module Validation = Saida__.Tricera2acsl
module Input_validation = Saida__.Input_validation

let fail label expected actual =
  failwith
    (Format.sprintf "%s: expected %s, got %s" label expected actual)

let contains text fragment =
  let text_length = String.length text in
  let fragment_length = String.length fragment in
  let rec search index =
    index + fragment_length <= text_length
    && (String.sub text index fragment_length = fragment
        || search (index + 1))
  in
  fragment_length = 0 || search 0

let with_temp_file contents test =
  let path = Filename.temp_file "saida_result_validation_" ".log" in
  let output = open_out path in
  output_string output contents;
  close_out output;
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () -> test path)

let expect_ok label = function
  | Ok value -> value
  | Error msg -> fail label "success" msg

let expect_error_containing label fragment = function
  | Error msg when contains msg fragment -> ()
  | Error msg -> fail label ("error containing " ^ fragment) msg
  | Ok _ -> fail label ("error containing " ^ fragment) "success"

let show_arguments arguments =
  "[" ^ String.concat "; " arguments ^ "]"

let expect_arguments label expected = function
  | Ok actual when actual = expected -> ()
  | Ok actual -> fail label (show_arguments expected) (show_arguments actual)
  | Error message -> fail label (show_arguments expected) message

let with_temp_directory test =
  let path = Filename.temp_file "saida argv safe;" ".tmp" in
  Sys.remove path;
  Unix.mkdir path 0o700;
  Fun.protect
    ~finally:(fun () ->
      Sys.readdir path
      |> Array.iter (fun name -> Sys.remove (Filename.concat path name));
      Unix.rmdir path)
    (fun () -> test path)

let path_exists path =
  try
    ignore (Unix.lstat path);
    true
  with Unix.Unix_error (Unix.ENOENT, _, _) -> false

let read_file path =
  let input = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr input)
    (fun () -> really_input_string input (in_channel_length input))

let test_tricera_verdicts () =
  with_temp_file
    "/* contract for helper */\nSAFE\n"
    (fun path ->
      Validation.validate_tricera_result path
      |> expect_ok "exact SAFE" |> ignore);
  List.iter
    (fun (label, verdict) ->
      with_temp_file
        ("SAFE\n" ^ verdict ^ "\n")
        (fun path ->
          Validation.validate_tricera_result path
          |> expect_error_containing label verdict))
    [ "UNSAFE", "UNSAFE";
      "UNKNOWN", "UNKNOWN";
      "UNKNOWN with spaced reason", "UNKNOWN (unsupported expression)";
      "UNKNOWN with reason suffix", "UNKNOWN(reason)";
      "TIMEOUT", "TIMEOUT" ];
  with_temp_file
    "SAFE (cached)\n"
    (fun path ->
      Validation.validate_tricera_result path
      |> expect_error_containing "SAFE must be exact" "explicit SAFE");
  with_temp_file
    "/* contracts but no verdict */\n"
    (fun path ->
      Validation.validate_tricera_result path
      |> expect_error_containing "missing verdict" "explicit SAFE");
  let missing = Filename.temp_file "saida_missing_result_" ".log" in
  Sys.remove missing;
  Validation.validate_tricera_result missing
  |> expect_error_containing "missing result file" "could not read"

let test_wp_summaries () =
  with_temp_file
    "[wp] Proved goals:   3 / 3\n"
    (fun path ->
      match Validation.validate_wp_result path |> expect_ok "complete WP" with
      | 3, 3 -> ()
      | proved, total ->
        fail "complete WP" "3 / 3"
          (Format.sprintf "%d / %d" proved total));
  with_temp_file
    "Proved goals: 1 / 2\n[wp] Proved goals: 2 / 2\n"
    (fun path ->
      match Validation.validate_wp_result path |> expect_ok "last WP summary" with
      | 2, 2 -> ()
      | proved, total ->
        fail "last WP summary" "2 / 2"
          (Format.sprintf "%d / %d" proved total));
  List.iter
    (fun (label, output, diagnostic) ->
      with_temp_file output (fun path ->
        Validation.validate_wp_result path
        |> expect_error_containing label diagnostic))
    [ "missing WP summary", "no summary\n", "proved-goals summary";
      "zero WP goals", "Proved goals: 0 / 0\n", "no proof goals";
      "incomplete WP proof", "Proved goals: 3 / 4\n", "proved 3 of 4" ]

let test_command_line_split () =
  Validation.split_command_line
    "-log --tag 'value with spaces' --empty=\"\" semi;literal"
  |> expect_arguments "quoted TriCera options"
       ["-log"; "--tag"; "value with spaces"; "--empty="; "semi;literal"];
  Validation.split_command_line "--tag 'unterminated"
  |> expect_error_containing "unterminated TriCera option" "unterminated"

let test_argv_safe_tricera_process () =
  with_temp_directory (fun directory ->
    let executable = Filename.concat directory "tri tool;$(never-run)" in
    let harness = Filename.concat directory "input file;$(never-run).c" in
    let victim = Filename.concat directory "victim.log" in
    let preferred_output =
      Filename.concat directory
        ("saida_result_" ^ Filename.basename harness)
    in
    let script = open_out executable in
    output_string script
      "#!/bin/sh\nfor argument in \"$@\"; do\n  printf 'ARG=%s\\n' \"$argument\"\ndone\nprintf 'SAFE\\n'\n";
    close_out script;
    Unix.chmod executable 0o700;
    let source = open_out harness in
    output_string source "int main(void) { return 0; }\n";
    close_out source;
    let victim_output = open_out victim in
    output_string victim_output "do not overwrite\n";
    close_out victim_output;
    Unix.symlink victim preferred_output;
    let output =
      Validation.create_artifact
        ~keep:true ~prefix:"saida_result_" ~original:harness
    in
    Fun.protect
      ~finally:(fun () -> Validation.cleanup_artifact ~keep:false output)
      (fun () ->
        let output_path = Validation.artifact_path output in
        if output_path = preferred_output then
          fail "symlink collision" "a collision-safe result path" output_path;
        let permissions = (Unix.stat output_path).Unix.st_perm land 0o777 in
        if permissions <> 0o600 then
          fail "result permissions" "0600" (Printf.sprintf "%04o" permissions);
        (match
           Validation.run_tricera executable true "entry"
             "-log --tag 'value with spaces' --literal='semi;$()'"
             harness output
         with
         | Ok 0 -> ()
         | Ok code ->
           fail "argv-safe TriCera process" "exit 0" (string_of_int code)
         | Error message ->
           fail "argv-safe TriCera process" "success" message);
        Validation.close_artifact output;
        if read_file victim <> "do not overwrite\n" then
          fail "symlink collision" "unchanged victim" "overwritten victim";
        match
          Validation.read_lines output_path |> expect_ok "TriCera argv output"
        with
        | [ main;
            nondeterministic;
            log;
            tag;
            tag_value;
            literal;
            source;
            safe ]
          when main = "ARG=-m:entry"
            && nondeterministic = "ARG=-forceNondetInit"
            && log = "ARG=-log"
            && tag = "ARG=--tag"
            && tag_value = "ARG=value with spaces"
            && literal = "ARG=--literal=semi;$()"
            && source = "ARG=" ^ harness
            && safe = "SAFE" -> ()
        | lines ->
          fail "TriCera argv output" "exact argument boundaries"
            (String.concat " | " lines)))

let test_artifact_cleanup () =
  with_temp_directory (fun directory ->
    let original = Filename.concat directory "input.c" in
    let verify_removed label path =
      if path_exists path then fail label "removed artifact" path
    in
    let successful_path = ref "" in
    Validation.with_artifact
      ~keep:false ~prefix:"saida_harness_" ~original
      (fun artifact ->
        successful_path := Validation.artifact_path artifact;
        output_string (Validation.artifact_channel artifact) "harness\n");
    verify_removed "successful artifact cleanup" !successful_path;
    let failing_path = ref "" in
    (try
       Validation.with_artifact
         ~keep:false ~prefix:"saida_result_" ~original
         (fun artifact ->
           failing_path := Validation.artifact_path artifact;
           output_string (Validation.artifact_channel artifact) "result\n";
           raise Exit)
     with Exit -> ());
    verify_removed "failed artifact cleanup" !failing_path)

let test_input_boundary () =
  Input_validation.select_single_source []
  |> expect_error_containing "no input" "SAIDA-E002";
  Input_validation.select_single_source ["a.c"; "b.c"]
  |> expect_error_containing "multiple inputs" "SAIDA-E003";
  match Input_validation.select_single_source ["only.c"] with
  | Ok "only.c" -> ()
  | Ok actual -> fail "single input" "only.c" actual
  | Error message -> fail "single input" "success" message

let () =
  test_tricera_verdicts ();
  test_wp_summaries ();
  test_command_line_split ();
  test_argv_safe_tricera_process ();
  test_artifact_cleanup ();
  test_input_boundary ()
