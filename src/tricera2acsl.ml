
(*
 * Copyright 2021, 2025 Scania CV AB
 * Copyright 2021 KTH
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 *
 *  SPDX-License-Identifier: GPL-2.0+
 *)
let try_read ic =
    try Some (input_line ic) with End_of_file -> None

let read_lines fname =
  try
    let ic = open_in fname in
    let rec read acc =
      match try_read ic with
      | Some line -> read (line :: acc)
      | None -> List.rev acc
    in
    Ok (Fun.protect ~finally:(fun () -> close_in ic) (fun () -> read []))
  with Sys_error msg ->
    Error (Format.sprintf "could not read %s: %s" fname msg)

let has_status_prefix status line =
  let status_length = String.length status in
  let line_length = String.length line in
  line_length >= status_length
  && String.sub line 0 status_length = status
  && (line_length = status_length
      || match line.[status_length] with
         | ' ' | '\t' | '(' | ':' -> true
         | _ -> false)

let validate_tricera_result result_fname =
  match read_lines result_fname with
  | Error msg -> Error msg
  | Ok lines ->
    let verdicts = List.map String.trim lines in
    let failure =
      List.find_opt
        (fun line ->
          has_status_prefix "UNSAFE" line
          || has_status_prefix "UNKNOWN" line
          || has_status_prefix "TIMEOUT" line)
        verdicts
    in
    (match failure with
     | Some verdict -> Error (Format.sprintf "TriCera reported %s" verdict)
     | None when List.exists (String.equal "SAFE") verdicts -> Ok ()
     | None -> Error "TriCera did not report an explicit SAFE verdict")

let wp_summary_regex =
  Str.regexp
    ".*Proved goals:[ \t]*\\([0-9]+\\)[ \t]*/[ \t]*\\([0-9]+\\)"

let parse_wp_summary_line line =
  if Str.string_match wp_summary_regex line 0 then
    try
      Some
        (int_of_string (Str.matched_group 1 line),
         int_of_string (Str.matched_group 2 line))
    with Failure _ -> None
  else
    None

let validate_wp_result result_fname =
  match read_lines result_fname with
  | Error msg -> Error msg
  | Ok lines ->
    let summary =
      List.fold_left
        (fun latest line ->
          match parse_wp_summary_line line with
          | Some _ as parsed -> parsed
          | None -> latest)
        None lines
    in
    (match summary with
     | None ->
       Error
         (Format.sprintf
            "WP did not produce a proved-goals summary; output: %s"
            result_fname)
     | Some (_, 0) ->
       Error
         (Format.sprintf
            "WP generated no proof goals (0 total); output: %s"
            result_fname)
     | Some (proved, total) when proved <> total ->
       Error
         (Format.sprintf
            "WP proved %d of %d goals; output: %s"
            proved total result_fname)
     | Some summary -> Ok summary)

type quote_state = Unquoted | Single_quoted | Double_quoted

let split_command_line input =
  let length = String.length input in
  let current = Buffer.create length in
  let arguments = ref [] in
  let token_started = ref false in
  let add character =
    token_started := true;
    Buffer.add_char current character
  in
  let flush () =
    if !token_started then begin
      arguments := Buffer.contents current :: !arguments;
      Buffer.clear current;
      token_started := false
    end
  in
  let rec parse index state =
    if index = length then
      match state with
      | Unquoted ->
        flush ();
        Ok (List.rev !arguments)
      | Single_quoted ->
        Error "unterminated single quote in -saida-tricera-opts"
      | Double_quoted ->
        Error "unterminated double quote in -saida-tricera-opts"
    else
      let character = input.[index] in
      match state, character with
      | Unquoted, (' ' | '\t' | '\r' | '\n') ->
        flush ();
        parse (index + 1) Unquoted
      | Unquoted, '\'' ->
        token_started := true;
        parse (index + 1) Single_quoted
      | Unquoted, '"' ->
        token_started := true;
        parse (index + 1) Double_quoted
      | Single_quoted, '\'' -> parse (index + 1) Unquoted
      | Double_quoted, '"' -> parse (index + 1) Unquoted
      | (Unquoted | Double_quoted), '\\' ->
        if index + 1 = length then
          Error "trailing escape in -saida-tricera-opts"
        else begin
          add input.[index + 1];
          parse (index + 2) state
        end
      | _, _ ->
        add character;
        parse (index + 1) state
  in
  parse 0 Unquoted

let process_status_code = function
  | Unix.WEXITED code -> code
  | Unix.WSIGNALED signal
  | Unix.WSTOPPED signal -> 128 + signal

let rec wait_for_process process_id =
  try
    let _, status = Unix.waitpid [] process_id in
    process_status_code status
  with Unix.Unix_error (Unix.EINTR, _, _) ->
    wait_for_process process_id

type artifact = {
  path: string;
  mutable channel: out_channel option;
}

let artifact_path artifact = artifact.path

let artifact_channel artifact =
  match artifact.channel with
  | Some channel -> channel
  | None -> invalid_arg ("artifact is closed: " ^ artifact.path)

let close_artifact artifact =
  match artifact.channel with
  | None -> ()
  | Some channel ->
    artifact.channel <- None;
    close_out_noerr channel

let remove_artifact artifact =
  try Sys.remove artifact.path with
  | Sys_error _ -> ()

let cleanup_artifact ~keep artifact =
  close_artifact artifact;
  if not keep then remove_artifact artifact

let open_exclusive path =
  let descriptor =
    Unix.openfile path [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_EXCL] 0o600
  in
  { path; channel = Some (Unix.out_channel_of_descr descriptor) }

let create_artifact ~keep ~prefix ~original =
  let basename = Filename.basename original in
  if keep then begin
    let directory = Filename.dirname original in
    let preferred = Filename.concat directory (prefix ^ basename) in
    try open_exclusive preferred with
    | Unix.Unix_error (Unix.EEXIST, _, _) ->
      let path, channel =
        Filename.open_temp_file
          ~mode:[Open_wronly; Open_creat; Open_excl; Open_binary]
          ~perms:0o600 ~temp_dir:directory
          (prefix ^ basename ^ ".") ""
      in
      { path; channel = Some channel }
  end else begin
    let path, channel =
      Filename.open_temp_file
        ~mode:[Open_wronly; Open_creat; Open_excl; Open_binary]
        ~perms:0o600 ~temp_dir:(Filename.get_temp_dir_name ())
        prefix ("_" ^ basename)
    in
    { path; channel = Some channel }
  end

let with_artifact ~keep ~prefix ~original action =
  let artifact = create_artifact ~keep ~prefix ~original in
  Fun.protect
    ~finally:(fun () -> cleanup_artifact ~keep artifact)
    (fun () -> action artifact)

let run_process program arguments output_artifact =
  let output =
    output_artifact |> artifact_channel |> Unix.descr_of_out_channel
  in
  let argv = Array.of_list (program :: arguments) in
  let process_id =
    Unix.create_process program argv Unix.stdin output output
  in
  wait_for_process process_id

let run_tricera tri_path force_nondet_init entrypoint tri_opts harness_fname output_artifact =
  match split_command_line tri_opts with
  | Error message -> Error message
  | Ok option_arguments ->
    let forced_init =
      if force_nondet_init then ["-forceNondetInit"] else []
    in
    let arguments =
      ["-m:" ^ entrypoint]
      @ forced_init @ option_arguments @ [harness_fname]
    in
    try Ok (run_process tri_path arguments output_artifact) with
    | Unix.Unix_error (error, function_name, argument) ->
      Error
        (Format.sprintf
           "could not execute TriCera: %s (%s %s)"
           (Unix.error_message error) function_name argument)

(*Assume contract for function foo starts with line: is of form
/* contracts for foo */ or /* contract for foo */
*)
let contracts_regex = Str.regexp "/\\* contracts? for \\([a-zA-Z_][0-9a-zA-Z_]*\\) \\*/"
let acsl_start_regex = Str.regexp "/\\*@$?"
let acsl_end_regex = Str.regexp ".*\\*/$?"

(*Looks for function name in a comment on the form: 
  '/* contract for <functionn-name> */'
*)
let find_function_name s =
  try 
    let _ = Str.search_forward contracts_regex s 0 in
    Some(Str.matched_group 1 s)
  with
    Not_found -> None


(*Returns the contract as a list of lines*)
let rec read_a_contract ic =
  match (try_read ic) with
    | Some s ->
      let s' = String.trim s in
      if (Str.string_match acsl_end_regex s' 0) then [s]
      else s::(read_a_contract ic)
    | None -> [] (*Shouldnt happen*)

(*ht: (key, value): (string, [string]),
  where key is function name value is the contract as a list of lines*)
let rec contracts_to_hash ic ht =
  match (try_read ic) with
    | Some s ->
      let s = String.trim s in
      let _ = (match (find_function_name s) with
          | Some(fn_name) ->
            let clist = read_a_contract ic in
            Hashtbl.add ht fn_name clist
          | None -> ())
      in
        contracts_to_hash ic ht
      (*if (Str.string_match contracts_regex s' 0) then
      let _ = if Hashtbl.length ht = 0 then
        Hashtbl.add ht "Dummy_since_empty :(" []
      else ()
      in
 *)
    | None -> ()

let create_contracts_hash tricera_result_fname =
  let ht = Hashtbl.create 10 in
  let ic = open_in tricera_result_fname in
  contracts_to_hash ic ht;
  close_in ic;
  ht
