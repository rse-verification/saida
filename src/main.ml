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

open Saida_vis
open Tricera2acsl
open Options_saida

(*This is a dirty fix for replacing ghost assigns, TODO: fix this properly later*)
let ghost_regex = Str.regexp ".*//@ ghost"

let get_fn_name s =
  match Str.string_match (Str.regexp {|.* \(.+\)(.*\($\|).*\)|}) s 0 with
  | true -> Str.matched_group 1 s
  | _ -> Kernel.fatal "Unable to infer function name from: %s" s

(*Returns the fundef starting at line-nr n,
  returns none if line n is not the start of a fundef
*)
let line_to_fun_def fn_list n =
    List.find_opt
      (fun (name, (start_pos, end_pos)) -> n == start_pos.Filepath.pos_lnum)
      fn_list

(*Checks if line nr n is start of a fun definition*)
let line_is_fun_def fn_list n =
  Option.is_some(line_to_fun_def fn_list n)


(* acslState describes if inside multi-line acsl specification or not*)
type acslState = 
| AcslOutside
| AcslInside

(*fn_list : [(name, loc)]contains a list of all function definitions and locations
    where name is string and loc is Cil_types.location
*)
let rec modify_acsl_annots ic oc acsl_state line fn_list =
  let next_acsl_state cur_state str =
    match cur_state with
    | AcslOutside when Str.string_match acsl_start_regex str 0 -> AcslInside
    | AcslInside when  Str.string_match acsl_end_regex str 0 -> AcslOutside
    | _ -> cur_state
  in
  match (try_read ic) with
  | None -> ()
  | Some src_line ->
      let s' = String.trim src_line in
      let acsl_state' = next_acsl_state acsl_state s' in
      let mod_src_line =
        match (acsl_state, acsl_state') with
        | (AcslInside, AcslOutside) -> "\n"
        | (AcslInside, AcslInside) -> ""
        | (AcslOutside, AcslInside) -> ""
        | (AcslOutside, AcslOutside) when line_is_fun_def fn_list line ->
            (match get_fn_name s' with
             | name when name = Kernel.MainFunction.get () -> src_line ^ "\n"
             | name -> "/*@contract@*/\n" ^ src_line ^ "\n")
        | (AcslOutside, AcslOutside) ->
            if (Str.string_match ghost_regex src_line 0) then
              (* Obvioulsy this will only work for single line comments. 
                 If e.g. ghost variable declarations are multi-line, this will fail. *)
              (Str.replace_first (Str.regexp "//@ ghost") "" src_line) ^ " //from ghost code\n"
            else src_line^"\n"
      in
      output_string oc mod_src_line;
      modify_acsl_annots ic oc acsl_state' (line+1) fn_list



(*Takes buffer for the harness function and the original file name and merges*)
(*File reading from Rosetta code ("read entire file")*)
let source_w_harness source_fname hbuff fn_list dest_fname =
  let source_chan = open_in source_fname in
  Fun.protect
    ~finally:(fun () -> close_in_noerr source_chan)
    (fun () ->
      let dest_chan = artifact_channel dest_fname in
      modify_acsl_annots source_chan dest_chan AcslOutside 1 fn_list;
      Buffer.output_buffer dest_chan hbuff;
      flush dest_chan)


let rec add_inferred_to_source ic buff ht line fn_list =
  match (try_read ic) with
    | Some s ->
      (match line_to_fun_def fn_list line with
        | Some(name, _) ->
          (match Hashtbl.find_opt ht name with
            | Some clist ->
              List.iter (fun r -> Buffer.add_string buff (r ^ "\n")) clist;
            | None ->
              if (name <> (Kernel.MainFunction.get ())) then
                Buffer.add_string buff ("//No inferred contract found for " ^ name ^ "\n")
              else ()
          )
        | None -> ()
      );
      Buffer.add_string buff (s ^ "\n");
      add_inferred_to_source ic buff ht (line+1) fn_list
    | None -> ()



let run_wp_plugin filename =
  Self.feedback "wp plugin started for file '%s'" filename;
  let entrypoint = Kernel.MainFunction.get () in
  let keep = KeepTempFiles.get () in
  with_artifact
    ~keep ~prefix:"saida_wp_" ~original:(filename ^ ".log")
    (fun log ->
      let arguments =
        ["-wp"; "-main"; entrypoint]
        @ (if Kernel.LibEntry.get () then ["-lib-entry"] else [])
        @ [filename]
      in
      let wp_exit = run_process "frama-c" arguments log in
      close_artifact log;
      let log_fname = artifact_path log in
      if wp_exit <> 0 then
        Self.abort
          "WP failed with exit status %d; output: %s"
          wp_exit log_fname;
      match validate_wp_result log_fname with
      | Error diagnostic -> Self.abort "%s" diagnostic
      | Ok (proved, total) ->
        Self.feedback "WP proved %d of %d goals" proved total)



let merge_source_w_inferred source_file fn_list result_fname out_fname =
  let contracts_hash = create_contracts_hash result_fname in
  let source_ic = open_in source_file in
  let n = in_channel_length source_ic in
  let buff = Buffer.create n in
  let () = add_inferred_to_source source_ic buff contracts_hash 1 fn_list in
  let () = close_in source_ic in
  let out_chan = open_out out_fname in
  let _ = Buffer.output_buffer out_chan buff in
  close_out out_chan


let run () =
  try
  if Enabled.get () then
    let source_fname =
      match Input_validation.select_single_source (Kernel.Files.get ()) with
      | Ok source -> Filepath.to_string source
      | Error diagnostic -> Self.abort "%s" diagnostic
    in

    let a2t = new acsl2tricera in
    let { fundec_locations = fn_list
        ; harness_functions = hf_list
        } = a2t#translate (Ast.get ()) in
    
    let harness_func = 
      List.find (fun i -> i.block.called_func == (Kernel.MainFunction.get_function_name ()))
      hf_list
    in
    let harness_buff = Buffer.create 1000 in
    let fmt = Format.formatter_of_buffer harness_buff in
    Format.pp_set_margin fmt max_int;
    let pt = new tricera_print fmt in
    pt#print_harness harness_func;
    let _ = Format.pp_print_flush fmt () in

    let output_fname = OutputFile.get () in
    let keep = KeepTempFiles.get () in
    with_artifact
      ~keep ~prefix:"saida_harness_" ~original:source_fname
      (fun harness ->
        source_w_harness source_fname harness_buff fn_list harness;
        close_artifact harness;
        with_artifact
          ~keep ~prefix:"saida_result_" ~original:source_fname
          (fun result ->
            let tricera_exit =
              match run_tricera
                    (TriceraPath.get ())
                    (Kernel.LibEntry.get ())
                    harness_func.name
                    (TriceraOptions.get ())
                    (artifact_path harness) result
              with
              | Ok exit_code -> exit_code
              | Error diagnostic ->
                Self.abort "TriCera invocation rejected: %s" diagnostic
            in
            close_artifact result;
            let result_fname = artifact_path result in
            if tricera_exit <> 0 then
              Self.abort
                "TriCera failed for harness %s with exit status %d; output: %s"
                harness_func.name tricera_exit result_fname;
            (match validate_tricera_result result_fname with
             | Ok () -> ()
             | Error diagnostic ->
               Self.abort
                 "%s while inferring contracts for harness %s"
                 diagnostic harness_func.name);
            merge_source_w_inferred
              source_fname fn_list result_fname output_fname;
            if Run_wp.get () then run_wp_plugin output_fname));
  with Sys_error _ as exc ->
    let msg = Printexc.to_string exc in
    Self.abort "I/O error: %s" msg

let () = Boot.Main.extend run
