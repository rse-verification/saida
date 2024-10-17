(*
 * Copyright 2021 Scania CV AB
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
open Filepath (*Needed to read the line number*)
open Options_saida


(*This is a dirty fix for replacing ghost assigns, TODO: fix this properly later*)
let ghost_regex = Str.regexp ".*//@ ghost"

(*NOTE: All regexes expect strings trimmed from leading/trailing whitespace*)

let fn_regex = Str.regexp
      ("^\\(\\(void\\)\\|\\(int\\)\\|\\(float\\)\\|\\(double\\)\\|"
      ^ "\\(enum [a-zA-Z_][a-zA-Z0-9_]*\\)\\|\\(struct [a-zA-Z_][0-9a-zA-Z_]*\\)\\) (.*)$?")
let main_regex = Str.regexp ".*main.*(.*)$?"
let entry_regex () = Str.regexp ".*entry.*(.*)$?"

let get_fn_name s =
  (* Scanf.sscanf s "%s %s()%s" (fun _ x _ -> x) *)
  let m = Str.string_match (Str.regexp {|.* \(.+\)(.*).*|}) s 0 in
  if m = true then
    (
      Str.matched_group 1 s
      )
  else
    (
    Kernel.fatal "Dummy"
    )

(*Returns the fundef starting at line-nr n,
  returns none if line n is not the start of a fundef
*)
let line_to_fun_def n fn_list =
    List.find_opt
      (fun (name, (start_pos, end_pos)) -> n == start_pos.pos_lnum)
      fn_list

(*Checks if line nr n is start of a fun definition*)
let line_is_fun_def n fn_list =
  match line_to_fun_def n fn_list with
    | Some _ -> true
    | None -> false

(*in_comment describes if inside multi-line acsl specification or not*)
(*fn_list : [(name, loc)]contains a list of all function definitions and locations
    where name is string and loc is Cil_types.location
*)
let rec add_contract_annots ic buff in_acsl line fn_list =
  match (try_read ic) with
    | Some s ->
      let s' = String.trim s in
      let (to_add, in_acsl') =
        match in_acsl with
          | true -> if (Str.string_match acsl_end_regex s' 0) then ("\n", false) else ("", true)
          | false ->
              if (Str.string_match acsl_start_regex s' 0) then ("", true)
              else
              (match line_to_fun_def line fn_list with
                | Some _ ->
                  let name = get_fn_name s' in
                  (* if (Str.string_match main_regex s' 0) then *)
                  if name = "main" then
                    ((Str.replace_first (Str.regexp "main") "main2" s) ^ "\n", false)
                  else
                    (* if (Str.string_match (entry_regex ()) s' 0) |> not then *)
                    Self.debug ~level:3 "name:%s %s" name (Kernel.MainFunction.get ());
                    if not(name = Kernel.MainFunction.get ()) then
                      (
                      ("/*@contract@*/\n" ^ s ^ "\n", false)
                      )
                    else
                      (s,false))
                | None ->
                    if (Str.string_match ghost_regex s 0) then
                      ((Str.replace_first (Str.regexp "//@ ghost") "" s) ^ " //from ghost code\n", false)
                    else (s^"\n", false))
      in
      Buffer.add_string buff to_add;
      add_contract_annots ic buff in_acsl' (line+1) fn_list
    | None -> ()



(*Takes buffer for the harness function and the original file name and merges*)
(*File reading from Rosetta code ("read entire file")*)
let source_w_harness source_fname hbuff fn_list =
  let source_f = open_in source_fname in
    let n = in_channel_length source_f in
    let source_buff = Buffer.create n in
    let _ = add_contract_annots source_f source_buff false 1 fn_list in
    let _ = close_in source_f in
  let merge_file = open_out harness_source_merged_fname in
    let _ = Buffer.output_buffer merge_file source_buff in
    let _ = Buffer.output_buffer merge_file hbuff in
    close_out merge_file


let rec add_inferred_to_source ic buff ht line fn_list =
  match (try_read ic) with
    | Some s ->
      let _ =
        (match line_to_fun_def line fn_list with
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
        )
      in
        let _ = Buffer.add_string buff (s ^ "\n") in
        add_inferred_to_source ic buff ht (line+1) fn_list
    | None -> ()






let run_wp_plugin filename =
  Self.feedback "wp plugin started for file '%s'" filename;
  let libentry = if Kernel.LibEntry.get () then "-lib-entry" else "" in
  let _ = Sys.command ("frama-c -wp " ^ filename ^ " " ^ libentry) in ()



let merge_source_w_inferred source_file fn_list =
  let contracts_hash = create_contracts_hash () in
  let source_ic = open_in source_file in
  let n = in_channel_length source_ic in
  let buff = Buffer.create n in
  let () = add_inferred_to_source source_ic buff contracts_hash 1 fn_list in
  let () = close_in source_ic in
  let out_file = open_out inferred_source_merged_fname in
  let _ = Buffer.output_buffer out_file buff in
  close_out out_file


let run () =
  try
  if Enabled.get () then
    let harness_buff = Buffer.create 1000 in
    let fmt = Format.formatter_of_buffer harness_buff in
    (* let fmt = Format.formatter_of_out_channel chan in *)
    let a2t = new acsl2tricera fmt in
    let fn_list = a2t#translate in
    let _ = Format.pp_print_flush fmt () in
    let source_files = Kernel.Files.get () in
    if List.length source_files == 0 then
      Self.result "Error, no source file found";
    if List.length source_files > 1 then
      Self.feedback "More then 1 source file found, using only first";
    if List.length source_files >= 1 then
      begin
        let source_file = Filepath.Normalized.to_pretty_string (List.nth source_files 0) in
        source_w_harness source_file harness_buff fn_list;
        ignore (run_tricera (Tricera_path.get ()));
        merge_source_w_inferred source_file fn_list;
        if Run_wp.get () then
          let fname = inferred_source_merged_fname
          in run_wp_plugin fname;
      end
    (* Buffer.output_buffer chan harness_buff; *)
    (* Format.fprintf fmt "%!"; *)
  with Sys_error _ as exc ->
    let msg = Printexc.to_string exc in
      Printf.eprintf "There was an error: %s\n" msg

let () = Boot.Main.extend run
