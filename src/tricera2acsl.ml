
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

open Options_saida

let harness_source_merged_fname = "tmp_harness_source_merged.c"
let tricera_output_name = "tmp_tricera_result.txt"
let inferred_source_merged_fname = "tmp_inferred_source_merged.c"

let try_read ic =
    try Some (input_line ic) with End_of_file -> None

(* let tricera_exec_file_path = "tricera/tri" *)

let run_tricera tri_path =
  let cmd_str =
    if NoTriPP.get () then
        tri_path ^ " -noPP "
    else
        tri_path ^ " "
    in
  let cmd_str = cmd_str ^ harness_source_merged_fname ^ " -log"
                ^ " > " ^ tricera_output_name
  in
  Sys.command cmd_str

let str_find_opt r s n =
  try Some(Str.search_forward r s n) with Not_found -> None

(*Assume contract for function foo starts with line: is of form
/* contracts for foo */
*)
let contracts_regex = Str.regexp "/\\* contracts for [0-9a-zA-Z_][0-9a-zA-Z_]* \\*/"
let acsl_start_regex = Str.regexp "/\\*@$?"
let acsl_end_regex = Str.regexp ".*\\*/$?"

(*Assume contract for function foo starts with line: is of form
/* contracts for foo */
*)
let contracts_start_to_name s =
  let s' = Str.replace_first (Str.regexp "/\\* contracts for") "" s in
  let s' = Str.replace_first (Str.regexp "\\*/") "" s' in
  String.trim s'


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
      let _ = (match (str_find_opt contracts_regex s 0) with
          | Some(_) ->
            let fn_name = contracts_start_to_name s in
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

let create_contracts_hash () =
  let ht = Hashtbl.create 10 in
  let ic = open_in tricera_output_name in
  let _ = contracts_to_hash ic ht in
  let _ = close_in ic in
  ht
