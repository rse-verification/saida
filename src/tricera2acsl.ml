
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

let run_tricera tri_path tri_opts harness_fname output_fname =
  let cmd_str = Format.asprintf "%s %s %s > %s" 
    tri_path tri_opts harness_fname output_fname
  in
  Sys.command cmd_str

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
