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


(*
  This file is the main visitor of Saida that converts a program to input (harness function)
  for tricera
*)


open Cil_types
open Cil_datatype

module IntSet = Set.Make(Int)

(* Printer extension to adjust output for TriCera *)
module HarnessPrinter (X : Printer.PrinterClass) = struct
  class printer : Printer.extensible_printer = 
    object (self)
      inherit X.printer as super

      (* Disallow TModel in offsets *)
      method! term_offset fmt (toff : term_offset) =
        match toff with
        | TModel (mi, _) -> Format.fprintf fmt "<TModel offset not supported: %s>" mi.mi_name
        | _ -> super#term_offset fmt toff

      (* Print 0 and 1 instead of \false and \true, since 0 and 1 is what is used by TriCera *)
      method! logic_constant fmt (lc : logic_constant) =
        match lc with
        | Boolean(false) -> Format.fprintf fmt "%d" 0 (* TriCera does not support "false" yet. *)
        | Boolean(true) -> Format.fprintf fmt "%d" 1 (* TriCera does not support "true" yet. *)
        | _ -> super#logic_constant fmt lc

      (* Print the C name of the variable if it exists, instead of the logic name *)
      method! logic_var fmt (lv : logic_var) =
        match lv.lv_origin with
        | Some(vi) -> Format.fprintf fmt "%s" vi.vorig_name
        | None -> super#logic_var fmt lv
    end
end

(* Printer extension to remove \old(...) wrapper since TriCera is using
   a different format. *)
module SuppressOldAndPre (X : Printer.PrinterClass) = struct
  class printer : Printer.extensible_printer = 
    object (self)
      inherit X.printer as super

      (* Suppress the \old(...) / \at(..., \old|\pre) term wrapper. *)
      method! term fmt (t : term) =
        match t.term_node with
        | Tat (inner, BuiltinLabel Old)
        | Tat (inner, BuiltinLabel Pre) ->
            (* Drop the wrapper and print the inner term only *)
            self#term fmt inner
        | _ ->
            super#term fmt t
    end
end

let is_old_or_pre_logic_label ll =
  match ll with
    | BuiltinLabel(Old) | BuiltinLabel(Pre) -> true
    | _ -> false

let logic_var_name lv =
  match lv.lv_origin with
    | Some(vi) -> vi.vname
    | None -> lv.lv_name

let to_c_type (lt : Cil_types.logic_type) : Cil_types.logic_type =
  match lt with
  | Cil_types.Linteger -> Cil_types.Ctype (Cil.int32_t ())
  | _ -> lt


type harness_func = {
  mutable name: string;
  mutable block: harness_block;
  mutable assumes: Cil_types.identified_predicate list;
  mutable asserts: Cil_types.identified_predicate list;
  mutable return_type: Cil_types.typ
  (* mutable ghost_vars_right_of_impl_in_post : logic_var list; *)
}

and harness_block = {
    mutable called_func: string;
    mutable log_vars: logic_var list;
}

let fst (a,b) = a
let snd (a,b) = b


(* let find_default_behavior behavs =
  let default_behav_list = List.filter
    (fun b -> b.b_name = "default!")
    behavs
  in
  assert( (List.length default_behav_list) = 1 ); *)


(*Set of recursive functions, partially copied from Frama-C source code*)
let rec bounded_vars_term term =
  match term.term_node with
  | TConst _   | TSizeOf _
  | TSizeOfStr _ | TAlignOf _
  | Tnull
  | Ttype _ -> Logic_var.Set.empty
  | TLval lv
  | TAddrOf lv
  | TStartOf lv -> bounded_vars_lval lv
  | TSizeOfE t
  | TAlignOfE t
  | TUnOp (_,t)
  | TCast (_,_,t)
  | Tat (t,_)
  | Toffset (_,t)
  | Tbase_addr (_,t)
  | Tblock_length (_,t)
  | Ttypeof t -> bounded_vars_term t
  | TBinOp (_,t1,t2) ->
    Logic_var.Set.union
      (bounded_vars_term t1)
      (bounded_vars_term t2)
  | TUpdate (t1,toff,t2) ->
    Logic_var.Set.union
      (Logic_var.Set.union
         (bounded_vars_term t1)
         (bounded_vars_term_offset toff))
      (bounded_vars_term t2)
  | Tif (t1,t2,t3) ->
    Logic_var.Set.union
      (bounded_vars_term t1)
      (Logic_var.Set.union
         (bounded_vars_term t2)
         (bounded_vars_term t3))
  | TDataCons(_,t) | Tapp (_,_,t) ->
    List.fold_left
      (fun acc t ->
         Logic_var.Set.union (bounded_vars_term t) acc)
      Logic_var.Set.empty t
  | Tlambda(prms,expr) ->
    Logic_var.Set.union
      (List.fold_left (Fun.flip Logic_var.Set.add) Logic_var.Set.empty prms)
      (bounded_vars_term expr)
  | Trange(i1,i2) ->
    let fv = match i1 with
      | None -> Logic_var.Set.empty
      | Some i -> bounded_vars_term i
    in
    (match i2 with
     | None -> fv
     | Some i ->
       Logic_var.Set.union fv (bounded_vars_term i))
  | Tempty_set -> Logic_var.Set.empty
  | Tunion l | Tinter l ->
    List.fold_left
      (fun acc t ->
         Logic_var.Set.union (bounded_vars_term t) acc)
      Logic_var.Set.empty
      l
  | Tcomprehension(t,q,p) ->
    let q_bv =
      List.fold_left
        (fun acc v -> Logic_var.Set.add v acc) Logic_var.Set.empty q
    in
    let t_bv = bounded_vars_term t in
    let q_t_bv = Logic_var.Set.union q_bv t_bv in
    (match p with
     | None -> q_t_bv
     | Some p ->
       Logic_var.Set.union q_t_bv (bounded_vars_predicate p))
  | Tlet(d,b) ->
    let d_bv =
      match d.l_body with
      | LBterm term -> bounded_vars_term term
      | LBpred p -> bounded_vars_predicate p
      | LBnone
      | LBreads _ | LBinductive _ ->
        Kernel.fatal ~current:true
          "definition of local variable %s is not a term or a predicate"
          d.l_var_info.lv_name
    in
    let b_bv = bounded_vars_term b
    in
    Logic_var.Set.union d_bv b_bv
  (* | TLogic_coerce(_,t) -> bounded_vars_term t *)


and bounded_vars_lval (h,o) =
    Logic_var.Set.union
      (bounded_vars_lhost h) (bounded_vars_term_offset o)

and bounded_vars_lhost h =
    match h with
      | TMem t -> bounded_vars_term t
      | _ -> Logic_var.Set.empty

and bounded_vars_term_offset offs =
    match offs with
      | TNoOffset -> Logic_var.Set.empty
      | TField (_,o) | TModel(_,o) -> bounded_vars_term_offset o
      | TIndex (t,o) ->
        Logic_var.Set.union
          (bounded_vars_term t)
          (bounded_vars_term_offset o)


and bounded_vars_predicate p = match p.pred_content with
  | Pfalse | Ptrue -> Logic_var.Set.empty
  | Papp (_,_,tl) ->
    List.fold_left
      (fun acc t ->
         Logic_var.Set.union (bounded_vars_term t) acc)
      Logic_var.Set.empty tl
  | Pallocable (_,t) | Pfreeable (_,t)
  | Pvalid (_,t) | Pvalid_read (_,t) | Pobject_pointer (_, t) | Pvalid_function t
  | Pinitialized (_,t) | Pdangling (_,t) ->
    bounded_vars_term t
  | Pseparated seps ->
    List.fold_left
      (fun bv tset ->
         Logic_var.Set.union
           (bounded_vars_term tset) bv)
      Logic_var.Set.empty
      seps
  | Pfresh (_,_,t1,t2)
  | Prel (_,t1,t2)
    ->
    Logic_var.Set.union
      (bounded_vars_term t1)
      (bounded_vars_term t2)
  | Pand (p1,p2)
  | Por (p1,p2)
  | Pxor (p1,p2)
  | Pimplies (p1,p2)
  | Piff (p1,p2) ->
    Logic_var.Set.union
      (bounded_vars_predicate p1)
      (bounded_vars_predicate p2)
  | Pnot p
  | Pat (p,_)
    -> bounded_vars_predicate p
  | Pif (t,p1,p2) ->
    Logic_var.Set.union
      (bounded_vars_term t)
      (Logic_var.Set.union
         (bounded_vars_predicate p1)
         (bounded_vars_predicate p2))
  | Plet (d, p) ->
    let fvd =
      match d.l_body with
      | LBterm t -> bounded_vars_term t
      | LBpred p -> bounded_vars_predicate p
      | LBnone
      | LBreads _ | LBinductive _ ->
        Kernel.fatal ~current:true
          "Local logic var %s is not a defined term or predicate"
          d.l_var_info.lv_name
    in
    Logic_var.Set.add
      d.l_var_info
      (Logic_var.Set.union fvd (bounded_vars_predicate p))

  | Pforall (lvs,p) | Pexists (lvs,p) ->
      List.fold_left
        (Fun.flip Logic_var.Set.add) (bounded_vars_predicate p) lvs


let logic_vars_from_pred pred =
  let free_vars = Cil.extract_free_logicvars_from_predicate pred in
  let bounded_vars = bounded_vars_predicate pred in
  Logic_var.Set.union free_vars bounded_vars

let logic_vars_from_id_pred_list id_pred_list =
  List.fold_left
    Logic_var.Set.union
    Logic_var.Set.empty
    (
      List.map
        (fun ip -> logic_vars_from_pred ip.ip_content.tp_statement)
        id_pred_list
    )

let make_harness_func f_svar behavs =
  (*TODO: Fix so that it can deal with different behaviors*)
  let assumes = List.concat (List.map (fun b -> b.b_requires) behavs) in
  (* let behavs_no_def = List.filter (fun b -> b.b_name = "default!") behavs in *)
  let asserts = List.concat (List.map (fun b -> List.map snd b.b_post_cond) behavs) in
  (*TODO: Extract vars only in \old-context instead*)
  let vars_in_post =
    List.fold_left
      Logic_var.Set.union
      Logic_var.Set.empty
      (
        List.map
          (fun ip -> logic_vars_from_pred ip.ip_content.tp_statement)
          asserts
      )
  in
  let vars_in_post_list = Logic_var.Set.elements vars_in_post in
  let log_vars_in_post =
    List.filter
      (fun lv ->
        match lv.lv_origin with
          | Some(_) -> false
          | None -> true
      )
      vars_in_post_list
  in
  let vars_in_pre =
    List.fold_left
      Logic_var.Set.union
      Logic_var.Set.empty
      (
        List.map
          (fun ip -> logic_vars_from_pred ip.ip_content.tp_statement)
          assumes
      )
  in
  let vars_in_pre_list = Logic_var.Set.elements vars_in_pre in
  let log_vars_in_pre =
    List.filter
      (fun lv ->
        match lv.lv_origin with
          | Some(_) -> false
          | None -> true
      )
      vars_in_pre_list
  in
  let all_log_vars = List.append log_vars_in_pre log_vars_in_post in
  let h_block = { called_func = f_svar.vname; log_vars = all_log_vars} in
  let f_ret_type = match f_svar.vtype.tnode with
    | TFun(r, _, _) -> r
    | _ -> f_svar.vtype (*shouldnt happen*)
  in
  {
    (* name = Printf.sprintf "%s_harness" f_name; *)
    name = "main";
    block = h_block;
    assumes = assumes;
    asserts = asserts;
    return_type = f_ret_type;
    (* ghost_vars_right_of_impl_in_post = []; *)
  }



(*Enum describing if something belongs to pre- or post-condition*)
type pre_or_post =
  | PRE
  | POST;;

(*relation is of rel type*)
let rel_to_string rel =
  match rel with
    | Rlt ->  "<"
    | Rgt ->  ">"
    | Rle ->  "<="
    | Rge ->  ">="
    | Req ->  "=="
    | Rneq -> "!="

(*Borrowed from Cil_printer.ml*)
let binop_to_string binop =
  match binop with
         | PlusA | PlusPI -> "+"
         | MinusA | MinusPP | MinusPI -> "-"
         | Mult -> "*"
         | Div -> "/"
         | Mod -> "%"
         | Shiftlt -> "<<"
         | Shiftrt -> ">>"
         | Lt -> "<"
         | Gt -> ">"
         | Le -> "<="
         | Ge -> ">="
         | Eq -> "=="
         | Ne -> "!="
         | BAnd -> "&"
         | BXor -> "^"
         | BOr -> "|"
         | LAnd -> "&&"
         | LOr -> "||"

let unop_to_string uop =
   match uop with
    | Neg -> "-"
    | BNot -> "~"
    | LNot -> "!"

let rec repeat_str str n =
  if n = 0 then ""
  else str ^ (repeat_str str (n-1))

let rec get_type_decl_string typ =
  match typ.tnode with
    | TInt(_) -> "int"
    | TComp(cinfo) -> Cil.compFullName cinfo
    | TPtr(inner_type) -> (get_type_decl_string inner_type) ^ " *"
    | TNamed(tinfo) -> tinfo.torig_name
    | _ -> "Only_int_or_ptr_or_struct_or_union_supported_in_var_decl"

let get_var_decl_string vi =
  let type_string = get_type_decl_string vi.vtype in
  Printf.sprintf "%s %s;" type_string vi.vname

(*special case where i first levels of derefs are not counted*)
let rec get_type_decl_string_2 typ i =
  match typ.tnode with
    | TInt(_) -> "int"
    | TComp(cinfo) -> Cil.compFullName cinfo
    | TPtr(inner_type) ->
      let s = if i > 0 then "" else " *" in
      (get_type_decl_string_2 inner_type (i-1)) ^ s
    | TNamed(tinfo) -> tinfo.torig_name
    | _ -> "Only_int_or_ptr_or_struct_or_union_supported_in_var_decl"

let get_var_decl_string_2 vi i =
  let type_string = get_type_decl_string_2 vi.vtype i in
  Printf.sprintf "%s %s;" type_string vi.vname

let get_logic_var_decl_string lv =
  let type_string =
    match lv.lv_type with
      | Ctype(inner_type) -> get_type_decl_string inner_type
      | Linteger -> "int"
      | _ -> "Unspported_type_of_logic_var"
  in
  Printf.sprintf "%s %s;" type_string lv.lv_name



(*Debugging function to check what type a Term is*)
let term_node_debug_print out tn =
    match tn with
        | TConst(lc) -> Format.fprintf out "-1";
        | TLval(tl) -> Format.fprintf out "0";
        | TSizeOf(_) -> Format.fprintf out "1"(** size of a given C type. *)
        | TSizeOfE (_) -> Format.fprintf out "2" (** size of the type of an expression. *)
        | TSizeOfStr (_) -> Format.fprintf out "3" (** size of a string constant. *)
        | TAlignOf (_) -> Format.fprintf out "4" (** alignment of a type. *)
        | TAlignOfE (_) -> Format.fprintf out "5" (** alignment of the type of an expression. *)
        | TUnOp (_, _) -> Format.fprintf out "6" (** unary operator. *)
        | TBinOp (_, _, _) -> Format.fprintf out "7" (** binary operators. *)
        | TCast (_,_, _) -> Format.fprintf out "8" (** cast to a C type. *)
        | TAddrOf (_) -> Format.fprintf out "9" (** address of a term. *)
        | TStartOf (_) -> Format.fprintf out "10" (** beginning of an array. *)

        (* additional constructs *)
        | Tapp (_, _, _) -> Format.fprintf out "11"
        (** application of a logic function. *)
        | Tlambda (_, _) -> Format.fprintf out "12" (** lambda abstraction. *)
        | TDataCons (_, _) -> Format.fprintf out "13"
        (** constructor of logic sum-type. *)
        | Tif (_, _, _) -> Format.fprintf out "14"
        (** conditional operator*)
        | Tat (_, _) -> Format.fprintf out "15"
        (** term refers to a particular program point. *)
        | Tbase_addr (_, _) -> Format.fprintf out "16" (** base address of a pointer. *)
        | Toffset (_, _) -> Format.fprintf out "17" (** offset from the base address of a pointer. *)
        | Tblock_length (_, _) -> Format.fprintf out "18" (** length of the block pointed to by the term. *)
        | Tnull -> Format.fprintf out "19"(** the null pointer. *)
        (* | TLogic_coerce (lt, term) -> Format.fprintf out "19"; *)
          (* logic_type_to_tla out lt *)
        (** implicit conversion from a C type to a logic type.
            The logic type must not be a Ctype. In particular, used to denote
            lifting to Linteger and Lreal.
        *)
        | TUpdate (_, _, _) -> Format.fprintf out "21"
        (** functional update of a field. *)
        | Ttypeof (_) -> Format.fprintf out "22" (** type tag for a term. *)
        | Ttype (_) -> Format.fprintf out "23" (** type tag for a C type. *)
        | Tempty_set -> Format.fprintf out "24" (** the empty set. *)
        | Tunion (_) -> Format.fprintf out "25" (** union of terms. *)
        | Tinter (_) -> Format.fprintf out "26" (** intersection of terms. *)
        | Tcomprehension (_, _, _) -> Format.fprintf out "27"
        | Trange (_, _) -> Format.fprintf out "28" (** range of integers. *)
        | Tlet (_,_) -> Format.fprintf out "29" (** local binding *)


let contains_ghost_var p =
   let lv_set = Cil.extract_free_logicvars_from_predicate p in
   let lv_list = Logic_var.Set.elements lv_set in
   let varinfos = List.filter_map (fun lv -> lv.lv_origin) lv_list in
   List.fold_left (fun b lv -> b || lv.vghost) false varinfos


let get_ensures_with_ghost_right_of_impl ensures =
  List.filter_map
    (
      fun ip ->
        let pn = ip.ip_content.tp_statement.pred_content in
        match pn with
          | Pimplies(_, p) ->
            if (contains_ghost_var p) then (Some ip) else None
          | _ -> None
    )
    ensures

module StringMap = Map.Make(String)

(*
  Class for pretty printing function contracts as harness function with
  assume and asserts in tricera style, inspired by Frama-C development guide:
    https://frama-c.com/download/frama-c-plugin-development-guide.pdf
*)
class acsl2tricera out = object (self)
  inherit Visitor.frama_c_inplace as super

  val mutable curr_func = None
  val mutable indent = 0
  val mutable global_c_vars = []
  val mutable global_ghost_vars = []

  val mutable fn_list = [];

  val mutable deref_lvl = 0;

  val mutable let_var_defs = Logic_var.Hashtbl.create 10

  method incr_deref_lvl = deref_lvl <- deref_lvl + 1;
  method decr_deref_lvl = deref_lvl <- if deref_lvl <= 0 then 0 else deref_lvl - 1;

  method get_deref_lvl = deref_lvl

  method incr_indent = indent <- indent + 1;
  method dec_indent = indent <- if indent <= 0 then 0 else indent - 1;

  (*This is the main function intended to be called upon creation*)
  method translate =
    let _ = Visitor.visitFramacFileSameGlobals
              ((self) :> Visitor.frama_c_inplace)
              (Ast.get ())
    in fn_list


  method get_curr_func_name =
    match curr_func with
      | Some f -> f.svar.vname
      | None -> "FUNC_MISSING"

  method get_curr_func_svar =
    match curr_func with
      | Some f -> f.svar
      | None -> Cil.makeGlobalVar "FUNC_MISSING" Cil_const.voidType

  method result_string = self#get_curr_func_name ^ "_result";

  method print_indent =
  for _ = 1 to indent do
    self#print_string "  "
  done;

  method print_string s = Format.fprintf out "%s%!" s
  method print_line s =
    self#print_indent;
    Format.fprintf out "%s%!\n" s;

  method print_newline = Format.fprintf out "\n"

  method print_using : 'a. (Format.formatter -> 'a -> unit) -> 'a -> unit =
    fun pretty_printer value -> pretty_printer out value;

  method print_wrapped_in_old (t : logic_type ) (f : unit -> unit) =
    let old_printer = Printer.current_printer () in
    Printer.update_printer (module SuppressOldAndPre : Printer.PrinterExtension);
    self#print_string 
      (Format.asprintf "$at(\"Old\", (%a)(" 
        Printer.pp_typ (Logic_utils.logicCType (to_c_type t)));
    f ();
    self#print_string "))";
    Printer.set_printer old_printer;


  method add_let_var_def b =
    Logic_var.Hashtbl.add let_var_defs b.l_var_info b.l_body;

  method! vfile f =
    let global_vars =
      List.filter_map
        (
          fun g ->
            match g with
              | GVar(vi, _, _) -> Some vi
              | _ -> None
        )
        f.globals
    in
    (*Set global vars*)
    global_c_vars <- List.filter (fun vi -> not vi.vghost) global_vars;
    global_ghost_vars <- List.filter (fun vi -> vi.vghost) global_vars;
    fn_list <- List.filter_map
        (fun g ->
          match g with
            | GFun(f, loc) -> Some((f.svar.vorig_name, loc))
            | _ -> None
        )
      f.globals;
    Cil.DoChildren

  method! vglob_aux g =
    match g with
      | GFun(f, _) ->
        curr_func <- Some f;
        Cil.DoChildren
      | _ -> Cil.SkipChildren


  method! vfunc f =
    Cil.SkipChildren

  (*Spec visited from here*)
  method! vspec s =
    let _ = if (List.length s.spec_behavior) > 0 then
      begin
        (* FIX ME: Currently prints a "main" function for each function 
             in the source that has ACSL annotation. *)
        let har_func = make_harness_func self#get_curr_func_svar s.spec_behavior in
        self#do_fun_spec har_func;
      end
    in
    Cil.SkipChildren

  method print_harness_fn_name hf =
    self#print_line (Printf.sprintf "void %s()" hf.name);

  (* Currently not used, global ghost variables are introduced in main.ml *)
  method print_global_ghost_vars_decl =
    if (List.length global_ghost_vars) > 0 then
      self#print_line "//Declaring all global ghost vars";
      (*Assumes that ghost vars have unique names (which they should have)*)
    List.iter
      (fun vi ->
        self#print_string (get_var_decl_string vi);
        self#print_newline;
      )
      global_ghost_vars;

  method print_require_assumes hf =
    if (List.length hf.assumes) > 0 then
      self#print_line "//The requires-clauses translated into assumes";
    List.iter
      (
        fun ip ->
          self#print_indent;
          self#print_string "assume(";
          let _ = Cil.visitCilIdPredicate (self :> Cil.cilVisitor) ip in
          self#print_string ");\n";
      )
      hf.assumes;

  method print_special_ghost_ensure_assumes hf =
    let ghost_special_list = get_ensures_with_ghost_right_of_impl hf.asserts in
    if (List.length ghost_special_list) > 0 then
      self#print_line "//Special assumes of ghost-variables 'assigned to' in requires clause";
    List.iter
      (fun ip ->
        self#print_indent;
        self#print_string "assume(";
        let _ = Cil.visitCilIdPredicate (self :> Cil.cilVisitor) ip in
        self#print_string ");\n";
      )
      ghost_special_list;

  method print_ensure_asserts hf =
    if (List.length hf.asserts) > 0 then
      self#print_line "//The ensures-clauses translated into asserts";
    List.iter
      (
        fun ip ->
          self#print_indent;
          self#print_string "assert(";
          let _ = Cil.visitCilIdPredicate (self :> Cil.cilVisitor) ip in
          self#print_string ");\n";
      )
      hf.asserts;

  method print_log_var_decls hf =
    let log_vars = hf.block.log_vars in
    if (List.length log_vars > 0) then
      self#print_line "//printing logic var declarations, e.g. from \\forall or \\exists";
    List.iter
      (fun lv -> self#print_line (get_logic_var_decl_string lv))
      log_vars

  method print_params_init =
    match curr_func with
      | Some(curr_func) when (List.length curr_func.sformals) > 0 ->
        self#print_line "//Declare the paramters of the function to be called";
        List.iter (fun vi -> self#print_line (get_var_decl_string vi)) curr_func.sformals;
      | _ -> ();

  method do_fun_spec hf =
    let old_printer = Printer.current_printer () in
    Printer.update_printer (module HarnessPrinter : Printer.PrinterExtension);

    self#print_harness_fn_name hf;
    self#print_string "{\n";
    self#incr_indent;

    (*Print the initialization of parameters (if any)*)
    (* FIX ME: Having parameters currently breaks the harness.
        The problem is that the "old" state does not exist for
        these. We need a two level harness for this. In the outer
        level we initialize the parameters for the function and
        send them as arguments to the inner harness function.
        the inner harness will contain all assumes and asserts. *)
    self#print_params_init;
    self#print_newline;

    (*Print the declaration of ghost-variables*)
    (*Since they are global, they have to be declared in global namespace,
      handled later in main.ml, revoked this but keeping as a comment for potential future use*)
    (* self#print_global_ghost_vars_decl;
    self#print_newline; *)

    (*Print logical variable declarations, e.g. from \forall, \exists or \let*)
    self#print_log_var_decls hf;
    self#print_newline;

    (*Print the assumes (from pre-cond)*)
    self#print_require_assumes hf;
    self#print_newline;

    (*Print assumes for special ghost-var ensures*)
    (*experimental feature*)
    (* self#print_special_ghost_ensure_assumes hf;
    self#print_newline; *)

    (*Print the function call to the function we are harness for*)
    self#print_line "//Function call that the harness function verifies";
    let _ =
      match curr_func with
        | Some(curr_func) ->
          let params =
            String.concat ", " (List.map (fun vi -> vi.vname) curr_func.sformals)
          in
          (* self#print_string (Printf.sprintf "%s(%s);\n" hf.block.called_func params); *)
          (*Quick fix main2 for working in tricera*)
          let s = match hf.return_type.tnode with
            | TVoid -> ""
            | _ -> (get_type_decl_string hf.return_type) ^ " " ^ self#result_string ^ " = "
          in
          let fname = curr_func.svar.vname in
          if fname = "main" then
            self#print_line (s ^ "main2("^ params ^");\n")
          else
            self#print_line (s ^ fname ^ "("^ params ^");\n");
        | None -> ();
    in
    (*Print the asserts, from the post-cond*)
    self#print_ensure_asserts hf;

    self#dec_indent;
    self#print_string "}\n";

    Printer.set_printer old_printer;


  method! vbehavior b =
    (* let pre_name = self#do_pre_cond b.b_requires in
    let post_name = self#do_post_cond b.b_post_cond in *)
    Cil.SkipChildren

  method pred_bin_op p1 p2 op_string =
    self#print_string "(";
    ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p1);
    self#print_string (Printf.sprintf " %s " op_string);
    ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p2);
    self#print_string ")";

  method! vpredicate_node pn =
    match pn with
      | Ptrue -> self#print_string "1";
        Cil.SkipChildren
      | Pfalse -> self#print_string "0";
        Cil.SkipChildren
      | Pand(p1, p2) ->  self#pred_bin_op p1 p2 "&&";
        Cil.SkipChildren
      | Por(p1, p2) ->  self#pred_bin_op p1 p2 "||";
        Cil.SkipChildren
      | Pxor(p1, p2)  ->
        (*
          NOTE, for non-booleans, frama-c automatically compares with 0,
          e.g., 2 ^^ 2  becomes (2!=0 ^^ 2!=0) in frama-c normalization
        *)
        let _ = self#pred_bin_op p1 p2 "!=" in
        Cil.SkipChildren
      | Pimplies(p1, p2) ->
        (
          self#print_string "!";
          self#print_string "(";
          ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p1);
          self#print_string " && !";
          ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p2);
          self#print_string ")";
          Cil.SkipChildren
        )
      | Piff(p1, p2) ->
        self#pred_bin_op p1 p2 "==";
        Cil.SkipChildren
      | Pnot(p) ->
        self#print_string "!";
        Cil.DoChildren
      | Prel(rel, t1, t2) ->
        (
          self#print_string "(";
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t1);
          self#print_string (Printf.sprintf " %s " (rel_to_string rel));
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t2);
          self#print_string ")";
          Cil.SkipChildren
        )
      | Pat(p, ll) ->
          let _ = if is_old_or_pre_logic_label ll then
            begin
              self#print_wrapped_in_old (Cil_types.Ctype { tnode = Cil_types.TInt IChar; tattr = [] })
                (fun () -> ignore (Cil.visitCilPredicate (self :> Cil.cilVisitor) p))
            end
          else
            self#print_string "unsupported predicate label";
          in
          Cil.SkipChildren
      | Pforall(q, p) ->
        ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p);
        Cil.SkipChildren
      | Pexists(q, p) ->
        (*Currently approximate with (p || !p)*)
        let notp = Logic_const.pnot p in
        let p_or_notp = Logic_const.por (p, notp) in
        ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p_or_notp);
        Cil.SkipChildren
      | Plet(b, p) ->
        self#add_let_var_def b;
        ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p);
        Cil.SkipChildren
      | Pvalid(ll, t) ->
        Printer.pp_predicate_node out pn;
        Cil.SkipChildren
      | Pif(t, p1, p2) ->
        self#print_string "(";
        ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t);
        self#print_string " ? ";
        ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p1);
        self#print_string " : ";
        ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p2);
        self#print_string ")";
        Cil.SkipChildren
      | _ ->
        self#print_string "unsupported predicate received >>>";
        self#print_using Printer.pp_predicate_node pn;
        self#print_string "<<<";
        Cil.SkipChildren

  method! vterm_node tn =
    let _ =
      match tn with
        | TConst(lc) ->
          self#print_using Printer.pp_logic_constant lc;
        | TLval(tl) ->
          ignore (Cil.visitCilTermLval (self :> Cil.cilVisitor) tl);
        | TBinOp(bop, t1, t2) ->
          self#print_string "(";
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t1);
          self#print_string (Printf.sprintf " %s " (binop_to_string bop));
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t2);
          self#print_string ")";
        | TUnOp(uop, t) ->
          self#print_string "(";
          self#print_string (unop_to_string uop);
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t);
          self#print_string ")";
        | TDataCons(lci, terms) ->
          self#print_string "logic_sum_types_not_supported"
          (* Format.fprintf out "%a" Printer.pp_logic_ctor_info lci; *)
        (* | TLogic_coerce (_, t) ->
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t); *)
        | Tat(t, ll) ->
          if is_old_or_pre_logic_label ll then
            begin
              self#print_wrapped_in_old
                t.term_type
                (fun () -> ignore (Cil.visitCilTerm (self :> Cil.cilVisitor) t));
            end
          else
            begin
              self#print_string "Currently only old/pre logic labels supported" ;
            end
        | Tif(c, t1, t2) ->
          self#print_string "(";
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) c);
          self#print_string " ? ";
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t1);
          self#print_string " : ";
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t2);
          self#print_string ")";
        | TCast(_, _, t) ->
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t);
        | Tlet(b, t) ->
          self#add_let_var_def b;
          ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t);
        | _ ->
          self#print_string "Unsupported term received";
          term_node_debug_print out tn;
    in
    Cil.SkipChildren


(*
Cases:
  ptr to struct: to =
*)

  method! vterm_lval (tlh, toff) =
    match tlh with
      | TResult(typ) ->
        let tlh'  = TVar(Cil_const.make_logic_var_kind self#result_string LVC (Ctype typ)) in
        self#print_using Printer.pp_term_lval (tlh', toff);
        Cil.SkipChildren
      | TMem({term_node = Tat(t,ll); _}) when is_old_or_pre_logic_label ll ->
        self#print_wrapped_in_old
                (Cil.typeOfTermLval  (tlh, toff))
                (fun () -> self#print_using Printer.pp_term_lval (tlh, toff));
        Cil.SkipChildren
      | TMem(t) ->
        self#print_using Printer.pp_term_lval (tlh, toff);
        Cil.SkipChildren
      | TVar(lv) ->
          (* first, check if it is a let-variable *)
          match Logic_var.Hashtbl.find_opt let_var_defs lv with
            | Some(l_body) ->
              let _ = match l_body with
                | LBterm(t) ->
                  ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t);
                | LBpred(p) ->
                  ignore ( Cil.visitCilPredicate (self :> Cil.cilVisitor) p);
                | _ -> ()  (*Shouldnt happen*)
              in
              Cil.SkipChildren
            | None ->
              self#print_using Printer.pp_term_lval (tlh, toff);
              Cil.SkipChildren

  method! vquantifiers q =
    Cil.SkipChildren
end
