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

let to_c_type (lt : Cil_types.logic_type) : Cil_types.logic_type =
  match lt with
  | Cil_types.Linteger -> Cil_types.Ctype (Cil.int32_t ())
  | _ -> lt

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


(* Printer extension to print pre/post conditions etc. in TriCera format. *)
module HarnessPrinter = struct
  open Printer

  (* 
     Enable Kernel.PrintAsIs for a single function call. 

     Among other things this will make sure expressions
     like (0 < x) && (x < 10) are printed like that,
     and not like 0 < x < 10 which is not valid in
     TriCera.
  *)
  let with_print_cil_as_is f arg =
    let module PrintAsIs = Kernel.PrintAsIs in
    let old, default = PrintAsIs.get (), not (PrintAsIs.is_set ()) in
    PrintAsIs.on ();
    let r = f arg in
    if default then PrintAsIs.clear () else PrintAsIs.set old;
    r

  module type FunctionNameProvider = sig
    val name : string
  end

  (* 
     Creates a HarnessPrinter for a specific function.
     We need to inject the function name because we sometimes
     need to give the result value of the function we are
     creating a harness for a name based on the function name.
  *)
  module Make(Name: FunctionNameProvider) : PrinterExtension
    = functor (X: PrinterClass) -> struct
    class printer : Printer.extensible_printer = 
      object (self)
        inherit X.printer as super

        val context_func_name = Name.name
        (*
          FIX ME: \let variables should be local to each clause.
            Currently they are kept for the whole function specification.
         *)
        val mutable let_var_defs = Logic_var.Hashtbl.create 10
  
        method private add_let_var_def b =
          (Options_saida.Self.debug ~level:3 "adding let var: %s" b.l_var_info.lv_name);
          Logic_var.Hashtbl.add let_var_defs b.l_var_info b.l_body;
  
        (* Note: Must match whatever acsl2tricera is using *)
        method private result_string (fname : string) =
          fname ^ "_result";
  
        method private wrap_in_label : 'a. 
          Format.formatter -> logic_label -> logic_type -> (Format.formatter -> 'a -> unit) -> 'a -> unit = 
            fun fmt ll t f arg ->
              Format.fprintf fmt "$at(\"%a\", (%a)(%a))"
                  super#logic_label ll
                  (self#typ None) (Logic_utils.logicCType (to_c_type t))
                  f arg;

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
  
        (* Supress quantifiers *)
        method! quantifiers fmt (qfs : logic_var list) =
          ()
    
        method! term_lval fmt (tlh, toff) =
          match tlh with
          | TResult(typ) ->
              let tlh' = TVar(Cil_const.make_logic_var_kind (self#result_string context_func_name) LVC (Ctype typ)) in
              super#term_lval fmt (tlh', toff);
          | TMem(t) ->
            super#term_lval fmt (tlh, toff);
          | TVar(lv) ->
              (* first, check if it is a let-variable *)
              (Options_saida.Self.debug ~level:3 "printer looking up let var: %s" lv.lv_name);
              match Logic_var.Hashtbl.find_opt let_var_defs lv with
              | Some(l_body) ->
                 (match l_body with
                 (* TODO: Currently expands body inplace. This is NOT the proper thing to do
                      when e.g. \old(...) is involved. See e.g. let.c for an example where
                      expansion leads to using an old value when a post value should be used.
                      See Example 2.31 in https://www.frama-c.com/download/acsl-1.22.pdf
                      for an other illustration of the problem. 
                 *)
                  | LBterm(t) -> self#term  fmt t;
                  | LBpred(p) -> self#predicate fmt p;
                  | _ -> ()  (*Shouldnt happen*))
              | None ->
                  super#term_lval fmt (tlh, toff);
  
        method! term_node fmt t =
          match t.term_node with
          | TConst _
          | TLval _
          | TBinOp _
          | TUnOp _
          | Tif _ 
          | TCast _ ->
            super#term_node fmt t
          | TDataCons(lci, terms) ->
            (* Format.fprintf out "%a" Printer.pp_logic_ctor_info lci; *)
            Format.fprintf fmt "logic_sum_types_not_supported"
       (* | TLogic_coerce (_, t) ->
            ignore ( Cil.visitCilTerm (self :> Cil.cilVisitor) t); *)
          | Tat(inner, ll) ->
              self#wrap_in_label fmt ll (inner.term_type) self#term inner;
          | Tlet(def, body) ->
            self#add_let_var_def def;
            self#term fmt body;
          | _ ->
            Format.fprintf fmt "Unsupported term received";
            term_node_debug_print fmt t.term_node;
  
        method private pred_bin_op fmt p1 p2 op_string =
          Format.fprintf fmt "%a %s %a" self#predicate p1 op_string self#predicate p2;
      
        method! predicate_node fmt pn =
          match pn with
            | Ptrue ->
              super#predicate_node fmt (Prel(Rneq, (Cil.lone ()), (Cil.lzero ())));
            | Pfalse ->
              super#predicate_node fmt (Prel(Rneq, (Cil.lzero ()), (Cil.lzero ())));
            | Pnot(_)
            | Pand(_)
            | Por(_)
            | Prel(_)
            | Pif(_) ->
              super#predicate_node fmt pn;
            | Pxor(p1, p2)  ->
              (*
                NOTE, for non-booleans, frama-c automatically compares with 0,
                e.g., 2 ^^ 2  becomes (2!=0 ^^ 2!=0) in frama-c normalization
              *)
              self#pred_bin_op fmt p1 p2 "!=";
            | Pimplies(p1, p2) ->
              (
                let notp1 = Logic_const.pnot p1 in
                let notp1_or_p2 =  Por(notp1, p2) in
                super#predicate_node fmt notp1_or_p2;
              )
            | Piff(p1, p2) ->
              self#pred_bin_op fmt p1 p2 "==";
            | Pat(inner, ll) ->
              let ltyp = Cil_types.Ctype Cil_const.intType in
              self#wrap_in_label fmt ll (ltyp) self#predicate inner;
            | Pforall(q, p) ->
              super#predicate fmt p;
            | Pexists(q, p) ->
              (* 
                 FIX ME: Currently approximate with (p || !p) which is plain wrong!
                   Instead, use Bool expansion (Shannon decomposition)
                   \exist q : p(q) <==> p[T/q] \/ p[F/q]
              *)
              let notp = Logic_const.pnot p in
              let p_or_notp = Por(p, notp) in
              self#predicate_node fmt p_or_notp;
            | Plet(b, p) ->
              self#add_let_var_def b;
              self#predicate fmt p;
            | Pvalid(ll, t) ->
              (* FIX ME: The corresponding option to tricera is -valid-deref and
                  works on the complete program level. Hence, to translate this
                  we should remove the \valid predicate and add the -valid-deref
                  option to tricera.
              *)
              super#predicate_node fmt pn;
            | _ ->
              Format.fprintf fmt "unsupported predicate received >>> %a <<<"
                super#predicate_node pn;
      end
  end
end



type harness_block = {
    mutable called_func: string;
    mutable log_vars: logic_var list;
}

type harness_func = {
  mutable name: string;
  mutable block: harness_block;
  mutable assumes: Cil_types.identified_predicate list;
  mutable asserts: Cil_types.identified_predicate list;
  mutable params: Cil_types.varinfo list;
  mutable return_type: Cil_types.typ
  (* mutable ghost_vars_right_of_impl_in_post : logic_var list; *)
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
  id_pred_list
  |> List.map
      (fun ip -> logic_vars_from_pred ip.ip_content.tp_statement)
  |> List.fold_left
      Logic_var.Set.union
      Logic_var.Set.empty


let make_harness_func fdec behavs =
  let get_logic_vars (predicates: identified_predicate list): logic_var list = 
    predicates
    |> List.map (fun ip -> logic_vars_from_pred ip.ip_content.tp_statement)
    |> List.fold_left Logic_var.Set.union Logic_var.Set.empty
    |> Logic_var.Set.elements
    |> List.filter
        (fun lv ->
          match lv.lv_origin with
          | Some(_) -> false
          | None -> true
        )
  in
  (*TODO: Fix so that it can deal with different behaviors*)
  let assumes = List.concat (List.map (fun b -> b.b_requires) behavs) in
  (* let behavs_no_def = List.filter (fun b -> b.b_name = "default!") behavs in *)
  let asserts = List.concat (List.map (fun b -> List.map snd b.b_post_cond) behavs) in
  (*TODO: Extract vars only in \old-context instead*)
  let log_vars_in_post = get_logic_vars asserts in
  let log_vars_in_pre = get_logic_vars assumes in
  let all_log_vars = List.append log_vars_in_pre log_vars_in_post in
  let h_block = { called_func = fdec.svar.vname; log_vars = all_log_vars} in
  let f_ret_type = match fdec.svar.vtype.tnode with
    | TFun(r, _, _) -> r
    | _ -> fdec.svar.vtype (*shouldnt happen*)
  in
  { name = "main" (* FIX ME: Should use a proper harness function name *)
    (* name = Printf.sprintf "%s_harness" f_name; *)
  ; block = h_block
  ; assumes = assumes
  ; asserts = asserts
  ; params = fdec.sformals
  ; return_type = f_ret_type;
    (* ghost_vars_right_of_impl_in_post = []; *)
  }


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


let get_logic_var_decl_string lv =
  let type_string =
    match lv.lv_type with
      | Ctype(inner_type) -> get_type_decl_string inner_type
      | Linteger -> "int"
      | _ -> "Unspported_type_of_logic_var"
  in
  Printf.sprintf "%s %s;" type_string lv.lv_name


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


type src_data = {
  fundec_locations: (string * location) list;
  harness_functions: harness_func list;
}
(*
  Class for pretty printing function contracts as harness function with
  assume and asserts in tricera style, inspired by Frama-C development guide:
    https://frama-c.com/download/frama-c-plugin-development-guide.pdf
*)
class acsl2tricera = object (self)
  inherit Visitor.frama_c_inplace as super

  val mutable curr_func = None
  val mutable indent = 0

  val mutable fn_list = [];
  val mutable hf_list = [];

  (*This is the main function intended to be called upon creation*)
  method translate file =
    let _ = Visitor.visitFramacFileSameGlobals
              ((self) :> Visitor.frama_c_inplace)
              (file)
    in 
    { fundec_locations = fn_list
    ; harness_functions = hf_list
    }

  method! vfile f =
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
    if (List.length s.spec_behavior) > 0 then 
      hf_list <- (make_harness_func (Option.get(curr_func)) s.spec_behavior)::hf_list;
    Cil.SkipChildren
end


class tricera_print out = object (self)
  val mutable indent = 0

  val mutable let_var_defs = Logic_var.Hashtbl.create 10

  method private incr_indent = indent <- indent + 1;
  method private dec_indent = indent <- if indent <= 0 then 0 else indent - 1;

  method private result_string fname = fname ^ "_result";

  method private print_indent =
  for _ = 1 to indent do
    self#print_string "  "
  done;

  method private print_string s = Format.fprintf out "%s%!" s

  method private print_line s =
    self#print_indent;
    Format.fprintf out "%s%!\n" s;

  method private print_newline = Format.fprintf out "\n"

  method private add_let_var_def b =
    (Options_saida.Self.debug ~level:3 "adding let var: %s" b.l_var_info.lv_name);
    Logic_var.Hashtbl.add let_var_defs b.l_var_info b.l_body;

  method private print_harness_fn_name hf =
    self#print_line (Printf.sprintf "void %s()" hf.name);

  method private print_require_assumes hf =
    if (List.length hf.assumes) > 0 then
      self#print_line "//The requires-clauses translated into assumes";
    List.iter
      (
        fun ip ->
          self#print_indent;
          self#print_string "assume(";
          let _ = Printer.pp_identified_predicate out ip in
          self#print_string ");\n";
      )
      hf.assumes;

  method private print_special_ghost_ensure_assumes hf =
    let ghost_special_list = get_ensures_with_ghost_right_of_impl hf.asserts in
    if (List.length ghost_special_list) > 0 then
      self#print_line "//Special assumes of ghost-variables 'assigned to' in requires clause";
    List.iter
      (fun ip ->
        self#print_indent;
        self#print_string "assume(";
        let _ = Printer.pp_identified_predicate out ip in
        self#print_string ");\n";
      )
      ghost_special_list;

  method private print_ensure_asserts hf =
    if (List.length hf.asserts) > 0 then
      self#print_line "//The ensures-clauses translated into asserts";
    List.iter
      (
        fun ip ->
          self#print_indent;
          self#print_string "assert(";
          let _ = Printer.pp_identified_predicate out ip in
          self#print_string ");\n";
      )
      hf.asserts;

  method private print_log_var_decls hf =
    let log_vars = hf.block.log_vars in
    if (List.length log_vars > 0) then
      self#print_line "//printing logic var declarations, e.g. from \\forall or \\exists";
    List.iter
      (fun lv -> self#print_line (get_logic_var_decl_string lv))
      log_vars

  method private print_params_init hf =
    match hf.params with
    | [] -> ()
    | params ->
        self#print_line "//Declare the paramters of the function to be called";
        List.iter (fun vi -> self#print_line (get_var_decl_string vi)) params;

  method do_fun_spec hf : unit =
    let old_printer = Printer.current_printer () in
    let new_printer = (
      module HarnessPrinter.Make(struct 
        let name = hf.block.called_func
      end) : Printer.PrinterExtension) in

    Printer.update_printer (new_printer);
    (self#print_fun_spec 
    |> Kernel.Unicode.without_unicode
    |> HarnessPrinter.with_print_cil_as_is
    ) hf;
    Printer.set_printer old_printer;

  method private print_fun_spec hf =
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
    self#print_params_init hf;
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

    let params =
      String.concat ", " (List.map (fun vi -> vi.vname) hf.params)
    in
    (* self#print_string (Printf.sprintf "%s(%s);\n" hf.block.called_func params); *)
    (*Quick fix main2 for working in tricera*)
    let s = match hf.return_type.tnode with
      | TVoid -> ""
      | _ -> (get_type_decl_string hf.return_type) ^ " " ^ (self#result_string hf.block.called_func) ^ " = "
    in
    let fname = hf.block.called_func in
    if fname = "main" then
      self#print_line (s ^ "main2("^ params ^");\n")
    else
      self#print_line (s ^ fname ^ "("^ params ^");\n");

    (*Print the asserts, from the post-cond*)
    self#print_ensure_asserts hf;

    self#dec_indent;
    self#print_string "}\n";
  end