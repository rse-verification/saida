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


(* Reduce a small, value-only subset of logic functions before the harness is
   printed. Keeping this in the typed ACSL AST avoids source-text substitution. *)
module LogicFunctionReducer = struct
  let error_code = "SAIDA-E001"

  let abort logic_name reason =
    Options_saida.Self.abort
      "[%s] Cannot safely reduce ACSL logic function '%s': %s"
      error_code logic_name reason

  let is_logic_integer = function
    | Linteger -> true
    | _ -> false

  let ensure_mathematical_arithmetic logic_name =
    match
      Tricera2acsl.validate_mathematical_arithmetic
        (Options_saida.TriceraOptions.get ())
    with
    | Ok () -> ()
    | Error reason -> abort logic_name reason

  let has_attribute name attributes =
    Ast_attributes.contains name attributes

  let unsupported_int_qualifier typ attributes =
    if Ast_types.has_qualifier "volatile" typ
       || has_attribute "volatile" attributes
    then Some "is volatile-qualified"
    else if Ast_types.has_attribute "atomic" typ
            || has_attribute "atomic" attributes
    then Some "is atomic-qualified"
    else None

  let validate_plain_signed_c_int typ attributes =
    match unsupported_int_qualifier typ attributes with
    | Some reason -> Error reason
    | None ->
      match typ.tnode with
      | TInt IInt -> Ok ()
      | _ ->
        Error
          "is not a direct signed C int value with an exact lift to ACSL integer"

  let same_logic_var left right = left.lv_id = right.lv_id

  let find_actual bindings logic_var =
    bindings
    |> List.find_opt (fun (formal, _) -> same_logic_var formal logic_var)
    |> Option.map snd

  let is_formal formals logic_var =
    List.exists (same_logic_var logic_var) formals

  let builtin_label_name = function
    | Here -> "Here"
    | Old -> "Old"
    | Pre -> "Pre"
    | Post -> "Post"
    | LoopEntry -> "LoopEntry"
    | LoopCurrent -> "LoopCurrent"
    | Init -> "Init"

  let rec validate_direct_signed_int_actual ?(old_allowed = true) term =
    match term.term_node with
    | Tat (inner, BuiltinLabel Old) when old_allowed ->
        validate_direct_signed_int_actual ~old_allowed:false inner
    | Tat (_, BuiltinLabel Old) ->
        Error
          "uses nested or repeated builtin label 'Old'; at most one 'Old' wrapper is supported"
    | Tat (_, BuiltinLabel label) ->
        Error
          (Format.asprintf
             "uses unsupported builtin label '%s'; only 'Old' is supported"
             (builtin_label_name label))
    | Tat (_, StmtLabel _) ->
        Error
          "uses a statement/custom label; only builtin label 'Old' is supported"
    | Tat (_, FormalLabel label) ->
        Error
          (Format.asprintf
             "uses unsupported formal label '%s'; only builtin label 'Old' is supported"
             label)
    | TCast (true, Linteger, inner) ->
        validate_direct_signed_int_actual ~old_allowed inner
    | TLval (TVar logic_var, TNoOffset) ->
        (match logic_var.lv_origin with
         | Some varinfo ->
             validate_plain_signed_c_int varinfo.vtype varinfo.vattr
         | _ ->
             Error
               "is not a direct signed C int value with an exact lift to ACSL integer")
    | TLval (TResult typ, TNoOffset) ->
        validate_plain_signed_c_int typ []
    | _ ->
        Error
          "is not a direct signed C int value with an exact lift to ACSL integer"

  let lift_actual_to_logic_integer actual =
    if is_logic_integer actual.term_type then actual
    else
      { actual with
        term_node = TCast (true, Linteger, actual);
        term_type = Linteger }

  let describe_logic_body = function
    | LBnone -> "it is declared without a definitional body"
    | LBreads _ -> "it has only a reads clause, not a definitional body"
    | LBterm _ -> "it has a term body"
    | LBpred _ -> "it defines a predicate rather than a term"
    | LBinductive _ -> "it has an inductive definition"

  let rec substitute_body logic_info bindings term =
    let logic_name = logic_info.l_var_info.lv_name in
    let require_logic_integer child =
      if not (is_logic_integer child.term_type) then
        abort logic_name
          "its definition mixes mathematical integers with a C, enum, unsigned, real, or other unsupported type"
    in
    let substitute = substitute_body logic_info bindings in
    (match term.term_node with
     | TCast _ ->
         abort logic_name
           "its definition contains a cast; narrowing, signedness-changing, and mixed C/logic casts are outside the semantics-preserving subset"
     | _ -> ());
    require_logic_integer term;
    match term.term_node with
    | TConst (Integer _ as constant) ->
        { term with term_node = TConst constant }
    | TLval (TVar logic_var, TNoOffset) ->
        (match find_actual bindings logic_var with
         | Some actual -> actual
         | None ->
             abort logic_name
               (Format.asprintf
                  "its body reads non-formal logic variable '%s'"
                  logic_var.lv_name))
    | TLval (TVar logic_var, _)
      when is_formal logic_info.l_profile logic_var ->
        abort logic_name
          (Format.asprintf
             "formal parameter '%s' is used with an array or field offset"
             logic_var.lv_name)
    | TUnOp (Neg, child) ->
        require_logic_integer child;
        { term with term_node = TUnOp (Neg, substitute child) }
    | TBinOp ((PlusA | MinusA | Mult as operator), left, right) ->
        require_logic_integer left;
        require_logic_integer right;
        { term with
          term_node = TBinOp (operator, substitute left, substitute right) }
    | Tapp (nested, _, _) ->
        if nested.l_var_info.lv_id = logic_info.l_var_info.lv_id then
          abort logic_name "its body is recursive"
        else
          abort logic_name
            (Format.asprintf
               "its body calls logic function '%s'"
               nested.l_var_info.lv_name)
    | TBinOp _ ->
        abort logic_name
          "its body uses a binary operator other than +, -, or *"
    | TUnOp _ ->
        abort logic_name "its body uses a unary operator other than unary -"
    | TConst _ ->
        abort logic_name "its definition contains a non-integer constant"
    | TLval _ ->
        abort logic_name "its body reads memory or a non-formal lvalue"
    | _ ->
        abort logic_name
          (Format.asprintf
             "its body contains unsupported term form %a"
             term_node_debug_print term.term_node)

  let reduce_application application logic_info labels arguments =
    let logic_name = logic_info.l_var_info.lv_name in
    ensure_mathematical_arithmetic logic_name;
    if logic_info.l_labels <> [] then
      abort logic_name "its definition declares one or more formal state labels";
    if labels <> [] then
      abort logic_name "its application supplies one or more state labels";
    if logic_info.l_tparams <> [] then
      abort logic_name "it has one or more logic type parameters";
    (match logic_info.l_type with
     | Some Linteger -> ()
     | Some _ ->
         abort logic_name
           "its result type is not the unbounded ACSL mathematical integer type"
     | None -> abort logic_name "it is a predicate, not a term-valued function");
    if not (List.for_all (fun formal -> is_logic_integer formal.lv_type)
              logic_info.l_profile)
    then
      abort logic_name
        "one or more formal parameters are not unbounded ACSL mathematical integers";
    if not (List.for_all (fun formal -> formal.lv_kind = LVFormal)
              logic_info.l_profile)
    then abort logic_name "its profile contains a non-formal parameter";
    if List.length logic_info.l_profile <> List.length arguments then
      abort logic_name
        (Format.asprintf
           "the application has %d arguments but its definition has %d formals"
           (List.length arguments) (List.length logic_info.l_profile));
    List.iteri
      (fun index argument ->
        match validate_direct_signed_int_actual argument with
        | Ok () -> ()
        | Error reason ->
            abort logic_name
              (Format.asprintf "application argument %d %s" (index + 1) reason))
      arguments;
    match logic_info.l_body with
    | LBterm body ->
        let bindings =
          List.combine logic_info.l_profile
            (List.map lift_actual_to_logic_integer arguments)
        in
        let reduced = substitute_body logic_info bindings body in
        { reduced with
          term_loc = application.term_loc;
          term_name = application.term_name }
    | unsupported_body ->
        abort logic_name (describe_logic_body unsupported_body)

  class application_reducer = object
    inherit Visitor.frama_c_inplace

    method! vterm term =
      match term.term_node with
      | Tapp _ ->
          Cil.DoChildrenPost
            (fun visited_term ->
              match visited_term.term_node with
              | Tapp (logic_info, labels, arguments) ->
                  reduce_application visited_term logic_info labels arguments
              | _ -> assert false)
      | _ -> Cil.DoChildren

    method! vpredicate_node = function
      | Papp (logic_info, _, _) ->
          abort logic_info.l_var_info.lv_name
            "it is used as a predicate; predicate definitions are outside this reduction"
      | _ -> Cil.DoChildren
  end

  let reduce_predicate predicate =
    let visitor = new application_reducer in
    Cil.visitCilPredicate (visitor :> Cil.cilVisitor) predicate

  let reduce_identified_predicate identified =
    let content = identified.ip_content in
    { identified with
      ip_content =
        { content with
          tp_statement = reduce_predicate content.tp_statement } }

  let reduce_behavior behavior =
    { behavior with
      b_assumes = List.map reduce_identified_predicate behavior.b_assumes;
      b_requires = List.map reduce_identified_predicate behavior.b_requires;
      b_post_cond =
        List.map
          (fun (kind, predicate) ->
            kind, reduce_identified_predicate predicate)
          behavior.b_post_cond }

  let reduce_specification spec =
    { spec with spec_behavior = List.map reduce_behavior spec.spec_behavior }
end

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
        (* A binding is valid only while its Tlet/Plet body is printed. *)
        val mutable let_var_defs = Logic_var.Hashtbl.create 10
        (* Number of enclosing ACSL labels while the binding is active. *)
        val mutable label_depth = 0
  
        method private with_let_var_def b f =
          (Options_saida.Self.debug ~level:3 "adding let var: %s" b.l_var_info.lv_name);
          let previous = Logic_var.Hashtbl.find_opt let_var_defs b.l_var_info in
          Logic_var.Hashtbl.remove let_var_defs b.l_var_info;
          Logic_var.Hashtbl.add let_var_defs b.l_var_info (b.l_body, label_depth);
          Fun.protect
            ~finally:(fun () ->
              Logic_var.Hashtbl.remove let_var_defs b.l_var_info;
              match previous with
              | Some value -> Logic_var.Hashtbl.add let_var_defs b.l_var_info value
              | None -> ())
            f;
  
        (* Note: Must match whatever tricera_print is using *)
        method private result_string (fname : string) =
          fname ^ "_result";
  
        method private wrap_in_label : 'a. 
          Format.formatter -> logic_label -> logic_type -> (Format.formatter -> 'a -> unit) -> 'a -> unit = 
            fun fmt ll t f arg ->
              let previous_depth = label_depth in
              label_depth <- previous_depth + 1;
              Fun.protect
                ~finally:(fun () -> label_depth <- previous_depth)
                (fun () ->
                  Format.fprintf fmt "$at(\"%a\", (%a)(%a))"
                    super#logic_label ll
                    (self#typ None) (Logic_utils.logicCType (to_c_type t))
                    f arg);

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
              | Some(l_body, binding_depth) ->
                 if label_depth > binding_depth then
                   Options_saida.Self.abort
                     "Unsupported \\let binding '%s' across an ACSL state label. The binding was created outside \\old/\\at but is used inside it; Saida refuses to inline this expression because it could change the state of the aliased value. Move the \\let inside the label or write the labelled expression explicitly."
                     lv.lv_name
                 else
                   (match l_body with
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
            self#with_let_var_def def (fun () -> self#term fmt body);
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
              self#with_let_var_def b (fun () -> self#predicate fmt p);
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
  mutable pre_call_asserts: Cil_types.identified_predicate list;
  mutable behavior_requires: Cil_types.identified_predicate list;
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


class quantifier_finder existential universal = object
  inherit Visitor.frama_c_inplace

  method! vpredicate predicate =
    match predicate.pred_content with
    | Pexists _ ->
      existential := true;
      Cil.DoChildren
    | Pforall _ ->
      universal := true;
      Cil.DoChildren
    | _ -> Cil.DoChildren
end


let predicate_quantifiers predicate =
  let existential = ref false in
  let universal = ref false in
  let visitor = new quantifier_finder existential universal in
  ignore
    (Visitor.visitFramacPredicate
       (visitor :> Visitor.frama_c_visitor)
       predicate);
  (!existential, !universal)


let make_harness_func fdec spec =
  let spec = LogicFunctionReducer.reduce_specification spec in
  let behavs = spec.spec_behavior in
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
  let is_default_behavior b = Cil.is_default_behavior b in
  let predicate_kind_name = function
    | Assert -> "assert"
    | Check -> "check"
    | Admit -> "admit"
  in
  let reject_unsupported_predicate ~allow_universal behavior clause predicate =
    let existential, universal =
      predicate_quantifiers predicate.ip_content.tp_statement
    in
    if existential then
      Options_saida.Self.abort
        "[SAIDA-E001] Existential quantification is unsupported on %s in behavior %s of function %s"
        clause behavior.b_name fdec.svar.vorig_name;
    if universal && not allow_universal then
      Options_saida.Self.abort
        "[SAIDA-E004] Universal quantification is supported only on postconditions; found it on %s in behavior %s of function %s"
        clause behavior.b_name fdec.svar.vorig_name;
    match predicate.ip_content.tp_kind with
     | Assert -> ()
     | kind ->
       Options_saida.Self.abort
         "Unsupported %s predicate kind on %s in behavior %s of function %s; Saida cannot preserve its proof semantics"
         (predicate_kind_name kind) clause behavior.b_name
         fdec.svar.vorig_name
  in
  let reject_unsupported_clauses () =
    if spec.spec_variant <> None then
      Options_saida.Self.abort
        "Unsupported decreases clause in the contract of %s"
        fdec.svar.vorig_name;
    if spec.spec_terminates <> None then
      Options_saida.Self.abort
        "Unsupported terminates clause in the contract of %s"
        fdec.svar.vorig_name;
    List.iter
      (fun b ->
        List.iter
          (reject_unsupported_predicate ~allow_universal:false b "assumes")
          b.b_assumes;
        List.iter
          (reject_unsupported_predicate ~allow_universal:false b "requires")
          b.b_requires;
        List.iter
          (fun (_, predicate) ->
            reject_unsupported_predicate
              ~allow_universal:true b "ensures" predicate)
          b.b_post_cond;
        (match b.b_assigns with
         | WritesAny -> ()
         | Writes _ when is_default_behavior b ->
           Options_saida.Self.warning
             "[SAIDA-W001] The function-level assigns clause of %s is preserved but is not checked by Saida's inference harness; validate the complete contract with WP."
             fdec.svar.vorig_name
         | Writes _ ->
            Options_saida.Self.abort
              "Unsupported assigns clause in behavior %s of function %s"
              b.b_name fdec.svar.vorig_name);
        (match b.b_allocation with
         | FreeAllocAny -> ()
         | FreeAlloc _ ->
           Options_saida.Self.abort
             "Unsupported allocation clause in behavior %s of function %s"
             b.b_name fdec.svar.vorig_name);
        if b.b_extended <> [] then
          Options_saida.Self.abort
            "Unsupported extended clause in behavior %s of function %s"
            b.b_name fdec.svar.vorig_name;
        List.iter
          (fun (kind, _) ->
            match kind with
            | Normal -> ()
            | Exits | Breaks | Continues | Returns ->
              Options_saida.Self.abort
                "Unsupported non-normal postcondition in behavior %s of function %s"
                b.b_name fdec.svar.vorig_name)
          b.b_post_cond)
      behavs
  in
  reject_unsupported_clauses ();
  let predicate_of_id_predicate ip = ip.ip_content.tp_statement in
  let conjunction predicates =
    Logic_const.pands (List.map predicate_of_id_predicate predicates)
  in
  let replace_predicate predicate statement =
    Logic_const.new_predicate
      ~kind:predicate.ip_content.tp_kind
      statement
  in
  let behavior_condition b = conjunction b.b_assumes in
  let complete_assertions =
    spec.spec_complete_behaviors
    |> List.map (fun names ->
      Ast_info.complete_behaviors spec names
      |> Logic_const.new_predicate)
  in
  let disjoint_assertions =
    spec.spec_disjoint_behaviors
    |> List.map (fun names ->
      Ast_info.disjoint_behaviors spec names
      |> Logic_const.new_predicate)
  in
  let conditional_requirements b =
    if b.b_assumes = [] then b.b_requires
    else
      List.map
        (fun requirement ->
          replace_predicate requirement
            (Logic_const.pimplies
               (behavior_condition b,
                predicate_of_id_predicate requirement)))
        b.b_requires
  in
  let guarded_postcondition b post =
    match b.b_assumes with
    | [] -> post
    | _ ->
      replace_predicate post
        (Logic_const.pimplies
           (Logic_const.pold (behavior_condition b),
            post.ip_content.tp_statement))
  in
  let assumes =
    behavs
    |> List.filter is_default_behavior
    |> List.concat_map (fun b -> b.b_requires)
  in
  let behavior_requires =
    behavs
    |> List.filter (fun b -> not (is_default_behavior b))
    |> List.concat_map conditional_requirements
  in
  let behavior_asserts =
    behavs
    |> List.filter (fun b -> not (is_default_behavior b))
    |> List.concat_map (fun b ->
      List.map (guarded_postcondition b) (List.map snd b.b_post_cond))
  in
  let default_asserts =
    behavs
    |> List.filter is_default_behavior
    |> List.concat_map (fun b -> List.map snd b.b_post_cond)
  in
  let asserts = default_asserts @ behavior_asserts in
  let pre_call_asserts = complete_assertions @ disjoint_assertions in
  (*TODO: Extract vars only in \old-context instead? *)
  let log_vars_in_post = get_logic_vars asserts in
  let log_vars_in_pre_asserts = get_logic_vars pre_call_asserts in
  let log_vars_in_behavior_requires = get_logic_vars behavior_requires in
  let log_vars_in_pre = get_logic_vars assumes in
  let all_log_vars =
    log_vars_in_pre @ log_vars_in_pre_asserts
    @ log_vars_in_behavior_requires @ log_vars_in_post
  in
  let h_block = { called_func = fdec.svar.vorig_name; log_vars = all_log_vars} in
  let f_ret_type = match fdec.svar.vtype.tnode with
    | TFun(r, _, _) -> r
    | _ -> fdec.svar.vtype (*shouldnt happen*)
  in
  { name = Format.sprintf "saida_harness_%s" fdec.svar.vorig_name
  ; block = h_block
  ; assumes = assumes
  ; pre_call_asserts = pre_call_asserts
  ; behavior_requires = behavior_requires
  ; asserts = asserts
  ; params = fdec.sformals
  ; return_type = f_ret_type;
    (* ghost_vars_right_of_impl_in_post = []; *)
  }


let get_type_decl_string typ =
  Format.asprintf "%a" Printer.pp_typ typ


let get_var_decl_string vi =
  let type_string = get_type_decl_string vi.vtype in
  Printf.sprintf "%s %s" type_string vi.vname


let get_logic_var_decl_string lv =
  let type_string =
    match lv.lv_type with
      | Ctype(inner_type) -> get_type_decl_string inner_type
      | Linteger -> "int"
      | _ -> "Unspported_type_of_logic_var"
  in
  Printf.sprintf "%s %s" type_string lv.lv_name


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
  Class for collecting information about function contracts.
  Inspired by Frama-C development guide:
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
      hf_list <- (make_harness_func (Option.get(curr_func)) s)::hf_list;
    Cil.SkipChildren
end


(*
  Class for pretty printing function contracts as harness function with
  assume and asserts in tricera style.
  TODO: This should be turned into a module.
*)
class tricera_print out = object (self)
  method private result_string fname = fname ^ "_result";

  method private print_newline = Format.fprintf out "@,"

  method private print_require_assumes hf =
    match hf.assumes with
    | [] -> ()
    | assumes ->
      Format.fprintf out "//The requires-clauses translated into assumes@,";
      List.iter
        (fun ip ->
          Format.fprintf out "assume(%a);@," 
            Printer.pp_predicate_node ip.ip_content.tp_statement.pred_content)
        assumes

  method private print_special_ghost_ensure_assumes hf =
    match get_ensures_with_ghost_right_of_impl hf.asserts with
    | [] -> ()
    | ghosts ->
      Format.fprintf out "//Special assumes of ghost-variables 'assigned to' in requires clause@,";
      List.iter
        (fun ip ->
          Format.fprintf out "assume(%a);@,"
            Printer.pp_predicate_node ip.ip_content.tp_statement.pred_content)
        ghosts

  method private print_ensure_asserts hf =
    match hf.asserts with
    | [] -> ()
    | asserts ->
      Format.fprintf out "//The ensures-clauses translated into asserts@,";
      List.iter
        (fun ip -> 
          Format.fprintf out "assert(%a);@,"
            Printer.pp_predicate_node ip.ip_content.tp_statement.pred_content)
        asserts

  method private print_pre_call_asserts hf =
    match hf.pre_call_asserts with
    | [] -> ()
    | assertions ->
      Format.fprintf out
        "//The complete/disjoint behavior declarations translated into asserts@,";
      List.iter
        (fun ip ->
          Format.fprintf out "assert(%a);@,"
            Printer.pp_predicate_node ip.ip_content.tp_statement.pred_content)
        assertions

  method private print_behavior_require_assumes hf =
    match hf.behavior_requires with
    | [] -> ()
    | requirements ->
      Format.fprintf out
        "//Behavior-specific requires translated into conditional assumes@,";
      List.iter
        (fun ip ->
          Format.fprintf out "assume(%a);@,"
            Printer.pp_predicate_node ip.ip_content.tp_statement.pred_content)
        requirements

  method private print_log_var_decls hf =
    match hf.block.log_vars with
    | [] -> ()
    | log_vars ->
      Format.fprintf out "//Logic var declarations, e.g. from \\forall or \\exists@,";
      List.iter
        (fun lv -> Format.fprintf out "%s;@," (get_logic_var_decl_string lv))
        log_vars

  method private print_params_init hf =
    match hf.params with
    | [] -> ()
    | params ->
        Format.fprintf out "//Declare the paramters of the function to be called@,";
        List.iter (fun vi -> Format.fprintf out "%s;@," (get_var_decl_string vi)) params

  method private print_function_call hf =
    Format.fprintf out "//Function call that the harness function verifies@,";
    let params = String.concat ", " (List.map (fun vi -> vi.vname) hf.params) in
    let result = match hf.return_type.tnode with
      | TVoid -> ""
      | _ ->
        Format.asprintf "%s %s = "
          (get_type_decl_string hf.return_type) (self#result_string hf.block.called_func)
    in
    Format.fprintf out "%s%s(%s);@,@," result hf.block.called_func params

  method private inner_harness_name hf = 
    hf.name ^ "_inner"

  method private print_inner_harness_call hf =
    Format.fprintf out "//Call inner harness function@,";
    let params = String.concat ", " (List.map (fun vi -> vi.vname) hf.params) in
    Format.fprintf out "%s(%s);@,@," (self#inner_harness_name hf) params

  method private print_decl fmt vars =
    match vars with
    | [] -> ()
    | head::[] ->
        Format.fprintf fmt "%s" (get_var_decl_string head)
    | head::tail -> 
        Format.fprintf fmt "%s," (get_var_decl_string head);
        self#print_decl fmt tail
    
  method private print_inner_harness hf =
    Format.fprintf out "@[<v>%s %s(%a)@,@[<v 2>{@," 
      (get_type_decl_string hf.return_type)
      (self#inner_harness_name hf)
      self#print_decl hf.params;

    (*Print logical variable declarations, e.g. from \forall, \exists or \let*)
    self#print_log_var_decls hf;
    self#print_newline;

    (*Print the assumes (from pre-cond)*)
    self#print_require_assumes hf;
    self#print_newline;

    (*Prove complete/disjoint behavior declarations before the function call.*)
    (match hf.pre_call_asserts with
     | [] -> ()
     | _ ->
       self#print_pre_call_asserts hf;
       self#print_newline);

    (*Apply behavior-specific requires only after checking coverage and
      exclusion under the function's main precondition.*)
    (match hf.behavior_requires with
     | [] -> ()
     | _ ->
       self#print_behavior_require_assumes hf;
       self#print_newline);

    (*Print assumes for special ghost-var ensures*)
    (*experimental feature*)
    (* self#print_special_ghost_ensure_assumes hf;
    self#print_newline; *)

    (*Print the function call to the function we are harness for*)
    self#print_function_call hf;

    (*Print the asserts, from the post-cond*)
    self#print_ensure_asserts hf;

    Format.fprintf out "@]@,}@,@]" 
    
  method private print_outer_harness hf =
    Format.fprintf out "@[<v>%s %s()@,@[<v 2>{@," "void" hf.name;

    self#print_params_init hf;
    self#print_newline;
    self#print_inner_harness_call hf;

    Format.fprintf out "@]@,}@,@]" 

  method private print_harness_functions hf =
    self#print_inner_harness hf;
    self#print_outer_harness hf

  (* 
     Entry point. Responsible for setting up a suitable
     Printer instance before printing the harness function.
  *)
  method print_harness hf : unit =
    let old_printer = Printer.current_printer () in
    let new_printer = (
      module HarnessPrinter.Make(struct 
        let name = hf.block.called_func
      end) : Printer.PrinterExtension) in

    Printer.update_printer (new_printer);
    (self#print_harness_functions 
    |> Kernel.Unicode.without_unicode
    |> HarnessPrinter.with_print_cil_as_is
    ) hf;
    Printer.set_printer old_printer
end
