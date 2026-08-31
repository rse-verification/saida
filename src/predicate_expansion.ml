(*
 * Copyright 2026 Scania CV AB
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * SPDX-License-Identifier: GPL-2.0+
 *)

open Cil_types

let predicate_name info = info.l_var_info.lv_name

let abort predicate info message =
  Options_saida.Self.abort ~current:true
    "SAIDA-E001: cannot expand predicate '%s' at %a: %s" (predicate_name info)
    Cil_datatype.Location.pretty predicate.pred_loc message

let find_active info active =
  List.exists (fun id -> id = info.l_var_info.lv_id) active

let bind_formals predicate info arguments =
  if List.length info.l_profile <> List.length arguments then
    abort predicate info
      (Format.asprintf "expected %d argument(s), received %d"
         (List.length info.l_profile)
         (List.length arguments));
  let bindings = Cil_datatype.Logic_var.Hashtbl.create 7 in
  List.iter2
    (fun formal argument ->
      Cil_datatype.Logic_var.Hashtbl.add bindings formal argument)
    info.l_profile arguments;
  bindings

let restricted_subset =
  "supported definitions use only direct comparisons between \
   mathematical-integer formals, exact signed C int parameters/results, and \
   unsuffixed decimal C-int-representable literals, joined by !, &&, or ||"

let reject predicate info reason =
  abort predicate info (Format.asprintf "%s; %s" reason restricted_subset)

let is_exact_signed_c_int typ =
  match typ.tnode with TInt IInt -> true | _ -> false

let is_mathematical_integer variable =
  match variable.lv_type with Linteger -> true | _ -> false

let validate_formals predicate info =
  List.iter
    (fun formal ->
      if not (is_mathematical_integer formal) then
        reject predicate info
          (Format.asprintf "formal parameter '%s' is not a mathematical integer"
             formal.lv_name))
    info.l_profile

let is_plain_decimal_literal representation =
  String.length representation > 0
  && String.for_all
       (fun character -> character >= '0' && character <= '9')
       representation

let validate_integer_literal predicate info term value representation =
  if term.term_type <> Linteger then
    reject predicate info "uses a non-mathematical-integer literal";
  begin match representation with
  | Some spelling when not (is_plain_decimal_literal spelling) ->
      reject predicate info
        "uses a suffixed or non-decimal integer literal spelling"
  | None | Some _ -> ()
  end;
  if not (Cil.fitsInInt IInt value) then
    reject predicate info "uses an integer literal outside signed C int range"

let validate_exact_c_int_leaf predicate info term =
  match term.term_node with
  | TLval (TVar variable, TNoOffset) ->
      begin match variable.lv_origin with
      | Some c_variable
        when c_variable.vformal && is_exact_signed_c_int c_variable.vtype ->
          ()
      | Some c_variable when c_variable.vglob ->
          reject predicate info
            (Format.asprintf "reads global C variable '%s'" c_variable.vname)
      | Some c_variable when not c_variable.vformal ->
          reject predicate info
            (Format.asprintf "reads non-parameter C variable '%s'"
               c_variable.vname)
      | Some c_variable ->
          reject predicate info
            (Format.asprintf
               "uses C parameter '%s' whose type is not exact signed C int"
               c_variable.vname)
      | None ->
          reject predicate info
            (Format.asprintf "reads free logic variable '%s'" variable.lv_name)
      end
  | TLval (TResult typ, TNoOffset) when is_exact_signed_c_int typ -> ()
  | TLval (TResult _, TNoOffset) ->
      reject predicate info "uses \\result whose type is not exact signed C int"
  | TLval (TMem _, _) -> reject predicate info "dereferences memory"
  | TLval (_, (TField _ | TIndex _ | TModel _)) ->
      reject predicate info "uses a field, index, or model-field access"
  | _ ->
      reject predicate info
        "uses an implicit conversion whose source is not a whole signed C int \
         parameter or result"

let validate_expanded_operand predicate info term =
  match term.term_node with
  | TConst (Integer (value, representation)) ->
      validate_integer_literal predicate info term value representation
  | TLval _ -> validate_exact_c_int_leaf predicate info term
  | TCast (true, Linteger, source) ->
      validate_exact_c_int_leaf predicate info source
  | TCast (false, _, _) -> reject predicate info "uses an explicit cast"
  | TCast (true, _, _) ->
      reject predicate info "uses an unsupported implicit conversion"
  | TConst (LEnum _) -> reject predicate info "uses an enum constant"
  | TConst _ -> reject predicate info "uses a non-integer constant"
  | TUnOp _ -> reject predicate info "uses a unary term operator"
  | TBinOp _ -> reject predicate info "uses a binary term operator"
  | Tif _ -> reject predicate info "uses a conditional term"
  | Tapp (logic_info, _, _) ->
      reject predicate info
        (Format.asprintf "calls logic function '%s'"
           (predicate_name logic_info))
  | Tlet _ | Tlambda _ | Tcomprehension _ ->
      reject predicate info "contains a binding term"
  | _ -> reject predicate info "uses an unsupported term"

let rec validate_expanded_predicate predicate info expanded =
  match expanded.pred_content with
  | Ptrue -> reject predicate info "uses Boolean constant \\true"
  | Pfalse -> reject predicate info "uses Boolean constant \\false"
  | Prel (_, left, right) ->
      validate_expanded_operand predicate info left;
      validate_expanded_operand predicate info right
  | Pnot inner -> validate_expanded_predicate predicate info inner
  | Pand (left, right) | Por (left, right) ->
      validate_expanded_predicate predicate info left;
      validate_expanded_predicate predicate info right
  | Papp _ ->
      reject predicate info "contains an unexpanded predicate application"
  | Pxor _ | Pimplies _ | Piff _ ->
      reject predicate info "uses an unsupported Boolean operator"
  | Pif _ -> reject predicate info "uses a conditional predicate"
  | Pforall _ | Pexists _ | Plet _ ->
      reject predicate info "contains a quantifier or local binding"
  | _ -> reject predicate info "uses an unsupported ACSL predicate"

let reject_definition_conversion predicate info source =
  match source.term_node with
  | TLval (TVar variable, TNoOffset) ->
      begin match variable.lv_origin with
      | Some c_variable when c_variable.vglob ->
          reject predicate info
            (Format.asprintf "reads global C variable '%s'" c_variable.vname)
      | _ ->
          reject predicate info "uses an implicit conversion in its definition"
      end
  | TLval (TMem _, _) -> reject predicate info "dereferences memory"
  | _ -> reject predicate info "uses an implicit conversion in its definition"

let instantiate_definition_operand predicate info bindings formals term =
  match term.term_node with
  | TConst (Integer (value, representation)) ->
      validate_integer_literal predicate info term value representation;
      term
  | TLval (TVar variable, TNoOffset)
    when Cil_datatype.Logic_var.Set.mem variable formals ->
      if not (is_mathematical_integer variable) then
        reject predicate info
          (Format.asprintf "formal parameter '%s' is not a mathematical integer"
             variable.lv_name);
      begin match Cil_datatype.Logic_var.Hashtbl.find_opt bindings variable with
      | Some argument -> argument
      | None ->
          reject predicate info
            (Format.asprintf "formal parameter '%s' is not bound"
               variable.lv_name)
      end
  | TLval (TVar variable, TNoOffset) ->
      begin match variable.lv_origin with
      | Some c_variable when c_variable.vglob ->
          reject predicate info
            (Format.asprintf "reads global C variable '%s'" c_variable.vname)
      | Some c_variable ->
          reject predicate info
            (Format.asprintf "reads non-formal C variable '%s'" c_variable.vname)
      | None ->
          reject predicate info
            (Format.asprintf "reads free logic variable '%s'" variable.lv_name)
      end
  | TLval (TResult _, TNoOffset) ->
      reject predicate info "uses \\result in a predicate definition"
  | TLval (TMem _, _) -> reject predicate info "dereferences memory"
  | TLval (_, (TField _ | TIndex _ | TModel _)) ->
      reject predicate info "uses a field, index, or model-field access"
  | TConst (LEnum _) -> reject predicate info "uses an enum constant"
  | TConst _ -> reject predicate info "uses a non-integer constant"
  | TUnOp _ -> reject predicate info "uses a unary term operator"
  | TBinOp _ -> reject predicate info "uses a binary term operator"
  | TCast (false, _, _) -> reject predicate info "uses an explicit cast"
  | TCast (true, _, source) ->
      reject_definition_conversion predicate info source
  | Tif _ -> reject predicate info "uses a conditional term"
  | Tapp (logic_info, _, _) ->
      reject predicate info
        (Format.asprintf "calls logic function '%s'"
           (predicate_name logic_info))
  | Tlet _ | Tlambda _ | Tcomprehension _ ->
      reject predicate info "contains a binding term"
  | _ -> reject predicate info "uses an unsupported term"

let rec expand_predicate active predicate =
  let visitor =
    object
      inherit Cil.nopCilVisitor

      method! vpredicate nested =
        match nested.pred_content with
        | Papp (info, labels, arguments) ->
            Cil.ChangeTo
              (expand_application active nested info labels arguments)
        | _ -> Cil.DoChildren
    end
  in
  Cil.visitCilPredicate visitor predicate

and instantiate_definition active predicate info bindings formals body =
  match body.pred_content with
  | Ptrue -> reject predicate info "uses Boolean constant \\true"
  | Pfalse -> reject predicate info "uses Boolean constant \\false"
  | Prel (relation, left, right) ->
      let left =
        instantiate_definition_operand predicate info bindings formals left
      in
      let right =
        instantiate_definition_operand predicate info bindings formals right
      in
      { body with pred_content = Prel (relation, left, right) }
  | Pnot inner ->
      let inner =
        instantiate_definition active predicate info bindings formals inner
      in
      { body with pred_content = Pnot inner }
  | Pand (left, right) ->
      let left =
        instantiate_definition active predicate info bindings formals left
      in
      let right =
        instantiate_definition active predicate info bindings formals right
      in
      { body with pred_content = Pand (left, right) }
  | Por (left, right) ->
      let left =
        instantiate_definition active predicate info bindings formals left
      in
      let right =
        instantiate_definition active predicate info bindings formals right
      in
      { body with pred_content = Por (left, right) }
  | Papp (nested_info, labels, arguments) ->
      let arguments =
        List.map
          (instantiate_definition_operand predicate info bindings formals)
          arguments
      in
      expand_application active body nested_info labels arguments
  | Pat (inner, _) ->
      ignore
        (instantiate_definition active predicate info bindings formals inner);
      reject predicate info "uses a labeled predicate"
  | Pxor _ | Pimplies _ | Piff _ ->
      reject predicate info "uses an unsupported Boolean operator"
  | Pif _ -> reject predicate info "uses a conditional predicate"
  | Pforall _ | Pexists _ | Plet _ ->
      reject predicate info "contains a quantifier or local binding"
  | _ -> reject predicate info "uses an unsupported ACSL predicate"

and expand_application active predicate info labels arguments =
  if info.l_type <> None then
    abort predicate info "the application resolves to a logic function";
  if info.l_tparams <> [] then
    abort predicate info "type-parameterized predicates are not supported";
  if find_active info active then
    abort predicate info "recursive predicate definitions are not supported";
  match info.l_body with
  | LBpred body ->
      validate_formals predicate info;
      List.iter (validate_expanded_operand predicate info) arguments;
      let bindings = bind_formals predicate info arguments in
      let formals = Cil_datatype.Logic_var.Set.of_list info.l_profile in
      let expanded =
        instantiate_definition
          (info.l_var_info.lv_id :: active)
          predicate info bindings formals body
      in
      if info.l_labels <> [] || labels <> [] then
        abort predicate info "label-parameterized predicates are not supported";
      validate_expanded_predicate predicate info expanded;
      expanded
  | LBnone ->
      abort predicate info
        "it has no direct definition; use 'predicate name(...) = expression'"
  | LBreads _ ->
      abort predicate info "predicate reads clauses are not supported"
  | LBinductive _ ->
      abort predicate info "inductive predicate definitions are not supported"
  | LBterm _ ->
      abort predicate info
        "the declaration contains a term rather than a predicate"

let expand_identified_predicate identified =
  let content = identified.ip_content in
  let statement = content.tp_statement in
  let expanded = expand_predicate [] statement in
  if expanded == statement then identified
  else { identified with ip_content = { content with tp_statement = expanded } }

let expand_behavior behavior =
  { behavior with
    b_assumes = List.map expand_identified_predicate behavior.b_assumes;
    b_requires = List.map expand_identified_predicate behavior.b_requires;
    b_post_cond =
      List.map
        (fun (kind, predicate) -> kind, expand_identified_predicate predicate)
        behavior.b_post_cond }

let expand_specification specification =
  { specification with
    spec_behavior = List.map expand_behavior specification.spec_behavior }
