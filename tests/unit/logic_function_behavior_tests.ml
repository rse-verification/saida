open Frama_c_kernel
open Cil_types

module Reducer = Saida__.Saida_vis.LogicFunctionReducer
module Validation = Saida__.Tricera2acsl

class application_counter count = object
  inherit Visitor.frama_c_inplace

  method! vterm term =
    (match term.term_node with
     | Tapp _ -> incr count
     | _ -> ());
    Cil.DoChildren
end

let count_applications predicates =
  let count = ref 0 in
  let visitor = new application_counter count in
  List.iter
    (fun predicate ->
      ignore
        (Visitor.visitFramacPredicate
           (visitor :> Visitor.frama_c_visitor)
           predicate.ip_content.tp_statement))
    predicates;
  !count

let predicates_of behaviors field =
  behaviors |> List.concat_map field

let postconditions behaviors =
  predicates_of behaviors
    (fun behavior -> List.map snd behavior.b_post_cond)

let expect_positive label count =
  if count <= 0 then
    failwith (Format.sprintf "%s: expected at least one application" label)

let expect_zero label count =
  if count <> 0 then
    failwith
      (Format.sprintf "%s: expected no applications, found %d" label count)

let expect_equal label expected actual =
  if expected <> actual then
    failwith
      (Format.sprintf "%s: expected %s, got %s" label expected actual)

let behavior_names specification =
  specification.spec_behavior |> List.map (fun behavior -> behavior.b_name)

let () =
  if Array.length Sys.argv <> 2 then
    failwith "expected the logic-function fixture path";
  ignore (Project.create "logic-function-behavior-test");
  let source = File.from_filename (Filepath.of_string Sys.argv.(1)) in
  File.init_from_c_files [source];
  let kernel_function = Globals.Functions.find_by_name "entry" in
  let specification = Annotations.funspec kernel_function in
  let behaviors = specification.spec_behavior in
  let assumes = predicates_of behaviors (fun behavior -> behavior.b_assumes) in
  let requires = predicates_of behaviors (fun behavior -> behavior.b_requires) in
  let ensures = postconditions behaviors in
  expect_positive "assumes before reduction" (count_applications assumes);
  expect_positive "requires before reduction" (count_applications requires);
  expect_positive "ensures before reduction" (count_applications ensures);
  let reduced = Reducer.reduce_specification specification in
  expect_equal "behavior names after reduction"
    (String.concat "," (behavior_names specification))
    (String.concat "," (behavior_names reduced));
  expect_zero "assumes after reduction"
    (count_applications
       (predicates_of reduced.spec_behavior (fun behavior -> behavior.b_assumes)));
  expect_zero "requires after reduction"
    (count_applications
       (predicates_of reduced.spec_behavior (fun behavior -> behavior.b_requires)));
  expect_zero "ensures after reduction"
    (count_applications (postconditions reduced.spec_behavior));
  (match Validation.validate_mathematical_arithmetic "-acsl" with
   | Ok () -> ()
   | Error reason -> failwith ("default arithmetic mode: " ^ reason));
  (match Validation.validate_mathematical_arithmetic "-arithMode:math" with
   | Ok () -> ()
   | Error reason -> failwith ("mathematical arithmetic mode: " ^ reason));
  (match Validation.validate_mathematical_arithmetic "-arithMode:bitvectors" with
   | Error _ -> ()
   | Ok () -> failwith "bitvector arithmetic mode should be rejected")
