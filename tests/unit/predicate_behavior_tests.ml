open Frama_c_kernel
open Cil_types

module Expansion = Saida__.Predicate_expansion

class application_counter count = object
  inherit Visitor.frama_c_inplace

  method! vpredicate_node = function
    | Papp _ ->
        incr count;
        Cil.DoChildren
    | _ -> Cil.DoChildren
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

let behavior_names specification =
  specification.spec_behavior |> List.map (fun behavior -> behavior.b_name)

let () =
  if Array.length Sys.argv <> 2 then
    failwith "expected the predicate fixture path";
  ignore (Project.create "predicate-behavior-test");
  let source = File.from_filename (Filepath.of_string Sys.argv.(1)) in
  File.init_from_c_files [source];
  let kernel_function = Globals.Functions.find_by_name "entry" in
  let specification = Annotations.funspec kernel_function in
  let behaviors = specification.spec_behavior in
  let assumes = predicates_of behaviors (fun behavior -> behavior.b_assumes) in
  let requires = predicates_of behaviors (fun behavior -> behavior.b_requires) in
  let ensures = postconditions behaviors in
  expect_positive "assumes before expansion" (count_applications assumes);
  expect_positive "requires before expansion" (count_applications requires);
  expect_positive "ensures before expansion" (count_applications ensures);
  let expanded = Expansion.expand_specification specification in
  if behavior_names expanded <> behavior_names specification then
    failwith "behavior names changed during predicate expansion";
  expect_zero "assumes after expansion"
    (count_applications
       (predicates_of expanded.spec_behavior (fun behavior -> behavior.b_assumes)));
  expect_zero "requires after expansion"
    (count_applications
       (predicates_of expanded.spec_behavior (fun behavior -> behavior.b_requires)));
  expect_zero "ensures after expansion"
    (count_applications (postconditions expanded.spec_behavior))
