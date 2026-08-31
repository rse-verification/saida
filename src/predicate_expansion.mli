val expand_identified_predicate :
  Cil_types.identified_predicate -> Cil_types.identified_predicate
(** Expand the restricted class of ACSL predicate applications supported by
    Saida's TriCera harness. Unsupported definitions abort Saida before the
    harness or an inferred contract is produced. *)

val expand_specification : Cil_types.funspec -> Cil_types.funspec
(** Expand predicate applications in every behavior clause while preserving
    the surrounding behavior and contract metadata. *)
