Require Import RegisterInvariants InstructionPortConnection.
From nbits Require Import NBits.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma formal_instruction_enable_connection invalid site mm phase old current result address enable clock mask data :
 VM.find 9176 current = Some (instruction_port_bundle address enable clock mask data) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 formal_connect invalid site mm phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result ->
 VM.find 9176 result = Some (instruction_port_bundle address (Gval (Fuint 1) [::true]) clock mask data).
Proof.
 intros Lookup Typed Connect.
 unfold formal_connect in Connect.
 change (formal_connect_bundle invalid site mm
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old current = Some result) in Connect.
 unfold formal_connect_bundle in Connect.
 cbn [HiF.base_ref eval_type_of_ref eval_hfexpr_validif_policy] in Connect.
 rewrite Lookup in Connect.
 cbn [instruction_port_bundle option_map type_of_val type_of_bundle_val] in Connect.
 rewrite Typed in Connect.
 cbn [adapt_hvalue_as_type repl_val_part convert_to_bundle_value option_map] in Connect.
 inversion Connect; subst result.
 rewrite (RegisterMapFacts.find_add_eq (eqxx 9176)). reflexivity.
Qed.
Print Assumptions formal_instruction_enable_connection.