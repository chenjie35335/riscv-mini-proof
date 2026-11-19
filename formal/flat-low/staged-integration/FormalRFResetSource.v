Require Import CoreSocModel ComparisonNodes RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_symbolic_expr_8091 := (@Evalidif VarOrder.T (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false])).
Definition rf_symbolic_tail_8091 := match straight_drop 8598 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma rf_symbolic_position_8091 : straight_drop 8597 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 8091 rf_symbolic_expr_8091) rf_symbolic_tail_8091).
Proof. vm_compute. reflexivity. Qed.
Lemma rf_symbolic_suffix_8091 : formal_typed_suffix_safe flat_memories 8091 rf_symbolic_tail_8091.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rf_symbolic_nonregister_8091 : has_register 8091 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.

Definition rf_symbolic_source_site := validif_source_address
 (validif_raw_address [::] 8597 0 [::]).
Definition rf_symbolic_source_word inputs path :=
 proj1_sig (formal_symbolic_inputs inputs path rf_symbolic_source_site [::] 32).
Lemma rf_symbolic_expression inputs path old :
 eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path))
 (validif_raw_address [::] 8597 0 [::]) flat_memories rf_symbolic_expr_8091 old old =
 Some (Gval (Fuint 32) (rf_symbolic_source_word inputs path)).
Proof. reflexivity. Qed.
Lemma rf_symbolic_source_width inputs path : size (rf_symbolic_source_word inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path rf_symbolic_source_site [::] 32)). Qed.
Theorem rf_symbolic_reset_node inputs path old current result :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find 8091 result = Some (Gval (Fuint 32) (rf_symbolic_source_word inputs path)).
Proof.
 intro Step. eapply formal_combinational_known_node;
 [exact rf_symbolic_position_8091|exact rf_symbolic_suffix_8091|exact rf_symbolic_nonregister_8091|
 exact (rf_symbolic_expression inputs path old)|reflexivity|exact Step].
Qed.
Print Assumptions rf_symbolic_reset_node.
