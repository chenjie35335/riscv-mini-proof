Require Import CoreSocModel ComparisonNodes FormalReferenceX0 FormalReferenceX0Connections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma formal_reference_x0_path invalid s0 s1 s2 s3 :
 VM.find 3255 s0 = Some (Gval (Fuint 32) (zeros 32)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 1597 s3 = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Zero S1 S2 S3.
 assert (Eval : eval_hfexpr_with_memory flat_memories reference_x0_expr_3256 s0 s0 = Some (Gval (Fuint 32) (zeros 32))).
 { cbn [reference_x0_expr_3256 eval_hfexpr_with_memory eval_href_with_memory]. exact Zero. }
 pose proof (reference_x0_node_3256 invalid s0 s0 s1 _ Eval (Logic.eq_refl _) S1) as Z1.
 assert (Z2 : VM.find 1787 s2 = Some (Gval (Fuint 32) (zeros 32))).
 { eapply reference_output_connection_1787; [exact Z1|reflexivity|exact S2]. }
 eapply reference_output_connection_1597; [exact Z2|reflexivity|exact S3].
Qed.
Theorem formal_reference_x0_after_four invalid s0 s1 s2 s3 s4 value :
 VM.find 1707 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 2177 s0 = Some value -> type_of_val value = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 1597 s4 = Some (Gval (Fuint 32) (zeros 32)).
Proof.
 intros Valid Source Typed S1 S2 S3 S4.
 exact (formal_reference_x0_path invalid s1 s2 s3 s4
  (formal_reference_x0_iteration invalid s0 s0 s1 value Valid Source Typed S1) S2 S3 S4).
Qed.
Print Assumptions formal_reference_x0_after_four.
