Require Import CoreSocModel ComparisonNodes FormalX0ConeNodes FormalX0WriteDataShape FormalSuccessfulNode UInt32ZeroMuxType.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem x0_selected_type invalid old current result data :
 VM.find 988 old = Some data -> type_of_val data = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 989 result = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros Data Typed Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result position_989 Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories expr_989 old old = Some value) in Eval.
 exists value. split.
 - rewrite (node_989_full_iteration invalid old current result Step). exact Eval.
 - unfold expr_989 in Eval. eapply uint32_zero_mux_result_type; [exact Data|exact Typed|exact Eval].
Qed.
Theorem x0_selected_type_after_three invalid s0 s1 s2 s3 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 exists value, VM.find 989 s3 = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intros S1 S2 S3.
 destruct (x0_write_data_typed_after_two invalid s0 s1 s2 S1 S2) as [data [Data Typed]].
 exact (x0_selected_type invalid s2 s2 s3 data Data Typed S3).
Qed.
Print Assumptions x0_selected_type_after_three.
