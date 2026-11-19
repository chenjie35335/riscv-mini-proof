Require Import CoreSocModel ComparisonNodes FetchPCResetNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition fetch_pc_reset_word32 := [::false;false] ++ nseq 7 true ++ nseq 23 false.
Definition fetch_pc_reset_word33 := fetch_pc_reset_word32 ++ [::false].
Lemma fetch_pc_reset_size32 : size fetch_pc_reset_word32 = 32%nat.
Proof. reflexivity. Qed.
Lemma fetch_pc_reset_size33 : size fetch_pc_reset_word33 = 33%nat.
Proof. reflexivity. Qed.
Lemma fetch_pc_reset_unsigned : to_nat fetch_pc_reset_word33 = 508%nat.
Proof. vm_compute. reflexivity. Qed.
Theorem fetch_pc_reset_subtraction invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7766 result = Some (Gval (Fuint 33) fetch_pc_reset_word33).
Proof.
 intro Step. apply (fetch_pc_reset_7766_value invalid old current result 33 fetch_pc_reset_word33); [|exact Step].
 vm_compute. reflexivity.
Qed.
Theorem fetch_pc_reset_value_after_two invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7767 s2 = Some (Gval (Fuint 32) fetch_pc_reset_word32).
Proof.
 intros S1 S2.
 pose proof (fetch_pc_reset_subtraction invalid s0 s0 s1 S1) as Subtract.
 apply (fetch_pc_reset_7767_value invalid s1 s1 s2 32 fetch_pc_reset_word32); [|exact S2].
 cbn [fetch_pc_reset_7767_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Subtract.
 reflexivity.
Qed.
Print Assumptions fetch_pc_reset_value_after_two.
