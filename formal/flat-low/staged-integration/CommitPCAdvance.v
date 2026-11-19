Require Import CoreSocModel ComparisonNodes CommitPCSelection CommitPCNormalCommit ExactWordMux ExceptionPCSourceRegisters StagedRegisterHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma mux_word_selected_sized bit left right :
 size (if bit then left else right) = 32%nat ->
 mux_word bit left right = (if bit then left else right).
Proof.
 intro Size. unfold mux_word. rewrite -Size take_size.
 unfold zext_to. rewrite subnn. unfold zext. rewrite cats0. reflexivity.
Qed.
Lemma commit_pc_advance_value front old :
 size front = 32%nat -> commit_pc_next false true front old = front.
Proof.
 intro Size. unfold commit_pc_next.
 rewrite (mux_word_selected_sized true front old Size).
 exact (mux_word_selected_sized false old front Size).
Qed.
Theorem commit_pc_advance_after_two invalid s0 s1 s2 result front old :
 size front = 32%nat ->
 VM.find 7749 s0 = Some (Gval (Fuint 32) front) ->
 VM.find 7751 s0 = Some (Gval (Fuint 32) old) ->
 VM.find 7855 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7852 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 s2 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements = Some result ->
 VM.find 7751 result = Some (Gval (Fuint 32) front).
Proof.
 intros Size Front Old Advance Hold Reset S1 S2 Commit.
 pose proof (commit_pc_after_two invalid s0 s1 s2 true false front old Front Old Advance Hold S1 S2) as Source.
 rewrite (commit_pc_advance_value front old Size) in Source.
 assert (Old2 : VM.find 7751 s2 = Some (Gval (Fuint 32) old)).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7751 exception_pc_implementation_register S2).
   rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7751 exception_pc_implementation_register S1). exact Old. }
 exact (commit_pc_formal_normal_commit invalid s2 s2 result (Gval (Fuint 32) old) front Old2 (Logic.eq_refl _) Reset Source Size Commit).
Qed.
Print Assumptions commit_pc_advance_after_two.
