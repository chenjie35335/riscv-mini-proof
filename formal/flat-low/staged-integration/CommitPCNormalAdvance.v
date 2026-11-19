Require Import CoreSocModel ComparisonNodes CommitPCControlledPropagation CommitPCAdvance CommitPCNormalCommit ExceptionPCSourceRegisters StagedRegisterHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem commit_pc_normal_advance invalid s0 s1 s2 s3 s4 result front old :
 size front = 32%nat ->
 VM.find 7749 s0 = Some (Gval (Fuint 32) front) ->
 VM.find 7751 s0 = Some (Gval (Fuint 32) old) ->
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 s1 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 s4 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 true s4 flat_statements = Some result ->
 VM.find 7751 result = Some (Gval (Fuint 32) front).
Proof.
 intros Size Front Old Stall Ex0 Ex1 Reset1 Reset4 S1 S2 S3 S4 Commit.
 pose proof (commit_pc_controlled_after_four invalid s0 s1 s2 s3 s4 front old false false false
 Front Old Stall Ex0 Ex1 Reset1 S1 S2 S3 S4) as Source.
 change (VM.find 7877 s4 = Some (Gval (Fuint 32) (CommitPCSelection.commit_pc_next false true front old))) in Source.
 rewrite (commit_pc_advance_value front old Size) in Source.
 assert (Old4 : VM.find 7751 s4 = Some (Gval (Fuint 32) old)).
 {
 rewrite (staged_combinational_holds_registers invalid flat_memories s3 s3 s4 flat_statements 7751 exception_pc_implementation_register S4).
 rewrite (staged_combinational_holds_registers invalid flat_memories s2 s2 s3 flat_statements 7751 exception_pc_implementation_register S3).
 rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7751 exception_pc_implementation_register S2).
 rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7751 exception_pc_implementation_register S1).
 exact Old. }
 exact (commit_pc_formal_normal_commit invalid s4 s4 result (Gval (Fuint 32) old) front Old4 (Logic.eq_refl _) Reset4 Source Size Commit).
Qed.
Print Assumptions commit_pc_normal_advance.
