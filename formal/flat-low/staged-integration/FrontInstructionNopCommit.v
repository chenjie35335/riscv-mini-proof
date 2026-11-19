Require Import CoreSocModel ComparisonNodes FrontInstructionNopNodes FormalInstructionWordsNormalCommit FormalInstructionResetConstants FormalInstructionResetCycle StagedRegisterHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem front_instruction_nop_commit_after_two invalid s0 s1 s2 result fetched held :
 VM.find 7796 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 75 s0 = Some fetched -> type_of_val fetched = Gtyp (Fuint 32) ->
 VM.find 7748 s0 = Some held -> type_of_val held = Gtyp (Fuint 32) ->
 VM.find 7799 s1 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 65 s2 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements = Some result ->
 VM.find 7748 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Kill Fetched FetchedType Held HeldType Advance Reset S1 S2 Commit.
 pose proof (front_instruction_inject_nop invalid s0 s0 s1 fetched Kill Fetched FetchedType S1) as Nop.
 pose proof (proj2 (instruction_register_shape 7748 ltac:(vm_compute;reflexivity))) as Present.
 assert (Held1 : VM.find 7748 s1 = Some held).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7748 Present S1). exact Held. }
 pose proof (front_instruction_select_nop invalid s1 s1 s2 held Advance Nop Held1 HeldType S2) as Source.
 assert (Held2 : VM.find 7748 s2 = Some held).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7748 Present S2). exact Held1. }
 exact (instruction_7748_formal_normal_commit invalid s2 s2 result held instruction_nop Held2 HeldType Reset Source (Logic.eq_refl _) Commit).
Qed.
Print Assumptions front_instruction_nop_commit_after_two.
