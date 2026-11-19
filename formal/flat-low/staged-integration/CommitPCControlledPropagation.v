Require Import FormalPipelineControlHistory CommitPCSelection.
Require Import CommitPCSelectionNodes ExactWordMux StagedRegisterHold ExceptionPCSourceRegisters JointBoundaryRegisters.
Require Import RegisterInvariants CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames FormalTypedNodeEquation.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem commit_pc_controlled_after_four invalid s0 s1 s2 s3 s4 ex ew stall exception reset :
 VM.find 7749 s0 = Some (Gval (Fuint 32) ex) ->
 VM.find 7751 s0 = Some (Gval (Fuint 32) ew) ->
 VM.find 7765 s0 = Some (Gval (Fuint 1) [::stall]) ->
 VM.find 128 s0 = Some (Gval (Fuint 1) [::exception]) ->
 VM.find 128 s1 = Some (Gval (Fuint 1) [::exception]) ->
 VM.find 65 s1 = Some (Gval (Fuint 1) [::reset]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 7877 s4 = Some (Gval (Fuint 32)
 (commit_pc_next (reset || (negb stall && exception)) (negb stall && negb exception) ex ew)).
Proof.
 intros Ex Ew Stall Exception0 Exception1 Reset S1 S2 S3 S4.
 pose proof (pipeline_advance_after_two invalid s0 s1 s2 stall exception Stall Exception0 S1 S2) as Advance.
 pose proof (pipeline_flush_after_three invalid s0 s1 s2 s3 stall exception reset Stall Exception1 Reset S1 S2 S3) as Flush.
 assert (Held : forall id value, id \in [::7749;7751] -> VM.find id s0 = Some value -> VM.find id s2 = Some value).
 { intros id value Member Value.
   assert (Present : has_register id flat_statements = true).
   { move: Member. rewrite in_cons in_cons in_nil orbF. move/orP => [/eqP Eq|/eqP Eq]; subst id.
     - apply (proj2 (joint_boundary_register_properties 7749 32 ltac:(apply (List.nth_error_In joint_boundary_registers 54%nat); vm_compute; reflexivity))).
     - exact exception_pc_implementation_register. }
   rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements id Present S2).
   rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements id Present S1). exact Value. }
 apply (commit_pc_after_two invalid s2 s3 s4 (negb stall && negb exception) (reset || (negb stall && exception)) ex ew);
 [exact (Held 7749 _ ltac:(vm_compute; reflexivity) Ex)|exact (Held 7751 _ ltac:(vm_compute; reflexivity) Ew)|exact Advance|exact Flush|exact S3|exact S4].
Qed.
Print Assumptions commit_pc_controlled_after_four.
