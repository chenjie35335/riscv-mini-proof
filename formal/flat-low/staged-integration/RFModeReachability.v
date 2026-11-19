Require Import RFModeInvariant ExternalReset FormalObservationCommit ObservedJointRegisterConcrete
 ObservedInstructionNormalTransfer ReferenceBankObservation LoadTypeCorrespondence RFNonAluBubbleHazard
 CycleView CycleInstructionNop RFWritebackModeCycle CoreSocModel FormalLocalHistory ControlWritebackKill.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_writeback_mode_reachable memory inputs k observed v :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)v ->cycle_writeback_mode v.
Proof.
 intros Observe Legal View. destruct k as[|k].
 - exact(cycle_writeback_mode_base memory inputs observed v Observe View).
 - assert(PreviousLegal:generated_legal_trace memory inputs k).
   { destruct Legal as[Initial Trace]. split;[exact Initial|]. intros j Bound;apply Trace;lia. }
   destruct PreviousLegal as[Initial Trace].
   destruct(Trace k ltac:(lia))as[Defined[current[Current Assumptions]]].
   assert(PreviousLegal:generated_legal_trace memory inputs k)by(split;assumption).
   pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
   destruct(generated_run memory inputs(S k))as[committed|]eqn:Run;[|discriminate Expanded].
   assert(Transition:cycle_transition memory inputs k current observed).
   { unfold cycle_transition. split;[exact Current|]. split;[exact PreviousLegal|]. split;[exact Observe|]. split;[exact Legal|]. exists committed;exact Run. }
   destruct(legal_observation_reset memory inputs k PreviousLegal)as[reset Reset].
   destruct reset.
   + exact(cycle_writeback_mode_reset memory inputs k current observed v Transition Reset View).
   + destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Current PreviousLegal
       ltac:(apply(List.nth_error_In JointBoundaryRegisters.joint_boundary_registers 53%nat);vm_compute;reflexivity))as[instruction[Size Instruction]].
     pose proof(rf_mode_normal_successor memory inputs k current committed Current PreviousLegal Run Reset instruction Instruction)as Mode.
     pose proof(joint_register_run_observed memory inputs(S k)committed observed 7750 32 load_type_instruction_member Run Observe)as CopyInstruction.
     rewrite(observed_instruction_normal_equal memory inputs k current committed Current PreviousLegal Run Reset)Instruction(cva_commit_instruction _ _ View)in CopyInstruction.
     assert(Commit:cv_commit_instruction v=instruction).
     { exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)CopyInstruction). }
     pose proof(joint_register_run_observed memory inputs(S k)committed observed 7756 2 rf_nonalu_mode_member Run Observe)as CopyMode.
     rewrite Mode(cva_write_select _ _ View)in CopyMode.
     unfold cycle_writeback_mode. intro NonNop. rewrite Commit.
     inversion CopyMode. split;assumption.
Qed.
