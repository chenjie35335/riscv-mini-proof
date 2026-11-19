Require Import JointBoundaryReachable.
From Coq Require Import List.
Require Import FormalInstructionResetBase FormalInstructionResetCycle.
Require Import StoreActiveWidthCycle StoreWidthReachableType StoreWidthInitialization JointBoundaryReachable
 ObservedInstructionNormalTransfer StoreTypeCorrespondence CoreSocModel FormalLocalHistory FormalObservationCommit
 JointBoundaryInduction ExternalReset StagedObservedRegister FormalFetchType RegisterInvariants JointBoundaryRegisters.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition store_active_width_invariant env := forall instruction lane,
 VM.find 7750 env=Some(Gval(Fuint 32)instruction) ->
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->
 VM.find 8040 env=Some(Gval(Fuint 6)(store_width_word lane)).
Theorem store_active_width_run memory inputs k states :
 generated_run memory inputs k=Some states ->generated_legal_trace memory inputs k ->
 store_active_width_invariant(top_environment states).
Proof.
 destruct k as[|k];intros Run Legal instruction lane Instruction Lane Store.
 - destruct(instruction_run_zero memory inputs states Run)as[env[Env[Front Nop]]].
   unfold top_environment in Instruction;rewrite Env Nop in Instruction;inversion Instruction;subst instruction. exfalso;exact(store_type_nop_not_store lane Lane Store).
 - assert(PriorLegal:generated_legal_trace memory inputs k).
   { apply(joint_legal_trace_prefix memory inputs(S k)k Legal);lia. }
   destruct(generated_successful_commit memory inputs k states Run)as[observed[Observe Commit]].
   destruct(legal_observation_reset memory inputs k PriorLegal)as[reset Reset].
   destruct reset.
   + pose proof Run as Next. rewrite generated_run_successor in Next.
     destruct (generated_run memory inputs k) as [previous|] eqn:Previous;[|discriminate Next].
     destruct (fetch9220_run_type memory inputs k previous Previous) as [old [value [Old Rest]]].
     destruct (joint_boundary_reachable memory inputs k previous Previous PriorLegal) as [Registers Storage].
     unfold top_environment in Registers. rewrite Old in Registers.
     destruct (Registers 7748%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity)) as [front [FrontSize Front]].
     destruct (Registers 7750%nat 32%nat store_type_instruction_member) as [oldinstruction [Size OldInstruction]].
     destruct (instruction_real_reset_cycle (generated_observation_input inputs k) previous old states
     (Gval (Fuint 32) front) (Gval (Fuint 32) oldinstruction) Old Front (Logic.eq_refl _) OldInstruction (Logic.eq_refl _) Reset Next)
     as [env [Env [FrontNop Nop]]].
     unfold top_environment in Instruction. rewrite Env Nop in Instruction. inversion Instruction;subst instruction. exfalso;exact(store_type_nop_not_store lane Lane Store).
   + pose proof(observed_instruction_normal_equal memory inputs k observed states Observe PriorLegal Run Reset)as Transfer.
     rewrite Transfer in Instruction.
     exact(store_active_width_cycle memory inputs k observed states instruction lane Observe PriorLegal Run Reset Instruction Lane Store).
Qed.
Theorem store_active_width_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (lane<3)%coq_nat ->store_type_is_store instruction lane ->
 VM.find 8040(top_environment observed)=Some(Gval(Fuint 6)(store_width_word lane)).
Proof.
 intros Observe Legal Instruction Lane Store.
 pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct(generated_run memory inputs k)as[committed|]eqn:Run;[|discriminate].
 destruct(fetch9220_run_type memory inputs k committed Run)as[env[value[Env Rest]]].
 pose proof(staged_observed_register_copies memory inputs k committed env observed 8040
 (Logic.eq_refl _)(Logic.eq_refl _)store_width_initial_safe store_width_register_present Run Env Observe)as CopyValid.
 destruct(joint_boundary_register_properties 7750 32 store_type_instruction_member)as[Safe Present].
 pose proof(staged_observed_register_copies memory inputs k committed env observed 7750
 (Logic.eq_refl _)(Logic.eq_refl _)ltac:(vm_compute;reflexivity) Present Run Env Observe)as CopyInstruction.
 unfold StagedCircuitRegisterHold.staged_register_lookup in CopyInstruction,CopyValid.
 destruct(SVM.find nil observed)as[observed_env|]eqn:ObservedEnv.
 2:{ unfold top_environment in Instruction. rewrite ObservedEnv in Instruction. discriminate. }
 unfold top_environment in Instruction |- *. rewrite ObservedEnv in Instruction |- *.
 rewrite CopyValid. rewrite CopyInstruction in Instruction.
 pose proof(store_active_width_run memory inputs k committed Run Legal)as Invariant.
 unfold top_environment in Invariant. rewrite Env in Invariant.
 exact(Invariant instruction lane Instruction Lane Store).
Qed.
