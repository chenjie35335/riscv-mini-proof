Require Import StoreCycleDataAgreement StoreCycleState StoreStateObserved MemoryPendingInvariant.
Require Import RFWriteEffect MemoryForwardedCycleStep RFAluWritebackObserved RFReadPorts LoadTypeCorrespondence StoreTypeCorrespondence ObservedJointRegisterConcrete.
Require Import FormalObservationCommit ComparisonNodes PCRelativeAddressCycle CycleView MemoryCycleStep ReferenceLoadSemantics DUTRedirectReachability ReferenceRedirectSemantics FormalInstructionResetBase FormalInstructionResetCycle FormalInstructionResetConstants FormalLocalHistory ReferenceBankObservation JointBoundaryRegisters JointBoundaryReachable FormalFetchType CoreSocModel.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition cycle_store_pending env v : Prop := forall lane,
 (lane<3)%coq_nat ->store_type_is_store(cv_commit_instruction v)lane ->cycle_store_state env v lane.
Lemma cycle_store_pending_nop env v :cv_commit_instruction v=instruction_nop ->cycle_store_pending env v.
Proof. intros Nop lane Lane Match. rewrite Nop in Match. exfalso;exact(store_type_nop_not_store lane Lane Match). Qed.
Theorem cycle_store_pending_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_store_pending(top_environment observed)v.
Proof.
 intros Observe View. pose proof Observe as Prepare.
 unfold generated_observe,generated_observe_cycle in Prepare.
 destruct(generated_run memory inputs 0)as[committed|]eqn:Run;[|discriminate].
 destruct(instruction_run_zero memory inputs committed Run)as[env[Env[Front Nop]]].
 pose proof(joint_register_run_observed memory inputs 0 committed observed 7750 32 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity)Run Observe)as Copy.
 assert(Value:VM.find 7750(top_environment committed)=Some(Gval(Fuint 32)instruction_nop))by(unfold top_environment;rewrite Env;exact Nop).
 rewrite Value(cva_commit_instruction _ _ View)in Copy.
 apply cycle_store_pending_nop. exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_store_pending_reset memory inputs k current next after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment next)after ->cycle_store_pending(top_environment next)after.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset After.
 pose proof Run as Cycle. rewrite generated_run_successor in Cycle.
 destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Cycle].
 destruct(fetch9220_run_type memory inputs k previous Previous)as[old[value[Old Rest]]].
 destruct(joint_boundary_reachable memory inputs k previous Previous Legal)as[Registers Storage].
 unfold top_environment in Registers;rewrite Old in Registers.
 destruct(Registers 7748%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[front[FrontSize Front]].
 destruct(Registers 7750%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity))as[instruction[Size Instruction]].
 destruct(instruction_real_reset_cycle (generated_observation_input inputs k)previous old committed(Gval(Fuint 32)front)(Gval(Fuint 32)instruction)Old Front(Logic.eq_refl _)Instruction(Logic.eq_refl _)Reset Cycle)as[env[Env[FrontNop Nop]]].
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7750 32 ltac:(apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 assert(Value:VM.find 7750(top_environment committed)=Some(Gval(Fuint 32)instruction_nop))by(unfold top_environment;rewrite Env;exact Nop).
 rewrite Value(cva_commit_instruction _ _ After)in Copy.
 apply cycle_store_pending_nop. exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_store_pending_normal memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cycle_banks_agree before ->cycle_reference_effect_step before after ->cycle_store_pending(top_environment next)after.
Proof.
 intros Transition Reset Before After Banks Effect lane Lane Match.
 pose proof(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)as Commit.
 rewrite Commit in Match.
 destruct Transition as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 pose proof(store_cycle_state_update memory inputs k current committed(cv_front_instruction before)lane(cv_left before)(cv_right before)
 Observe Legal Run Reset Lane(cva_front_instruction _ _ Before)Match(cva_left _ _ Before)(cva_right _ _ Before))as Updated.
 pose proof(store_state_observed memory inputs(S k)committed next lane(cv_left before)(cv_right before)(cv_front_instruction before)Run NextObserve Updated)as State.
 assert(Size:size(cv_front_instruction before)=32%nat).
 { destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal
   ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[word[Size Value]].
   rewrite(cva_front_instruction _ _ Before)in Value. inversion Value;subst word;exact Size. }
 assert(Bound:forall second,(to_nat(rf_instruction_address second(cv_front_instruction before))<32)%coq_nat).
 { intro second. pose proof(to_nat_bounded(rf_instruction_address second(cv_front_instruction before)))as H.
   rewrite(rf_instruction_address_size second _ Size)in H. exact(elimT ltP H). }
 unfold cycle_store_state. rewrite Commit.
 rewrite(Effect _ (Bound false))(Effect _ (Bound true)).
 rewrite <-(cycle_forwarded_read memory inputs k current before false Observe Legal Before Banks).
 rewrite <-(cycle_forwarded_read memory inputs k current before true Observe Legal Before Banks).
 exact State.
Qed.
