Require Import StoreNonStoreCycle StoreWriteValidReset StoreWriteValidResetBase StoreWriteValidReachableType StoreWriteValidInitialization
 ObservedInstructionNormalTransfer StoreTypeCorrespondence CoreSocModel FormalLocalHistory FormalObservationCommit
 JointBoundaryInduction ExternalReset StagedObservedRegister FormalFetchType RegisterInvariants JointBoundaryRegisters.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition store_nonstore_write_valid_invariant env := forall instruction,
 VM.find 7750 env=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 VM.find 8028 env=Some(Gval(Fuint 1)[::false]).
Theorem store_nonstore_write_valid_run memory inputs k states :
 generated_run memory inputs k=Some states ->generated_legal_trace memory inputs k ->
 store_nonstore_write_valid_invariant(top_environment states).
Proof.
 destruct k as[|k];intros Run Legal instruction Instruction NonStore.
 - exact(store_write_valid_run_zero memory inputs states Run).
 - assert(PriorLegal:generated_legal_trace memory inputs k).
   { apply(joint_legal_trace_prefix memory inputs(S k)k Legal);lia. }
   destruct(generated_successful_commit memory inputs k states Run)as[observed[Observe Commit]].
   destruct(legal_observation_reset memory inputs k PriorLegal)as[reset Reset].
   destruct reset.
   + exact(store_write_valid_reset_cycle memory inputs k observed states Observe PriorLegal Run Reset).
   + pose proof(observed_instruction_normal_equal memory inputs k observed states Observe PriorLegal Run Reset)as Transfer.
     rewrite Transfer in Instruction.
     exact(store_nonstore_write_valid_cycle memory inputs k observed states instruction Observe PriorLegal Run Reset Instruction NonStore).
Qed.
Theorem store_nonstore_write_valid_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 VM.find 8028(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Instruction NonStore.
 pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct(generated_run memory inputs k)as[committed|]eqn:Run;[|discriminate].
 destruct(fetch9220_run_type memory inputs k committed Run)as[env[value[Env Rest]]].
 pose proof(staged_observed_register_copies memory inputs k committed env observed 8028
 (Logic.eq_refl _)(Logic.eq_refl _)store_write_valid_initial_safe store_write_valid_register_present Run Env Observe)as CopyValid.
 destruct(joint_boundary_register_properties 7750 32 store_type_instruction_member)as[Safe Present].
 pose proof(staged_observed_register_copies memory inputs k committed env observed 7750
 (Logic.eq_refl _)(Logic.eq_refl _)ltac:(vm_compute;reflexivity) Present Run Env Observe)as CopyInstruction.
 unfold StagedCircuitRegisterHold.staged_register_lookup in CopyInstruction,CopyValid.
 destruct(SVM.find nil observed)as[observed_env|]eqn:ObservedEnv.
 2:{ unfold top_environment in Instruction. rewrite ObservedEnv in Instruction. discriminate. }
 unfold top_environment in Instruction |- *. rewrite ObservedEnv in Instruction |- *.
 rewrite CopyValid. rewrite CopyInstruction in Instruction.
 pose proof(store_nonstore_write_valid_run memory inputs k committed Run Legal)as Invariant.
 unfold top_environment in Invariant. rewrite Env in Invariant.
 exact(Invariant instruction Instruction NonStore).
Qed.
Require Import StoreWriteValidObserved.
Theorem store_nonstore_write_port_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 VM.find 1478(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset Instruction NonStore.
 apply(store_write_valid_false_observed memory inputs k observed Observe Legal Reset).
 exact(store_nonstore_write_valid_observed memory inputs k observed instruction Observe Legal Instruction NonStore).
Qed.
