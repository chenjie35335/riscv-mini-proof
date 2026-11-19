Require Import StoreNonStoreReachable ReferenceNonStoreWriteObserved MemoryRequestObservedSemantics StoreTypeCorrespondence
 StoreWriteGateHistory StoreWriteValidRegister ObservedLegalNoTrap ExceptionSourceNoTrap
 CoreSocModel ComparisonNodes FormalLocalHistory ObservedJointRegisterConcrete
 JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization FormalResetPreparation
 Assertion5NoWrite Assertion5ResetGuard CycleView.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nonstore_data_assertion_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 generated_assert_m0_5_local(top_environment observed).
Proof.
 intros Observe Legal Reset Instruction NonStore.
 pose proof(store_nonstore_write_valid_observed memory inputs k observed instruction Observe Legal Instruction NonStore)as Valid.
 destruct(memory_reference_enable_known memory inputs k observed Observe Legal Reset)as[enabled Enabled].
 destruct(reference_nonstore_decode_observed memory inputs k observed instruction enabled Observe Legal Instruction Enabled NonStore)as[SB[SH SW]].
 destruct(observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps NoTrap]]]]]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
   destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]].
   exists word;split;[exact Size|].
   rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Value. }
 assert(ValidHistory:forall t,(41<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 8028(history t)=Some(Gval(Fuint 1)[::false])).
 { intros t Lower Upper.
   rewrite(store_write_valid_register_history _ history 9259 Steps t Upper).
   rewrite <-(store_write_valid_register_history _ history 9259 Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Valid. }
 destruct(top_reset_prepared(Some committed)_ initial _ Reset Prepare)as[env[Env InitialReset]].
 assert(Reset0:VM.find 1(history 0%nat)=Some(Gval(Fuint 1)[::false])).
 { rewrite First. unfold top_environment. rewrite Env. exact InitialReset. }
 pose proof(legal_local_reset_history _ history 9259 false Steps Reset0)as Resets.
 assert(DUT:VM.find 1478(history 9258%nat)=Some(Gval(Fuint 1)[::false])).
 { eapply(store_write_valid_false_no_exception_history _ history 9259 41 Steps ValidHistory).
   - exact(exception_source_false_after_settling (generated_observation_input inputs k)nil history Boundary Steps NoTrap).
   - vm_compute;lia.
   - vm_compute;lia. }
 assert(Reference:VM.find 1523(history 9258%nat)=Some(Gval(Fuint 1)[::false])).
 { apply(reference_write_false_history_from_last (generated_observation_input inputs k)nil history false enabled Steps Resets);
   try(rewrite Last;assumption);vm_compute;lia. }
 pose proof(assertion5_reset_guard_observed memory inputs k observed false Observe Reset)as Guard.
 rewrite <-Last in Guard |- *.
 exact(assertion5_no_write_step _ (history 9258%nat)(history 9258%nat)(history 9259%nat)true DUT Reference Guard(Steps 9258%nat ltac:(vm_compute;lia))).
Qed.
