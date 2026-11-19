Require Import StoreWriteGateHistory StoreWriteValidRegister ObservedLegalNoTrap ExceptionSourceNoTrap
 CoreSocModel ComparisonNodes FormalLocalHistory ObservedJointRegisterConcrete
 JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_write_valid_false_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 8028(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1478(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset Valid.
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
 rewrite <-Last.
 eapply(store_write_valid_false_no_exception_history _ history 9259 41 Steps ValidHistory).
 - exact(exception_source_false_after_settling (generated_observation_input inputs k) nil history Boundary Steps NoTrap).
 - vm_compute;lia.
 - vm_compute;lia.
Qed.
