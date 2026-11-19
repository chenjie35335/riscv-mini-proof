Require Import ReadValidHistory MemoryRequestWidth LoadTypeCorrespondence ObservedLegalNoTrap ExceptionSourceNoTrap
 CoreSocModel ComparisonNodes FormalLocalHistory ObservedJointRegisterConcrete
 JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem read_valid_observed memory inputs k observed kind :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (kind<8)%coq_nat ->
 VM.find 7755(top_environment observed)=Some(Gval(Fuint 3)(from_N 3(N.of_nat kind))) ->
 VM.find 1474(top_environment observed)=Some(Gval(Fuint 1)[::memory_request_active false kind]).
Proof.
 intros Observe Legal Reset Kind Mode.
 destruct(observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as[committed[initial[history[Run[Prepare[First[Last[Steps NoTrap]]]]]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
   destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[word[Size Value]].
   exists word;split;[exact Size|].
   rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Value. }
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 7755(history t)=Some(Gval(Fuint 3)(from_N 3(N.of_nat kind)))).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7755 3 load_type_register_member Steps)as Hold.
   rewrite(Hold t Upper). rewrite <-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Mode. }
 rewrite <-Last. eapply(read_valid_history kind _ history 9259 41 Kind Steps).
 - intros t Lower Upper. exact(memory_width_decoder_history false kind _ history 9259 Kind Steps Modes t ltac:(lia)Upper).
 - exact(exception_source_false_after_settling (generated_observation_input inputs k)nil history Boundary Steps NoTrap).
 - vm_compute;lia.
 - lia.
Qed.
