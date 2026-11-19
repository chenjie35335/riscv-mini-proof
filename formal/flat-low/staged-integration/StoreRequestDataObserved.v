Require Import CoreSocModel ComparisonNodes StoreOffsetValue StoreRequestDataValue
 FormalObservedHistory FormalLocalHistory ALUInputStability EarlyControlStabilityHistory
 ObservedRFPortsConcrete ObservedJointRegisterConcrete JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem store_request_data_observed memory inputs k observed b0 b1 tail word :
 generated_observe memory inputs k=Some observed ->
 generated_legal_trace memory inputs k ->
 VM.find 1155(top_environment observed)=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)word) ->
 VM.find 79(top_environment observed)=Some(Gval(Fuint 32)
   (take 32(zeros(to_nat(store_offset_word b0 b1))++word))).
Proof.
 intros Observe Legal Address Word.
 destruct(proj1(proj2(observed_rf_ports_concrete memory inputs k observed Observe Legal)))as[actual[Size Actual]].
 rewrite Word in Actual. inversion Actual;subst actual.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Boundary:forall node width,List.In(node,width)joint_boundary_registers ->
   map_uint_concrete(N.of_nat node)width(history 0%nat)).
 { intros node width Member.
   destruct(observed_joint_register_concrete memory inputs k observed node width Observe Legal Member)as[bits[BitsSize Value]].
   exists bits. split;[exact BitsSize|].
   rewrite <-(joint_update_register_history_same _ history 9259 node width Member Steps 9259 ltac:(vm_compute;lia)).
   rewrite Last. exact Value. }
 assert(AddressEarlier:VM.find 1155(history 9254%nat)=Some(Gval(Fuint 32)(b0::b1::tail))).
 { apply(alu_stable_value_at (generated_observation_input inputs k)nil history 1155%nat _ 9254 Boundary Steps).
   - unfold alu_stability_targets. do 3 right. left;reflexivity.
   - vm_compute;lia.
   - vm_compute;lia.
   - rewrite Last. exact Address. }
 assert(WordEarlier:VM.find 7819(history 9257%nat)=Some(Gval(Fuint 32)word)).
 { rewrite(early_control_stable_7819_history (generated_observation_input inputs k)nil history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)).
   rewrite Last. exact Word. }
 pose proof(store_offset_three_steps _ (history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)
   b0 b1 tail AddressEarlier (Steps 9254%nat ltac:(vm_compute;lia))(Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia)))as Offset.
 pose proof(store_request_data_two_steps8 _ (history 9257%nat)(history 9258%nat)(history 9259%nat)
   word(store_offset_word b0 b1)Size(Logic.eq_refl _)WordEarlier Offset
   (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia)))as Result.
 rewrite Last (store_request_word8_low word(store_offset_word b0 b1)Size)in Result.
 exact Result.
Qed.
