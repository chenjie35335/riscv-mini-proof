Require Import ReferenceBankCycleHistory ReferenceBankCycleCuts RFReferenceWriteEffect ReferenceBankCycleStability CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition ref_bank_target_indices := [::158%nat;437%nat;431%nat;427%nat;424%nat;421%nat;418%nat;414%nat;410%nat;404%nat;403%nat;400%nat;395%nat;388%nat;383%nat;379%nat;375%nat;371%nat;366%nat;361%nat;356%nat;349%nat;346%nat;343%nat;322%nat;301%nat;283%nat;265%nat;247%nat;242%nat;234%nat;224%nat;219%nat;195%nat;187%nat;166%nat;157%nat].
Definition ref_bank_target_index stage :=nth 0%nat ref_bank_target_indices stage.
Definition ref_bank_target_node stage :=if Nat.eqb stage 36 then 3221 else rf_reference_write_data stage.
Lemma ref_bank_target_certificate stage :(stage<37)%coq_nat ->
 (ref_bank_target_index stage<438)%coq_nat /\ref_bank_cycle_node(ref_bank_target_index stage)=ref_bank_target_node stage /\(ref_bank_cycle_rank(ref_bank_target_index stage)<=44)%coq_nat.
Proof. intro Bound. do 37(destruct stage as[|stage];[vm_compute;repeat split;try reflexivity;lia|]);lia. Qed.
(* Shared target facts. *)
Theorem ref_bank_target_history inputs path history limit bit raw :size raw=32%nat ->
 VM.find 9222(history 0%nat)=Some(Gval(Fuint 32)raw) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall stage,(stage<37)%coq_nat ->
 (forall t,(244<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find(ref_bank_target_node stage)(history t)=Some value /\type_of_val value=Gtyp ground) /\
 (forall t u,(244<=t)%coq_nat ->(244<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find(ref_bank_target_node stage)(history t)=VM.find(ref_bank_target_node stage)(history u)).
Proof.
 intros Size Initial Resets Steps stage Stage.
 pose proof(ref_bank_cycle_cut_facts inputs path history limit bit raw Size Initial Resets Steps)as Cuts.
 destruct(ref_bank_target_certificate stage Stage)as[Inside[Node Rank]].
 destruct(ref_bank_cycle_history inputs path history limit 200 Steps
 (fun node t Member Lower Upper=>proj1(Cuts node Member)t Lower Upper)
 (fun node t u Member Lower Other Upper OtherUpper=>proj2(Cuts node Member)t u Lower Other Upper OtherUpper)
 (ref_bank_target_index stage)Inside)as[Ground Stable].
 rewrite Node in Ground,Stable. split.
 - intros t Lower Upper. apply Ground;lia.
 - intros t u Lower Other Upper OtherUpper. apply Stable;lia.
Qed.
Require Import ReferenceControlRegisters FormalLocalHistory ObservedJointRegisterConcrete JointBoundaryRegisters RFWritebackSelection ReferenceControlStabilityHistory.
Theorem ref_bank_target_observed_history memory inputs k observed history reset :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 history 9259%nat=top_environment observed ->
 (forall t,(t<9259)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=9259)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 forall stage time,(stage<37)%coq_nat ->(244<=time)%coq_nat ->(time<=9259)%coq_nat ->
 VM.find(ref_bank_target_node stage)(history time)=VM.find(ref_bank_target_node stage)(top_environment observed).
Proof.
 intros Observe Legal Last Steps Resets stage time Stage Lower Upper.
 assert(Member:List.In(9222%nat,32%nat)joint_boundary_registers).
 { apply(List.nth_error_In joint_boundary_registers 69%nat);vm_compute;reflexivity. }
 destruct(observed_joint_register_concrete memory inputs k observed 9222%nat 32%nat Observe Legal Member)as[raw[Size Value]].
 assert(Initial:VM.find 9222(history 0%nat)=Some(Gval(Fuint 32)raw)).
 { rewrite<-(reference_control_register_history_same _ history 9259 9222 rf_load_raw_register Steps 9259%nat ltac:(lia)). rewrite Last. exact Value. }
 pose proof(proj2(ref_bank_target_history (generated_observation_input inputs k)nil history 9259 reset raw Size Initial Resets Steps stage Stage))as Stable.
 rewrite<-(Last). apply Stable;lia.
Qed.
