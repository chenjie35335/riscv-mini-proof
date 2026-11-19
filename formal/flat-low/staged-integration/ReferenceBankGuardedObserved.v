Require Import ReferenceBankGuardedCommit RFWriteEffect ReferenceBankCycleControls ReferenceBankCycleTargets ReferenceBankSelectedData ReferenceBankCycleInputs RFReferenceSelectedCommit RFReferenceWriteEffect RFReferenceNopHistory RFArchitecturalRelation ReferenceControlRegisters ReferenceBankObservation FormalObservedHistory FormalLocalHistory PipelinePCAdjacentTransfer ReferencePCResetHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition ref_bank_guarded_controls env :Prop :=
 VM.find 1707 env=Some(Gval(Fuint 1)[::ref_write_bit env 1707]) /\
 (forall stage,(stage<36)%coq_nat ->VM.find(rf_reference_chain_guard stage)env=Some(Gval(Fuint 1)[::ref_write_guard env stage])) /\
 (forall stage,(stage<36)%coq_nat ->ref_write_guard env stage=true ->rf_reference_write_depth stage=2%nat ->VM.find(rf_reference_permission_node stage)env=Some(Gval(Fuint 1)[::ref_write_permission env stage])).
Theorem reference_bank_guarded_effect_commit memory inputs k observed bank result :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 rf_reference_bank_at(top_environment observed)bank ->bank 0%nat=nseq 32 false ->
 ref_bank_guarded_controls(top_environment observed) ->
 ref_write_selected_data_concrete(top_environment observed) ->
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))) ->
 formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(top_environment observed)true(top_environment observed)flat_statements=Some result ->
 rf_reference_bank_at result(rf_apply_effect bank(ref_write_effect(top_environment observed))).
Proof.
 intros Observe Legal Reset Bank Zero Controls Data Destination Commit.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(ResetBit:reset=false).
 { pose proof(Resets 9259%nat ltac:(lia))as Value. rewrite Last in Value.
   rewrite(adjacent_transfer_observed_reset memory inputs k observed Observe Legal Reset)in Value. congruence. }
 subst reset.
 assert(InitialBank:rf_reference_bank_at(history 0%nat)bank).
 { intros index Bound. destruct(Bank index Bound)as[Size Value]. split;[exact Size|].
   destruct(rf_architectural_register_properties _ (rf_reference_register_member index Bound))as[Present Rest].
   rewrite<-(reference_control_register_history_same _ history 9259 _ Present Steps 9259%nat ltac:(lia)).
   rewrite Last. exact Value. }
 assert(Target:forall stage t,(stage<37)%coq_nat ->(244<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find(ref_bank_target_node stage)(history t)=VM.find(ref_bank_target_node stage)(top_environment observed)).
 { exact(ref_bank_target_observed_history memory inputs k observed history false Observe Legal Last Steps Resets). }
 assert(Control:forall node t,List.In node ref_bank_control_nodes ->(244<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=VM.find node(top_environment observed)).
 { intros node t Member Lower Upper.
   rewrite(ref_bank_controls_stable (generated_observation_input inputs k)nil history 9259 false Resets Steps node Member t 9259 ltac:(lia)ltac:(lia)Upper ltac:(lia)).
   rewrite Last. reflexivity. }
 unfold ref_write_effect.
 eapply(rf_reference_guarded_bank_effect_commit _ history 9259 244 (ref_write_destination(top_environment observed))bank
 (ref_write_guard(top_environment observed))(ref_write_permission(top_environment observed))(ref_write_word(top_environment observed))(ref_write_bit(top_environment observed)1707)result).
 - intros t Lower Upper. change(VM.find(ref_bank_target_node 36)(history t)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed)))).
   rewrite(Target 36%nat t ltac:(lia)Lower Upper). exact Destination.
 - lia.
 - exact InitialBank.
 - exact Zero.
 - intros stage t Stage Selected Lower Upper.
   destruct(Data stage Stage Selected)as[value[Value Low]]. exists value;split;[|exact Low].
   pose proof(Target stage t ltac:(lia)Lower Upper)as Equal.
   unfold ref_bank_target_node in Equal. assert(Miss:Nat.eqb stage 36=false)by(apply Nat.eqb_neq;lia).
   rewrite Miss in Equal. rewrite Equal. exact Value.
 - intros stage t Stage Lower Upper. rewrite(Control _ t(ref_bank_guard_member stage Stage)Lower Upper). exact(proj1(proj2 Controls)stage Stage).
 - intros stage t Stage Selected Depth Lower Upper. rewrite(Control _ t(ref_bank_permission_member stage Stage Depth)Lower Upper). exact(proj2(proj2 Controls)stage Stage Selected Depth).
 - intros t Lower Upper. rewrite(Control 1707 t ltac:(unfold ref_bank_control_nodes;vm_compute;tauto)Lower Upper). exact(proj1 Controls).
 - exact Steps.
 - vm_compute;lia.
 - exact(reference_pc_reset_after_four _ (history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)false (Resets 9255%nat ltac:(vm_compute;lia))(Steps 9255%nat ltac:(vm_compute;lia))(Steps 9256%nat ltac:(vm_compute;lia))(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))).
 - rewrite Last. exact Commit.
Qed.
Theorem reference_bank_guarded_effect_next memory inputs k observed committed next bank :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some committed ->generated_observe memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 rf_reference_bank_at(top_environment observed)bank ->bank 0%nat=nseq 32 false ->
 ref_bank_guarded_controls(top_environment observed) ->ref_write_selected_data_concrete(top_environment observed) ->
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))) ->
 rf_reference_bank_at(top_environment next)(rf_apply_effect bank(ref_write_effect(top_environment observed))).
Proof.
 intros Observe Legal Run Next Reset Bank Zero Controls Data Destination.
 apply(reference_bank_next_observed memory inputs k observed committed next _ Observe Run Next).
 intros result Commit. exact(reference_bank_guarded_effect_commit memory inputs k observed bank result Observe Legal Reset Bank Zero Controls Data Destination Commit).
Qed.
