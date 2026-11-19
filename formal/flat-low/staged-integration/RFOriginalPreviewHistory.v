Require Import RFReferenceNopCycle.
Require Import FormalInstructionResetConstants.
Require Import RFReferenceWriteEffect ReferenceBankGuardedCommit RFReferenceNopObservedOutputs ReferenceBankGuardedObserved
 RFReferenceNopHistory RFReferenceNopIngress RFWriteEffect RFArchitecturalRelation ReferenceControlRegisters ReferenceBankCycleTargets
 ReferenceBankSelectedData ReferenceBankCycleInputs ReferenceBankCycleControls RFReferenceSelectedCommit RFReferenceWriteEffect
 DUTBankCycleHistory RFPreviewEffect RFDutOutputWires FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem rf_reference_guarded_effect_preview_history invalid history (limit start:nat) index rd bank guards permissions words active :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->
 (forall stage t,(stage<36)%coq_nat ->guards stage=true ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->guards stage=true ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 112<=time)%coq_nat ->(time<=limit)%coq_nat ->
 let word:=rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index in
 size word=32%nat /\VM.find(N.of_nat(Nat.add 1597 index))(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lower Upper Rd Start Bank Data Guards Permissions Active Steps time Ready Within.
 assert(Initial:forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(N.of_nat(2177-index)%nat)(history t)=Some value /\rf_reference_low_word(bank index)value).
 { intros t L U. destruct t as[|[|t]];try lia.
   destruct(rf_reference_bank_history_hold invalid history limit bank Bank Steps t ltac:(lia) index Upper)as[Size Value].
   exists(Gval(Fuint 32)(bank index)). split.
   - exact(rf_reference_old_word_ingress index invalid(history t)(history(S t))(history(S(S t)))(bank index)Upper Size Value(Steps t ltac:(lia))(Steps(S t)ltac:(lia))).
   - exists 32%nat,(bank index). repeat split;try assumption;try reflexivity. rewrite -Size take_size. reflexivity. }
 destruct time as[|[|[|[|time]]]];try lia.
 destruct(rf_reference_guarded_effect_history invalid history limit start index rd(bank index)guards permissions words Lower Upper Rd Initial Data Guards Permissions Steps 36 time ltac:(lia) ltac:(change(Nat.add start 108<=time)%coq_nat;lia) ltac:(lia))as[value[Value Low]].
 destruct(Initial time ltac:(lia) ltac:(lia))as[prior[Prior PLow]].
 assert(Choice:(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index).
 { destruct active;[exact(rf_reference_fold_effect guards permissions words(to_nat rd)index bank 36 Lower)|].
   unfold rf_apply_effect. assert(Zero:(index==0%nat)=false)by(apply/eqP;lia). rewrite Zero. reflexivity. }
 assert(Size:size(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=32%nat).
 { destruct active;[exact(rf_reference_low_word_size _ _ Low)|exact(rf_reference_low_word_size _ _ PLow)]. }
 pose proof(rf_reference_effect_exit index invalid(history time)(history(S time))(history(S(S time)))(history(S(S(S time))))active value prior _ _ Lower Upper (Active time ltac:(lia) ltac:(lia)) Value Low Prior PLow (Steps time ltac:(lia))(Steps(S time)ltac:(lia))(Steps(S(S time))ltac:(lia)))as Port.
 rewrite Choice in Size,Port. split;[exact Size|].
 exact(rf_reference_output_step index invalid(history(S(S(S time))))(history(S(S(S time))))(history(S(S(S(S time)))))_ Upper Size Port(Steps(S(S(S time)))ltac:(lia))).
Qed.
Theorem reference_original_preview_history memory inputs k observed bank history index :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 history 9259%nat=top_environment observed ->
 (forall t,(t<9259)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=9259)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::false])) ->
 rf_reference_bank_at(top_environment observed)bank ->
 ref_bank_guarded_controls(top_environment observed) ->ref_write_selected_data_concrete(top_environment observed) ->
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed))) ->
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 VM.find(N.of_nat(Nat.add 1597 index))(history 9258%nat)=Some(Gval(Fuint 32)(rf_apply_effect bank(ref_write_effect(top_environment observed))index)).
Proof.
 intros Observe Legal Last Steps Resets Bank Controls Data Destination LowerIndex UpperIndex.
 assert(InitialBank:rf_reference_bank_at(history 0%nat)bank).
 { intros lane Bound. destruct(Bank lane Bound)as[Size Value]. split;[exact Size|].
   destruct(rf_architectural_register_properties _ (rf_reference_register_member lane Bound))as[Present Rest].
   rewrite<-(reference_control_register_history_same _ history 9259 _ Present Steps 9259%nat ltac:(lia)).
   rewrite Last. exact Value. }
 assert(Target:forall stage t,(stage<37)%coq_nat ->(244<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find(ref_bank_target_node stage)(history t)=VM.find(ref_bank_target_node stage)(top_environment observed)).
 { exact(ref_bank_target_observed_history memory inputs k observed history false Observe Legal Last Steps Resets). }
 assert(Control:forall node t,List.In node ref_bank_control_nodes ->(244<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=VM.find node(top_environment observed)).
 { intros node t Member Lower Upper.
   rewrite(ref_bank_controls_stable (generated_observation_input inputs k)nil history 9259 false Resets Steps node Member t 9259 ltac:(lia)ltac:(lia)Upper ltac:(lia)).
   rewrite Last. reflexivity. }
 unfold ref_write_effect.
 eapply proj2. eapply(rf_reference_guarded_effect_preview_history _ history 9259 244 index(ref_write_destination(top_environment observed))bank
 (ref_write_guard(top_environment observed))(ref_write_permission(top_environment observed))(ref_write_word(top_environment observed))(ref_write_bit(top_environment observed)1707)
 LowerIndex UpperIndex).

 - intros t Lower Upper. change(VM.find(ref_bank_target_node 36)(history t)=Some(Gval(Fuint 5)(ref_write_destination(top_environment observed)))).
   rewrite(Target 36%nat t ltac:(lia)Lower Upper). exact Destination.
 - lia.
 - exact InitialBank.
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
 - vm_compute;lia.
Qed.

Theorem rf_reference_nop_original_outputs invalid history bank :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1597 index)) (history 9258%nat) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Instruction Steps Resets Bubble index Index.
 destruct (Bank index Index) as [Size _].
 eapply (rf_reference_output_step index invalid (history 9257%nat) (history 9257%nat) (history 9258%nat) (bank index));
 [exact Index|exact Size| |apply Steps;vm_compute;lia].
 eapply (rf_reference_nop_from_writeback_sources invalid history 9259 12 bank Bank Zero Instruction
 (rf_reference_nop_checker_enabled invalid history Steps Resets Bubble) Steps 9257 ltac:(vm_compute;lia));exact Index.
Qed.
