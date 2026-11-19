Require Import RFReferenceSelectedWrite RFEffectState RFReferenceWriteEffect RFArchitecturalWriteEffect RFReferenceNopHistory RFReferenceNopIngress RFReferenceNopEntry RFReferenceNopStorageCertificates RFWriteEffect CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_reference_selected_effect_sized guards permissions words destination count :
 (forall stage,(stage<count)%coq_nat ->guards stage=true ->size(words stage)=32%nat) ->
 rf_effect_sized(rf_reference_effect guards permissions words destination count).
Proof.
 intro Words. induction count as[|count IH];[exact I|].
 cbn [rf_reference_effect]. destruct(guards count)eqn:Guard;cbn.
 - destruct(rf_reference_permission_value count(permissions count));cbn.
   + apply Words;[lia|exact Guard].
   + apply IH. intros stage Bound Selected. apply Words;[lia|exact Selected].
 - apply IH. intros stage Bound Selected. apply Words;[lia|exact Selected].
Qed.
Theorem rf_reference_selected_nonzero_effect_commit invalid history (limit start:nat) index rd bank guards permissions words active result :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->
 (forall stage t,(stage<36)%coq_nat ->guards stage=true ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (Nat.add start 111<=limit)%coq_nat ->VM.find 1515(history limit)=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories(history limit)true(history limit)flat_statements=Some result ->
 VM.find(N.of_nat(7299+index)%nat)result=Some(Gval(Fuint 32)
 (rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index)).
Proof.
 intros Lower Upper Rd Start Bank Data Guards Permissions Active Steps Ready Reset Commit.
 assert(Initial:forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(N.of_nat(2177-index)%nat)(history t)=Some value /\rf_reference_low_word(bank index)value).
 { intros t L U. destruct t as[|[|t]];try lia.
   destruct(rf_reference_bank_history_hold invalid history limit bank Bank Steps t ltac:(lia) index Upper)as[Size Value].
   exists(Gval(Fuint 32)(bank index)). split.
   - exact(rf_reference_old_word_ingress index invalid(history t)(history(S t))(history(S(S t)))(bank index)Upper Size Value(Steps t ltac:(lia))(Steps(S t)ltac:(lia))).
   - exists 32%nat,(bank index). repeat split;try assumption;try reflexivity. rewrite -Size take_size. reflexivity. }
 destruct limit as[|[|[|time]]];try lia.
 destruct(rf_reference_selected_effect_history invalid history(S(S(S time)))start index rd(bank index)guards permissions words Lower Upper Rd Initial Data Guards Permissions Steps 36 time ltac:(lia) ltac:(change(Nat.add start 108<=time)%coq_nat;lia) ltac:(lia))as[value[Value Low]].
 destruct(Initial time ltac:(lia) ltac:(lia))as[prior[Prior PLow]].
 assert(Choice:(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index).
 { destruct active;[exact(rf_reference_fold_effect guards permissions words(to_nat rd)index bank 36 Lower)|].
   unfold rf_apply_effect. assert(Zero:(index==0%nat)=false)by(apply/eqP;lia). rewrite Zero. reflexivity. }
 assert(Size:size(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=32%nat).
 { destruct active;[exact(rf_reference_low_word_size _ _ Low)|exact(rf_reference_low_word_size _ _ PLow)]. }
 pose proof(rf_reference_effect_exit index invalid(history time)(history(S time))(history(S(S time)))(history(S(S(S time))))active value prior _ _ Lower Upper (Active time ltac:(lia) ltac:(lia)) Value Low Prior PLow (Steps time ltac:(lia))(Steps(S time)ltac:(lia))(Steps(S(S time))ltac:(lia)))as Port.
 rewrite Choice in Size,Port.
 pose proof(rf_reference_bank_history_hold invalid history(S(S(S time)))bank Bank Steps(S(S(S time)))ltac:(lia))as FinalBank.
 eapply rf_reference_normal_commit_value;[exact Upper|exact(proj2(FinalBank index Upper))|reflexivity|exact Reset|exact Port|exact Size|exact Commit].
Qed.
Theorem rf_reference_selected_bank_effect_commit invalid history (limit start:nat) rd bank guards permissions words active result :
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->bank 0%nat=nseq 32 false ->
 (forall stage t,(stage<36)%coq_nat ->guards stage=true ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (Nat.add start 111<=limit)%coq_nat ->VM.find 1515(history limit)=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories(history limit)true(history limit)flat_statements=Some result ->
 rf_reference_bank_at result(rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)).
Proof.
 intros Rd Start Bank Zero Data Guards Permissions Active Steps Ready Reset Commit index Index.
 split.
 - apply rf_apply_effect_size;[exact(proj1(Bank index Index))|].
 destruct active;[|exact I]. apply rf_reference_selected_effect_sized. intros stage Stage Selected.
 destruct(Data stage start Stage Selected ltac:(lia)ltac:(lia))as[value[Value Low]]. exact(rf_reference_low_word_size _ _ Low).
 - destruct index as[|index].
 + change(VM.find 7299 result=Some(Gval(Fuint 32)(nseq 32 false))).
 destruct(rf_reference_bank_history_hold invalid history limit bank Bank Steps limit ltac:(lia)0%nat ltac:(lia))as[Size Old].
 eapply(rf_reference_normal_commit_value invalid(history limit)(history limit)result 0(Gval(Fuint 32)(bank 0%nat))(nseq 32 false));[lia|exact Old|reflexivity|exact Reset| |reflexivity|exact Commit].
 exact(rf_reference_x0_source_history invalid history limit start bank active Bank Zero Start Active Steps limit ltac:(lia)ltac:(lia)).
 + exact(rf_reference_selected_nonzero_effect_commit invalid history limit start(S index)rd bank guards permissions words active result ltac:(lia)Index Rd Start Bank Data Guards Permissions Active Steps Ready Reset Commit).
Qed.
