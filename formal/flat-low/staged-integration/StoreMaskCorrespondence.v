Require Import StoreRequestMaskValues StoreMaskValues StoreOffsetValue StoreMaskResult ReferenceStoreData.
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Semantics_with_implicit_widths.
Definition store_expanded_request_mask lane b0 b1 :=
 let mask:=store_request_mask4 lane b0 b1 in
 store_mask_word(nth false mask 0)(nth false mask 1)(nth false mask 2)(nth false mask 3).
Definition store_aligned_lane lane b0 b1 :=
 match lane with 0=>b0=false /\b1=false |1=>b0=false |2=>True|_=>False end.
Lemma store_request_mask_pattern lane b0 b1 :
 (lane<3)%coq_nat ->store_aligned_lane lane b0 b1 ->
 store_expanded_request_mask lane b0 b1=
 zeros(to_nat(store_offset_word b0 b1))++ones(reference_store_data_width lane)++
 zeros(32-to_nat(store_offset_word b0 b1)-reference_store_data_width lane).
Proof.
 intros Lane Aligned. destruct lane as[|[|[|lane]]];try lia;
 destruct b0,b1;cbn[store_aligned_lane]in Aligned;try solve [intuition discriminate];reflexivity.
Qed.
Theorem store_instruction_masked_result lane b0 b1 word :
 (lane<3)%coq_nat ->store_aligned_lane lane b0 b1 ->size word=32%nat ->
 zext_to 32(drop(to_nat(store_offset_word b0 b1))
 (andB(take 32(zeros(to_nat(store_offset_word b0 b1))++word))
 (store_expanded_request_mask lane b0 b1)))=
 zext_to 32(take(reference_store_data_width lane)word).
Proof.
 intros Lane Aligned Size. rewrite(store_request_mask_pattern lane b0 b1 Lane Aligned).
 apply store_masked_request_result;[exact Size| |].
 - destruct b0,b1;reflexivity.
 - destruct lane as[|[|[|lane]]];try lia;
   destruct b0,b1;cbn[store_aligned_lane]in Aligned;try solve [intuition discriminate];reflexivity.
Qed.
