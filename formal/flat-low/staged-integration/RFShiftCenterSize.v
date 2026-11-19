Require Import RFShiftCenter.
From firrtl Require Import Semantics_with_implicit_widths.
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Lemma rf_shift_center_size arithmetic word right :size word=32%nat ->size(rf_shift_center_word arithmetic word right)=32%nat.
Proof.
 intro Size. unfold rf_shift_center_word,sext_to.
 rewrite size_take size_sext addnC subnK;[reflexivity|].
 rewrite size_drop size_cat size_andB size_drop size_take Size. cbn[size]. apply leq_subr.
Qed.
