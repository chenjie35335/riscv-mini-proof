Require Import StoreRequestDataConnection.
Require Import StoreShiftNode CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Lemma store_request_data_port_exact invalid old current result width word :
 (32 <= width)%coq_nat -> size word = width ->
 VM.find 7837 old = Some (Gval (Fuint width) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 79 result = Some (Gval (Fuint 32) (take 32 word)).
Proof.
 intros Bound Size Source Step.
 assert (BoundB : (31 < width)%nat). { apply/ltP. lia. }
 assert (LowSize : size (take 32 word) = 32%nat).
 { rewrite size_take Size. have B : (32 < width)%nat \/ width = 32%nat.
   { destruct (Nat.eq_dec width 32) as [E|E]; [right;exact E|left;apply/ltP;lia]. }
   destruct B as [B| ->]; [rewrite B|]; reflexivity. }
 apply (store_request_data_connection_79 invalid old current result (Gval (Fuint 32) (take 32 word)) _).
 - cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
   cbn [eval_unop]. rewrite BoundB leq0n. cbn [andb]. rewrite subn0 drop0. reflexivity.
 - change (Some (Gval (Fuint 32) (zext_to 32 (take 32 (take 32 word)))) = Some (Gval (Fuint 32) (take 32 word))).
   rewrite take_take; try reflexivity. unfold zext_to,zext. rewrite LowSize subnn cats0. reflexivity.
 - exact Step.
Qed.
Require Import StoreShiftSemantics.
Definition store_request_word word offset := take 32(zext_to 63(zeros(to_nat offset)++word)).
Theorem store_request_data_two_steps invalid s0 s1 s2 word offset :
 size word=32%nat ->size offset=5%nat ->
 VM.find 7819 s0=Some(Gval(Fuint 32)word) ->VM.find 7831 s0=Some(Gval(Fuint 5)offset) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 79 s2=Some(Gval(Fuint 32)(store_request_word word offset)).
Proof.
 intros WordSize OffsetSize Word Offset First Second.
 exact(store_request_data_port_exact invalid s1 s1 s2 63 _ ltac:(lia)
 (store_shift_result_size word offset WordSize OffsetSize)
 (store_shift_value invalid s0 s0 s1 word offset Word Offset First)Second).
Qed.
Lemma store_request_word_size word offset :size word=32%nat ->size offset=5%nat ->size(store_request_word word offset)=32%nat.
Proof. intros Word Offset. unfold store_request_word. rewrite size_take(store_shift_result_size word offset Word Offset). reflexivity. Qed.

Definition store_request_word8 word offset := take 32(zext_to 287(zeros(to_nat offset)++word)).
Theorem store_request_data_two_steps8 invalid s0 s1 s2 word offset :
 size word=32%nat ->size offset=8%nat ->
 VM.find 7819 s0=Some(Gval(Fuint 32)word) ->VM.find 7831 s0=Some(Gval(Fuint 8)offset) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find 79 s2=Some(Gval(Fuint 32)(store_request_word8 word offset)).
Proof.
 intros WordSize OffsetSize Word Offset First Second.
 exact(store_request_data_port_exact invalid s1 s1 s2 287 _ ltac:(lia)
 (store_shift_result_size8 word offset WordSize OffsetSize)
 (store_shift_value_width invalid s0 s0 s1 word offset 8 Word Offset First)Second).
Qed.
Lemma store_request_word8_size word offset :size word=32%nat ->size offset=8%nat ->size(store_request_word8 word offset)=32%nat.
Proof. intros Word Offset. unfold store_request_word8. rewrite size_take(store_shift_result_size8 word offset Word Offset). reflexivity. Qed.
Require Import RFReferenceWriteEffect.
Lemma store_request_word8_low word offset :size word=32%nat ->
 store_request_word8 word offset=take 32(zeros(to_nat offset)++word).
Proof.
 intro Size. unfold store_request_word8,zext_to.
 apply rf_reference_take_extension. rewrite size_cat size_zeros Size. apply/leP. change (32 <= Nat.add (to_nat offset) 32)%coq_nat. lia.
Qed.
