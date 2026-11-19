Require Import StoreShiftNode CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem store_shift_value_width invalid old current result word offset width :
 VM.find 7819 old=Some(Gval(Fuint 32)word) ->
 VM.find 7831 old=Some(Gval(Fuint width)offset) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7837 result=Some(Gval(Fuint (32+2^width).-1)(zext_to (32+2^width).-1(zeros(to_nat offset)++word))).
Proof.
 intros Word Offset Step. apply(store_shift_node_step invalid old current result _ _);[|exact Step].
 intro site. cbn[store_shift_expression eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Word Offset. reflexivity.
Qed.
Theorem store_shift_value invalid old current result word offset :
 VM.find 7819 old=Some(Gval(Fuint 32)word) ->
 VM.find 7831 old=Some(Gval(Fuint 5)offset) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7837 result=Some(Gval(Fuint 63)(zext_to 63(zeros(to_nat offset)++word))).
Proof.
 intros Word Offset Step. apply(store_shift_node_step invalid old current result (Fuint 63) _);[|exact Step].
 intro site. cbn[store_shift_expression eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Word Offset. reflexivity.
Qed.
Lemma store_shift_result_size word offset :
 size word=32%nat ->size offset=5%nat ->
 size(zext_to 63(zeros(to_nat offset)++word))=63%nat.
Proof.
 intros Word Offset. unfold zext_to. rewrite size_zext addnC subnK;[reflexivity|].
 rewrite size_cat size_zeros Word.
 pose proof(to_nat_bounded offset)as Bound. rewrite Offset in Bound.
 apply/leP. move/ltP:Bound=>Bound. change (to_nat offset < 32)%coq_nat in Bound. change (Nat.add (to_nat offset) 32 <= 63)%coq_nat. lia.
Qed.

Lemma store_shift_result_size8 word offset :
 size word=32%nat ->size offset=8%nat ->
 size(zext_to 287(zeros(to_nat offset)++word))=287%nat.
Proof.
 intros Word Offset. unfold zext_to. rewrite size_zext addnC subnK;[reflexivity|].
 rewrite size_cat size_zeros Word.
 pose proof(to_nat_bounded offset)as Bound. rewrite Offset in Bound.
 apply/leP. move/ltP:Bound=>Bound. change (to_nat offset < 256)%coq_nat in Bound. change (Nat.add (to_nat offset) 32 <= 287)%coq_nat. lia.
Qed.
