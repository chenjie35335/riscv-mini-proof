Require Import StoreRequestMaskNodes StoreTypeCorrespondence CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition store_request_half b0 b1 :=zext_to 5(zeros(to_nat[::b0;b1])++[::true;true]).
Definition store_request_byte b0 b1 :=zext_to 4(zeros(to_nat[::b0;b1])++[::true]).
Definition store_request_wordmask lane :=if Nat.eqb lane 0 then [::true;true;true;true]else [::false;false;false;false].
Definition store_request_half_select lane b0 b1 :=if Nat.eqb lane 1 then store_request_half b0 b1 else zext_to 5(store_request_wordmask lane).
Definition store_request_mask5 lane b0 b1 :=if Nat.eqb lane 2 then zext_to 5(store_request_byte b0 b1)else store_request_half_select lane b0 b1.
Definition store_request_mask4 lane b0 b1 :=take 4(store_request_mask5 lane b0 b1).

Theorem store_request_mask_value_7838 invalid old current result lane previous :
 (lane<3)%coq_nat ->
 VM.find 7765 old=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7754 old=Some(Gval(Fuint 2)previous) ->
 VM.find 91 old=Some(Gval(Fuint 2)(from_N 2(store_type_lane_kind lane))) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7838 result=Some(Gval(Fuint 2)(from_N 2(store_type_lane_kind lane))).
Proof.
 intros Lane H0 H1 H2 Step.
 eapply(store_request_mask_node_step 7838 store_request_mask_expr_7838 invalid old current result).
 - unfold store_request_mask_nodes. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7838 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0 H1 H2.
   unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite H1.
   do 3(destruct lane as[|lane];[reflexivity|]);lia.
 - exact Step.
Qed.

Theorem store_request_mask_value_7839 invalid old current result b0 b1 tail :
 VM.find 1155 old=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7839 result=Some(Gval(Fuint 2)[::b0;b1]).
Proof.
 intros H0 Step.
 eapply(store_request_mask_node_step 7839 store_request_mask_expr_7839 invalid old current result).
 - unfold store_request_mask_nodes. do 1 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7839 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   cbn[eval_unop]. rewrite !take_cons ?take0. reflexivity.
 - exact Step.
Qed.

Theorem store_request_mask_value_7840 invalid old current result b0 b1 :
 VM.find 7839 old=Some(Gval(Fuint 2)[::b0;b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7840 result=Some(Gval(Fuint 5)(store_request_half b0 b1)).
Proof.
 intros H0 Step.
 eapply(store_request_mask_node_step 7840 store_request_mask_expr_7840 invalid old current result).
 - unfold store_request_mask_nodes. do 2 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7840 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   destruct b0,b1;reflexivity.
 - exact Step.
Qed.

Theorem store_request_mask_value_7841 invalid old current result b0 b1 tail :
 VM.find 1155 old=Some(Gval(Fuint 32)(b0::b1::tail)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7841 result=Some(Gval(Fuint 2)[::b0;b1]).
Proof.
 intros H0 Step.
 eapply(store_request_mask_node_step 7841 store_request_mask_expr_7841 invalid old current result).
 - unfold store_request_mask_nodes. do 3 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7841 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   cbn[eval_unop]. rewrite !take_cons ?take0. reflexivity.
 - exact Step.
Qed.

Theorem store_request_mask_value_7842 invalid old current result b0 b1 :
 VM.find 7841 old=Some(Gval(Fuint 2)[::b0;b1]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7842 result=Some(Gval(Fuint 4)(store_request_byte b0 b1)).
Proof.
 intros H0 Step.
 eapply(store_request_mask_node_step 7842 store_request_mask_expr_7842 invalid old current result).
 - unfold store_request_mask_nodes. do 4 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7842 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   destruct b0,b1;reflexivity.
 - exact Step.
Qed.

Theorem store_request_mask_value_7843 invalid old current result lane :
 (lane<3)%coq_nat ->
 VM.find 7838 old=Some(Gval(Fuint 2)(from_N 2(store_type_lane_kind lane))) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7843 result=Some(Gval(Fuint 1)[::Nat.eqb lane 0]).
Proof.
 intros Lane H0 Step.
 eapply(store_request_mask_node_step 7843 store_request_mask_expr_7843 invalid old current result).
 - unfold store_request_mask_nodes. do 5 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7843 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   do 3(destruct lane as[|lane];[reflexivity|]);lia.
 - exact Step.
Qed.

Theorem store_request_mask_value_7844 invalid old current result lane :
 (lane<3)%coq_nat ->
 VM.find 7843 old=Some(Gval(Fuint 1)[::Nat.eqb lane 0]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7844 result=Some(Gval(Fuint 4)(store_request_wordmask lane)).
Proof.
 intros Lane H0 Step.
 eapply(store_request_mask_node_step 7844 store_request_mask_expr_7844 invalid old current result).
 - unfold store_request_mask_nodes. do 6 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7844 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   do 3(destruct lane as[|lane];[reflexivity|]);lia.
 - exact Step.
Qed.

Theorem store_request_mask_value_7845 invalid old current result lane :
 (lane<3)%coq_nat ->
 VM.find 7838 old=Some(Gval(Fuint 2)(from_N 2(store_type_lane_kind lane))) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7845 result=Some(Gval(Fuint 1)[::Nat.eqb lane 1]).
Proof.
 intros Lane H0 Step.
 eapply(store_request_mask_node_step 7845 store_request_mask_expr_7845 invalid old current result).
 - unfold store_request_mask_nodes. do 7 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7845 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   do 3(destruct lane as[|lane];[reflexivity|]);lia.
 - exact Step.
Qed.

Theorem store_request_mask_value_7846 invalid old current result lane b0 b1 :
 (lane<3)%coq_nat ->
 VM.find 7845 old=Some(Gval(Fuint 1)[::Nat.eqb lane 1]) ->
 VM.find 7840 old=Some(Gval(Fuint 5)(store_request_half b0 b1)) ->
 VM.find 7844 old=Some(Gval(Fuint 4)(store_request_wordmask lane)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7846 result=Some(Gval(Fuint 5)(store_request_half_select lane b0 b1)).
Proof.
 intros Lane H0 H1 H2 Step.
 eapply(store_request_mask_node_step 7846 store_request_mask_expr_7846 invalid old current result).
 - unfold store_request_mask_nodes. do 8 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7846 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0 H1 H2.
   unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite H1 H2.
   do 3(destruct lane as[|lane];[destruct b0,b1;reflexivity|]);lia.
 - exact Step.
Qed.

Theorem store_request_mask_value_7847 invalid old current result lane :
 (lane<3)%coq_nat ->
 VM.find 7838 old=Some(Gval(Fuint 2)(from_N 2(store_type_lane_kind lane))) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7847 result=Some(Gval(Fuint 1)[::Nat.eqb lane 2]).
Proof.
 intros Lane H0 Step.
 eapply(store_request_mask_node_step 7847 store_request_mask_expr_7847 invalid old current result).
 - unfold store_request_mask_nodes. do 9 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7847 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0.
   do 3(destruct lane as[|lane];[reflexivity|]);lia.
 - exact Step.
Qed.

Theorem store_request_mask_value_7848 invalid old current result lane b0 b1 :
 (lane<3)%coq_nat ->
 VM.find 7847 old=Some(Gval(Fuint 1)[::Nat.eqb lane 2]) ->
 VM.find 7842 old=Some(Gval(Fuint 4)(store_request_byte b0 b1)) ->
 VM.find 7846 old=Some(Gval(Fuint 5)(store_request_half_select lane b0 b1)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 7848 result=Some(Gval(Fuint 5)(store_request_mask5 lane b0 b1)).
Proof.
 intros Lane H0 H1 H2 Step.
 eapply(store_request_mask_node_step 7848 store_request_mask_expr_7848 invalid old current result).
 - unfold store_request_mask_nodes. do 10 right. left;reflexivity.
 - intro site. cbn[store_request_mask_expr_7848 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H0 H1 H2.
   unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite H1 H2.
   do 3(destruct lane as[|lane];[destruct b0,b1;reflexivity|]);lia.
 - exact Step.
Qed.

Lemma store_request_mask4_size lane b0 b1 :(lane<3)%coq_nat ->size(store_request_mask4 lane b0 b1)=4%nat.
Proof. intro Lane. do 3(destruct lane as[|lane];[destruct b0,b1;reflexivity|]);lia. Qed.
