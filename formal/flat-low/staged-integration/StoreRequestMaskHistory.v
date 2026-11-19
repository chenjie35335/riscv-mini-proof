Require Import StoreRequestMaskValues StoreRequestMaskConnection StoreTypeCorrespondence CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Lemma store_request_mask_port invalid old current result lane b0 b1 :
 (lane<3)%coq_nat ->
 VM.find 7848 old=Some(Gval(Fuint 5)(store_request_mask5 lane b0 b1)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 80 result=Some(Gval(Fuint 4)(store_request_mask4 lane b0 b1)).
Proof.
 intros Lane Source Step.
 apply(store_request_mask_connection_80 invalid old current result (Gval(Fuint 4)(store_request_mask4 lane b0 b1)) _).
 - cbn[eval_hfexpr_with_memory eval_href_with_memory]. rewrite Source.
   do 3(destruct lane as[|lane];[destruct b0,b1;reflexivity|]);lia.
 - do 3(destruct lane as[|lane];[destruct b0,b1;reflexivity|]);lia.
 - exact Step.
Qed.
Theorem store_request_mask_history invalid history limit start lane previous b0 b1 tail :
 (lane<3)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 7765(history t)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 7754(history t)=Some(Gval(Fuint 2)previous) /\
 VM.find 91(history t)=Some(Gval(Fuint 2)(from_N 2(store_type_lane_kind lane))) /\
 VM.find 1155(history t)=Some(Gval(Fuint 32)(b0::b1::tail))) ->
 forall time,(Nat.add start 6<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 80(history time)=Some(Gval(Fuint 4)(store_request_mask4 lane b0 b1)).
Proof.
 intros Lane Steps Inputs.
 assert(H7838:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7838(history t)=Some(Gval(Fuint 2)(from_N 2(store_type_lane_kind lane)))).
 { intros[|t]L U;[lia|]. destruct(Inputs t ltac:(lia)ltac:(lia))as[A[B[C D]]].
 exact(store_request_mask_value_7838 invalid(history t)(history t)(history(S t))lane previous Lane A B C(Steps t ltac:(lia))). }
 assert(H7839:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7839(history t)=Some(Gval(Fuint 2)[::b0;b1])).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7839 invalid(history t)(history t)(history(S t))b0 b1 tail).
 - exact(proj2(proj2(proj2(Inputs t ltac:(lia)ltac:(lia))))).
 - apply Steps;lia. }
 assert(H7841:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7841(history t)=Some(Gval(Fuint 2)[::b0;b1])).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7841 invalid(history t)(history t)(history(S t))b0 b1 tail).
 - exact(proj2(proj2(proj2(Inputs t ltac:(lia)ltac:(lia))))).
 - apply Steps;lia. }
 assert(H7840:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7840(history t)=Some(Gval(Fuint 5)(store_request_half b0 b1))).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7840 invalid(history t)(history t)(history(S t))b0 b1).
 - apply H7839;lia.
 - apply Steps;lia. }
 assert(H7842:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7842(history t)=Some(Gval(Fuint 4)(store_request_byte b0 b1))).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7842 invalid(history t)(history t)(history(S t))b0 b1).
 - apply H7841;lia.
 - apply Steps;lia. }
 assert(H7843:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7843(history t)=Some(Gval(Fuint 1)[::Nat.eqb lane 0])).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7843 invalid(history t)(history t)(history(S t))lane).
 - exact Lane.
 - apply H7838;lia.
 - apply Steps;lia. }
 assert(H7845:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7845(history t)=Some(Gval(Fuint 1)[::Nat.eqb lane 1])).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7845 invalid(history t)(history t)(history(S t))lane).
 - exact Lane.
 - apply H7838;lia.
 - apply Steps;lia. }
 assert(H7847:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7847(history t)=Some(Gval(Fuint 1)[::Nat.eqb lane 2])).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7847 invalid(history t)(history t)(history(S t))lane).
 - exact Lane.
 - apply H7838;lia.
 - apply Steps;lia. }
 assert(H7844:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7844(history t)=Some(Gval(Fuint 4)(store_request_wordmask lane))).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7844 invalid(history t)(history t)(history(S t))lane).
 - exact Lane.
 - apply H7843;lia.
 - apply Steps;lia. }
 assert(H7846:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7846(history t)=Some(Gval(Fuint 5)(store_request_half_select lane b0 b1))).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7846 invalid(history t)(history t)(history(S t))lane b0 b1).
 - exact Lane.
 - apply H7845;lia.
 - apply H7840;lia.
 - apply H7844;lia.
 - apply Steps;lia. }
 assert(H7848:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7848(history t)=Some(Gval(Fuint 5)(store_request_mask5 lane b0 b1))).
 { intros[|t]L U;[lia|].
 apply(store_request_mask_value_7848 invalid(history t)(history t)(history(S t))lane b0 b1).
 - exact Lane.
 - apply H7847;lia.
 - apply H7842;lia.
 - apply H7846;lia.
 - apply Steps;lia. }
 intros[|time]Lower Upper;[lia|].
 apply(store_request_mask_port invalid(history time)(history time)(history(S time))lane b0 b1 Lane).
 - apply H7848;lia.
 - apply Steps;lia.
Qed.
