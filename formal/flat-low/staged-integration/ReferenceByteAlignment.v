Require Import CoreSocModel ComparisonNodes ReferenceBooleanShape ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates2 NormalizedBit.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_byte_alignment_history lane invalid history limit :
 (lane < 3)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if Nat.eqb lane 0 then 2634 else if Nat.eqb lane 1 then 2736 else 2679) (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 2]).
Proof.
 intros Lane Steps.
 destruct lane as [|lane].
 {
 assert (C2566 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2566 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2566 reference_control_expr_2566);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2566| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2566 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (C2625 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2625 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2625 reference_control_expr_2625);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2625| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2625 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (C2628 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2628 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2628 reference_control_expr_2628);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2628| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2628 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (N2624 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2624 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2624 2623 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2624 (Steps t ltac:(lia))). }
 assert (N2627 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2627 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2627 2626 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2627 (Steps t ltac:(lia))). }
 assert (N2630 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2630 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2630 2629 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2630 (Steps t ltac:(lia))). }
 assert (M2631 : forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2631 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2630 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2631 reference_control_expr_2631);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2631| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2631 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2628 t ltac:(lia) ltac:(lia)). cbn.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 assert (M2632 : forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2632 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2627 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2632 reference_control_expr_2632);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2632| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2632 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2625 t ltac:(lia) ltac:(lia)). cbn.
 rewrite (M2631 t ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 assert (M2633 : forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2633 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2624 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2633 reference_control_expr_2633);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2633| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2633 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2566 t ltac:(lia) ltac:(lia)). cbn.
 rewrite (M2632 t ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2634 reference_control_expr_2634);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2634| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2634 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (M2633 time ltac:(lia) ltac:(lia)). reflexivity. }
 destruct lane as [|lane].
 {
 assert (C2724 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2724 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2724 reference_control_expr_2724);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2724| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2724 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (C2727 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2727 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2727 reference_control_expr_2727);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2727| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2727 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (C2730 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2730 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2730 reference_control_expr_2730);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2730| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2730 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (N2726 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2726 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2726 2725 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2726 (Steps t ltac:(lia))). }
 assert (N2729 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2729 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2729 2728 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2729 (Steps t ltac:(lia))). }
 assert (N2732 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2732 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2732 2731 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2732 (Steps t ltac:(lia))). }
 assert (M2733 : forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2733 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2732 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2733 reference_control_expr_2733);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2733| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2733 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2730 t ltac:(lia) ltac:(lia)). cbn.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 assert (M2734 : forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2734 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2729 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2734 reference_control_expr_2734);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2734| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2734 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2727 t ltac:(lia) ltac:(lia)). cbn.
 rewrite (M2733 t ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 assert (M2735 : forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2735 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2726 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2735 reference_control_expr_2735);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2735| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2735 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2724 t ltac:(lia) ltac:(lia)). cbn.
 rewrite (M2734 t ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2736 reference_control_expr_2736);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2736| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2736 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (M2735 time ltac:(lia) ltac:(lia)). reflexivity. }
 destruct lane as [|lane].
 {
 assert (C2665 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2665 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2665 reference_control_expr_2665);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2665| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2665 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (C2671 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2671 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2671 reference_control_expr_2671);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2671| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2671 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (C2674 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2674 (history t) = Some (Gval (Fuint 1) [::false])).
 { intros [|t] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2674 reference_control_expr_2674);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2674| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2674 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert (N2670 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2670 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2670 2669 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2670 (Steps t ltac:(lia))). }
 assert (N2673 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2673 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2673 2672 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2673 (Steps t ltac:(lia))). }
 assert (N2676 : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 2676 (history t) = Some value /\ normalized_bit value).
 { intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes 2676 2675 invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_2676 (Steps t ltac:(lia))). }
 assert (M2677 : forall t, (2 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2677 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2676 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2677 reference_control_expr_2677);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2677| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2677 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2674 t ltac:(lia) ltac:(lia)). cbn.
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 assert (M2678 : forall t, (3 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2678 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2673 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2678 reference_control_expr_2678);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2678| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2678 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2671 t ltac:(lia) ltac:(lia)). cbn.
 rewrite (M2677 t ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 assert (M2679 : forall t, (4 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find 2679 (history t) = Some (Gval (Fuint 1) [::true])).
 { intros [|t] Lower Upper;try lia.
 destruct (N2670 t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
 eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes 2679 reference_control_expr_2679);
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_2679| |apply Steps;lia].
 intros site. cbn [reference_control_expr_2679 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (C2665 t ltac:(lia) ltac:(lia)). cbn.
 rewrite (M2678 t ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }
 intros time Lower Upper. exact (M2679 time ltac:(lia) Upper). }
 lia.
Qed.
Theorem reference_byte_invalid_history writing invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if writing then 2736 else 2634) (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Steps time Lower Upper. destruct writing;
 [exact (reference_byte_alignment_history 1%nat invalid history limit ltac:(lia) Steps time Lower Upper)
 |exact (reference_byte_alignment_history 0%nat invalid history limit ltac:(lia) Steps time Lower Upper)].
Qed.
(* Observed byte alignment. *)
Require Import FormalObservedHistory FormalLocalHistory.
Theorem reference_byte_invalid_observed memory inputs k observed writing :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find (if writing then 2736 else 2634) (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 rewrite <- Last. exact (reference_byte_invalid_history writing _ history 9259 Steps 9259 ltac:(vm_compute;lia) ltac:(lia)).
Qed.
Theorem reference_lb_aligned_observed memory inputs k observed :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 2679 (top_environment observed) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Observe Legal.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 rewrite <- Last. exact (reference_byte_alignment_history 2%nat _ history 9259 ltac:(lia) Steps 9259 ltac:(vm_compute;lia) ltac:(lia)).
Qed.
