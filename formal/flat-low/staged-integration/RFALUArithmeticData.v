Require Import FormalLocalHistory.
Require Import ObservedJointRegisterConcrete.
Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceLoadSemantics.
From Coq Require Import NArith ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_arithmetic_expr_3067 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_arithmetic_expr_3068 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3067)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_arithmetic_expr_3069 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3068))).
Definition rf_arithmetic_expr_3222 := (@Eref VarOrder.T (@Eid VarOrder.T 3069)).
Definition rf_arithmetic_expr_3496 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_arithmetic_expr_3497 := (@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_arithmetic_expr_3498 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3496)) (@Eref VarOrder.T (@Eid VarOrder.T 3497))).
Definition rf_arithmetic_expr_3499 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3498))).
Definition rf_arithmetic_expr_3500 := (@Eref VarOrder.T (@Eid VarOrder.T 3499)).
Definition rf_arithmetic_expr_3501 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_arithmetic_expr_3502 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3501))).
Definition rf_arithmetic_expr_3503 := (@Eref VarOrder.T (@Eid VarOrder.T 3502)).
Definition rf_arithmetic_expr_3504 := (@Eref VarOrder.T (@Eid VarOrder.T 2552)).
Definition rf_arithmetic_nodes := [::(3067,rf_arithmetic_expr_3067);(3068,rf_arithmetic_expr_3068);(3069,rf_arithmetic_expr_3069);(3222,rf_arithmetic_expr_3222);(3496,rf_arithmetic_expr_3496);(3497,rf_arithmetic_expr_3497);(3498,rf_arithmetic_expr_3498);(3499,rf_arithmetic_expr_3499);(3500,rf_arithmetic_expr_3500);(3501,rf_arithmetic_expr_3501);(3502,rf_arithmetic_expr_3502);(3503,rf_arithmetic_expr_3503);(3504,rf_arithmetic_expr_3504)].
Definition rf_arithmetic_offsets := [::3146%nat;0%nat;0%nat;152%nat;273%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_arithmetic_positions :select_node_offsets rf_arithmetic_offsets flat_statements=Some rf_arithmetic_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_arithmetic_safety :selected_node_safety flat_memories flat_statements rf_arithmetic_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_add_left lane :=if Nat.eqb lane 2 then 2812 else 2209.
Definition rf_add_right lane :=if Nat.eqb lane 0 then 2804 else 2552.
Definition rf_add_output lane :=nth 0 [::3500;3222;3503]lane.
Theorem rf_reference_add_four lane invalid s0 s1 s2 s3 s4 left right :
 (lane<3)%coq_nat ->
 (forall old, old=s0 \/ old=s1 ->VM.find(rf_add_left lane)old=Some(Gval(Fuint 32)left)) ->
 (forall old, old=s0 \/ old=s1 ->VM.find(rf_add_right lane)old=Some(Gval(Fuint 32)right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 VM.find(rf_add_output lane)s4=Some(Gval(Fuint 32)(reference_load_address left right)).
Proof.
 intros Bound Left Right S1 S2 S3 S4.
 destruct lane as[|lane].
 {
 pose proof(Left s0(or_introl(Logic.eq_refl _)))as L.
 pose proof(Right s0(or_introl(Logic.eq_refl _)))as R.
 cbn[rf_add_left rf_add_right]in L,R.
assert(V3496:VM.find 3496 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3496 rf_arithmetic_expr_3496);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 4%nat);reflexivity| |exact S1].
intros site. cbn[rf_arithmetic_expr_3496 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite L. reflexivity.
}
assert(V3497:VM.find 3497 s1=Some(Gval(Fuint 32)right)).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3497 rf_arithmetic_expr_3497);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 5%nat);reflexivity| |exact S1].
intros site. cbn[rf_arithmetic_expr_3497 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R. reflexivity.
}
assert(Sum:VM.find 3498 s2=Some(Gval(Fuint 33)(from_N 33(to_N left+to_N right)))).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3498 rf_arithmetic_expr_3498);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 6%nat);reflexivity| |exact S2].
intros site. cbn[rf_arithmetic_expr_3498 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite V3496 V3497. reflexivity.
}
assert(Tail:VM.find 3499 s3=Some(Gval(Fuint 32)(reference_load_address left right))).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3499 rf_arithmetic_expr_3499);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 7%nat);reflexivity| |exact S3].
intros site. cbn[rf_arithmetic_expr_3499 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sum. reflexivity.
}
eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3500 rf_arithmetic_expr_3500);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 8%nat);reflexivity| |exact S4].
intros site. cbn[rf_arithmetic_expr_3500 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Tail. reflexivity.
}
destruct lane as[|lane].
{
pose proof(Left s0(or_introl(Logic.eq_refl _)))as L.
pose proof(Right s1(or_intror(Logic.eq_refl _)))as R.
cbn[rf_add_left rf_add_right]in L,R.
assert(A:VM.find 3067 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3067 rf_arithmetic_expr_3067);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 0%nat);reflexivity| |exact S1].
intros site. cbn[rf_arithmetic_expr_3067 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite L. reflexivity.
}
assert(Sum:VM.find 3068 s2=Some(Gval(Fuint 33)(from_N 33(to_N left+to_N right)))).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3068 rf_arithmetic_expr_3068);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 1%nat);reflexivity| |exact S2].
intros site. cbn[rf_arithmetic_expr_3068 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A R. reflexivity.
}
assert(Tail:VM.find 3069 s3=Some(Gval(Fuint 32)(reference_load_address left right))).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3069 rf_arithmetic_expr_3069);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 2%nat);reflexivity| |exact S3].
intros site. cbn[rf_arithmetic_expr_3069 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sum. reflexivity.
}
eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3222 rf_arithmetic_expr_3222);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 3%nat);reflexivity| |exact S4].
intros site. cbn[rf_arithmetic_expr_3222 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Tail. reflexivity.
}
destruct lane as[|lane];[|lia].
pose proof(Left s1(or_intror(Logic.eq_refl _)))as L.
pose proof(Right s1(or_intror(Logic.eq_refl _)))as R.
cbn[rf_add_left rf_add_right]in L,R.
assert(Sum:VM.find 3501 s2=Some(Gval(Fuint 33)(from_N 33(to_N left+to_N right)))).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3501 rf_arithmetic_expr_3501);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 9%nat);reflexivity| |exact S2].
intros site. cbn[rf_arithmetic_expr_3501 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite L R. reflexivity.
}
assert(Tail:VM.find 3502 s3=Some(Gval(Fuint 32)(reference_load_address left right))).
{eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3502 rf_arithmetic_expr_3502);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 10%nat);reflexivity| |exact S3].
intros site. cbn[rf_arithmetic_expr_3502 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Sum. reflexivity.
}
eapply(reference_redirect_ground_step rf_arithmetic_offsets rf_arithmetic_nodes 3503 rf_arithmetic_expr_3503);[exact rf_arithmetic_positions|exact rf_arithmetic_safety|apply(List.nth_error_In rf_arithmetic_nodes 11%nat);reflexivity| |exact S4].
intros site. cbn[rf_arithmetic_expr_3503 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Tail. reflexivity.
Qed.
Require Import FormalObservedHistory ReferenceControlStabilityHistory.
Theorem rf_reference_add_observed memory inputs k observed lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (lane<3)%coq_nat ->
 VM.find(rf_add_left lane)(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find(rf_add_right lane)(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find(rf_add_output lane)(top_environment observed)=Some(Gval(Fuint 32)(reference_load_address left right)).
Proof.
 intros Observe Legal Lane Left Right.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(L:forall time,(9255<=time)%coq_nat ->(time<=9259)%coq_nat ->VM.find(rf_add_left lane)(history time)=Some(Gval(Fuint 32)left)).
 { intros time Lower Upper. unfold rf_add_left in*. destruct(Nat.eqb lane 2).
 - rewrite(reference_control_stable_2812_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9255 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left.
 - rewrite(reference_control_stable_2209_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9255 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall time,(9255<=time)%coq_nat ->(time<=9259)%coq_nat ->VM.find(rf_add_right lane)(history time)=Some(Gval(Fuint 32)right)).
 { intros time Lower Upper. unfold rf_add_right in*. destruct(Nat.eqb lane 0).
 - rewrite(reference_control_stable_2804_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9255 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right.
 - rewrite(reference_control_stable_2552_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps time 9259 ltac:(apply (Nat.le_trans _ 9255 _);[vm_compute;lia|exact Lower])ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 rewrite<-Last.
 apply(rf_reference_add_four lane(formal_invalid_policy(generated_observation_input inputs k)nil)(history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)(history 9259%nat)left right Lane).
 - intros old[Same|Same];subst old;apply L;vm_compute;lia.
 - intros old[Same|Same];subst old;apply R;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
 - apply Steps;vm_compute;lia.
Qed.
