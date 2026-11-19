Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_alu_expr_1290 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Definition rf_alu_expr_1292 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Definition rf_alu_expr_1294 := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 1151)) (@Eref VarOrder.T (@Eid VarOrder.T 1152))).
Definition rf_alu_expr_3472 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_alu_expr_3473 := (@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_alu_expr_3474 := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 3472)) (@Eref VarOrder.T (@Eid VarOrder.T 3473))).
Definition rf_alu_expr_3475 := (@Eref VarOrder.T (@Eid VarOrder.T 3474)).
Definition rf_alu_expr_3476 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_alu_expr_3477 := (@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_alu_expr_3478 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 3476)) (@Eref VarOrder.T (@Eid VarOrder.T 3477))).
Definition rf_alu_expr_3479 := (@Eref VarOrder.T (@Eid VarOrder.T 3478)).
Definition rf_alu_expr_3480 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_alu_expr_3481 := (@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_alu_expr_3482 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3480)) (@Eref VarOrder.T (@Eid VarOrder.T 3481))).
Definition rf_alu_expr_3483 := (@Eref VarOrder.T (@Eid VarOrder.T 3482)).
Definition rf_alu_expr_3519 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_alu_expr_3520 := (@Eprim_binop VarOrder.T Bxor (@Eref VarOrder.T (@Eid VarOrder.T 3519)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_alu_expr_3521 := (@Eref VarOrder.T (@Eid VarOrder.T 3520)).
Definition rf_alu_expr_3522 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_alu_expr_3523 := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 3522)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_alu_expr_3524 := (@Eref VarOrder.T (@Eid VarOrder.T 3523)).
Definition rf_alu_expr_3525 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_alu_expr_3526 := (@Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 3525)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_alu_expr_3527 := (@Eref VarOrder.T (@Eid VarOrder.T 3526)).
Definition rf_alu_nodes := [::(1290,rf_alu_expr_1290);(1292,rf_alu_expr_1292);(1294,rf_alu_expr_1294);(3472,rf_alu_expr_3472);(3473,rf_alu_expr_3473);(3474,rf_alu_expr_3474);(3475,rf_alu_expr_3475);(3476,rf_alu_expr_3476);(3477,rf_alu_expr_3477);(3478,rf_alu_expr_3478);(3479,rf_alu_expr_3479);(3480,rf_alu_expr_3480);(3481,rf_alu_expr_3481);(3482,rf_alu_expr_3482);(3483,rf_alu_expr_3483);(3519,rf_alu_expr_3519);(3520,rf_alu_expr_3520);(3521,rf_alu_expr_3521);(3522,rf_alu_expr_3522);(3523,rf_alu_expr_3523);(3524,rf_alu_expr_3524);(3525,rf_alu_expr_3525);(3526,rf_alu_expr_3526);(3527,rf_alu_expr_3527)].
Definition rf_alu_offsets := [::1365%nat;1%nat;1%nat;2181%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;35%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_alu_positions :select_node_offsets rf_alu_offsets flat_statements=Some rf_alu_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_alu_safety :selected_node_safety flat_memories flat_statements rf_alu_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_bitwise_op lane :=match Nat.modulo lane 3 with 0%nat=>Band|1%nat=>Bor|_=>Bxor end.
Definition rf_bitwise_word lane left right :=match Nat.modulo lane 3 with 0%nat=>andB left right|1%nat=>orB left right|_=>xorB left right end.
Definition rf_bitwise_source lane :=if Nat.ltb lane 3 then 2804 else 2552.
Definition rf_bitwise_output lane := nth 0 [::3483;3479;3475;3527;3524;3521] lane.
Definition rf_bitwise_dut lane :=nth 0 [::1290;1292;1294] (Nat.modulo lane 3).
Theorem rf_reference_bitwise_three lane invalid s0 s1 s2 s3 left right : (lane<6)%coq_nat ->
 VM.find 2209 s0=Some(Gval(Fuint 32)left) ->
 (forall old,old=s0 \/ old=s1 ->VM.find(rf_bitwise_source lane)old=Some(Gval(Fuint 32)right)) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 VM.find(rf_bitwise_output lane)s3=Some(Gval(Fuint 32)(rf_bitwise_word lane left right)).
Proof. intros Bound Left Right S1 S2 S3.
destruct lane as[|lane].
{
assert(A:VM.find 3480 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3480 rf_alu_expr_3480);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 11%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3480 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. reflexivity.
}
assert(B:VM.find 3481 s1=Some(Gval(Fuint 32)right)).
{pose proof(Right s0 (or_introl(Logic.eq_refl _)))as R. cbn[rf_bitwise_source]in R.
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3481 rf_alu_expr_3481);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 12%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3481 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R. reflexivity.
}
assert(C:VM.find 3482 s2=Some(Gval(Fuint 32)(andB left right))).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3482 rf_alu_expr_3482);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 13%nat);reflexivity| |exact S2].
intros site. cbn[rf_alu_expr_3482 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A B. reflexivity.
}
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3483 rf_alu_expr_3483);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 14%nat);reflexivity| |exact S3].
intros site. cbn[rf_alu_expr_3483 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite C. reflexivity.
}
destruct lane as[|lane].
{
assert(A:VM.find 3476 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3476 rf_alu_expr_3476);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 7%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3476 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. reflexivity.
}
assert(B:VM.find 3477 s1=Some(Gval(Fuint 32)right)).
{pose proof(Right s0 (or_introl(Logic.eq_refl _)))as R. cbn[rf_bitwise_source]in R.
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3477 rf_alu_expr_3477);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 8%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3477 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R. reflexivity.
}
assert(C:VM.find 3478 s2=Some(Gval(Fuint 32)(orB left right))).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3478 rf_alu_expr_3478);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 9%nat);reflexivity| |exact S2].
intros site. cbn[rf_alu_expr_3478 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A B. reflexivity.
}
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3479 rf_alu_expr_3479);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 10%nat);reflexivity| |exact S3].
intros site. cbn[rf_alu_expr_3479 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite C. reflexivity.
}
destruct lane as[|lane].
{
assert(A:VM.find 3472 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3472 rf_alu_expr_3472);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 3%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3472 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. reflexivity.
}
assert(B:VM.find 3473 s1=Some(Gval(Fuint 32)right)).
{pose proof(Right s0 (or_introl(Logic.eq_refl _)))as R. cbn[rf_bitwise_source]in R.
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3473 rf_alu_expr_3473);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 4%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3473 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite R. reflexivity.
}
assert(C:VM.find 3474 s2=Some(Gval(Fuint 32)(xorB left right))).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3474 rf_alu_expr_3474);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 5%nat);reflexivity| |exact S2].
intros site. cbn[rf_alu_expr_3474 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A B. reflexivity.
}
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3475 rf_alu_expr_3475);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 6%nat);reflexivity| |exact S3].
intros site. cbn[rf_alu_expr_3475 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite C. reflexivity.
}
destruct lane as[|lane].
{
assert(A:VM.find 3525 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3525 rf_alu_expr_3525);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 21%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3525 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. reflexivity.
}
pose proof(Right s1 (or_intror(Logic.eq_refl _)))as B. cbn[rf_bitwise_source]in B.
assert(C:VM.find 3526 s2=Some(Gval(Fuint 32)(andB left right))).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3526 rf_alu_expr_3526);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 22%nat);reflexivity| |exact S2].
intros site. cbn[rf_alu_expr_3526 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A B. reflexivity.
}
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3527 rf_alu_expr_3527);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 23%nat);reflexivity| |exact S3].
intros site. cbn[rf_alu_expr_3527 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite C. reflexivity.
}
destruct lane as[|lane].
{
assert(A:VM.find 3522 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3522 rf_alu_expr_3522);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 18%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3522 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. reflexivity.
}
pose proof(Right s1 (or_intror(Logic.eq_refl _)))as B. cbn[rf_bitwise_source]in B.
assert(C:VM.find 3523 s2=Some(Gval(Fuint 32)(orB left right))).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3523 rf_alu_expr_3523);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 19%nat);reflexivity| |exact S2].
intros site. cbn[rf_alu_expr_3523 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A B. reflexivity.
}
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3524 rf_alu_expr_3524);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 20%nat);reflexivity| |exact S3].
intros site. cbn[rf_alu_expr_3524 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite C. reflexivity.
}
destruct lane as[|lane].
{
assert(A:VM.find 3519 s1=Some(Gval(Fuint 32)left)).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3519 rf_alu_expr_3519);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 15%nat);reflexivity| |exact S1].
intros site. cbn[rf_alu_expr_3519 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left. reflexivity.
}
pose proof(Right s1 (or_intror(Logic.eq_refl _)))as B. cbn[rf_bitwise_source]in B.
assert(C:VM.find 3520 s2=Some(Gval(Fuint 32)(xorB left right))).
{eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3520 rf_alu_expr_3520);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 16%nat);reflexivity| |exact S2].
intros site. cbn[rf_alu_expr_3520 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite A B. reflexivity.
}
eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 3521 rf_alu_expr_3521);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 17%nat);reflexivity| |exact S3].
intros site. cbn[rf_alu_expr_3521 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite C. reflexivity.
}
lia. Qed.

Theorem rf_dut_bitwise_step lane invalid old result left right : (lane<6)%coq_nat ->
 VM.find 1151 old=Some(Gval(Fuint 32)left) ->
 VM.find 1152 old=Some(Gval(Fuint 32)right) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(rf_bitwise_dut lane)result=Some(Gval(Fuint 32)(rf_bitwise_word lane left right)).
Proof. intros Bound Left Right Step.
destruct lane as[|lane].
{ eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 1290 rf_alu_expr_1290);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 0%nat);reflexivity| |exact Step].
intros site. cbn[rf_alu_expr_1290 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. reflexivity. }
destruct lane as[|lane].
{ eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 1292 rf_alu_expr_1292);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 1%nat);reflexivity| |exact Step].
intros site. cbn[rf_alu_expr_1292 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. reflexivity. }
destruct lane as[|lane].
{ eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 1294 rf_alu_expr_1294);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 2%nat);reflexivity| |exact Step].
intros site. cbn[rf_alu_expr_1294 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. reflexivity. }
destruct lane as[|lane].
{ eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 1290 rf_alu_expr_1290);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 0%nat);reflexivity| |exact Step].
intros site. cbn[rf_alu_expr_1290 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. reflexivity. }
destruct lane as[|lane].
{ eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 1292 rf_alu_expr_1292);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 1%nat);reflexivity| |exact Step].
intros site. cbn[rf_alu_expr_1292 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. reflexivity. }
destruct lane as[|lane].
{ eapply(reference_redirect_ground_step rf_alu_offsets rf_alu_nodes 1294 rf_alu_expr_1294);[exact rf_alu_positions|exact rf_alu_safety|apply(List.nth_error_In rf_alu_nodes 2%nat);reflexivity| |exact Step].
intros site. cbn[rf_alu_expr_1294 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right. reflexivity. }
lia. Qed.
Theorem rf_bitwise_data_correspondence lane invalid dut dut_next r0 r1 r2 r3 left right :
 (lane<6)%coq_nat ->
 VM.find 1151 dut=Some(Gval(Fuint 32)left) ->
 VM.find 1152 dut=Some(Gval(Fuint 32)right) ->
 VM.find 2209 r0=Some(Gval(Fuint 32)left) ->
 (forall old,old=r0 \/ old=r1 ->VM.find(rf_bitwise_source lane)old=Some(Gval(Fuint 32)right)) ->
 formal_value_iter invalid flat_memories dut false dut flat_statements=Some dut_next ->
 formal_value_iter invalid flat_memories r0 false r0 flat_statements=Some r1 ->
 formal_value_iter invalid flat_memories r1 false r1 flat_statements=Some r2 ->
 formal_value_iter invalid flat_memories r2 false r2 flat_statements=Some r3 ->
 VM.find(rf_bitwise_dut lane)dut_next=VM.find(rf_bitwise_output lane)r3.
Proof.
 intros Bound DL DR RL RR DS S1 S2 S3.
 rewrite(rf_dut_bitwise_step lane invalid dut dut_next left right Bound DL DR DS).
 rewrite(rf_reference_bitwise_three lane invalid r0 r1 r2 r3 left right Bound RL RR S1 S2 S3). reflexivity.
Qed.

Require Import ALUOutputTransfer RFReferenceWriteEffect JointUpdateNodePositions JointUpdateExpressionCertificates FormalSuccessfulNodeEvaluation FormalTypedNodeEquation.
Lemma rf_alu_selected_low_mux node condition yes no invalid old result bit selected word :
 List.In(node,@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T condition))(@Eref VarOrder.T(@Eid VarOrder.T yes))(@Eref VarOrder.T(@Eid VarOrder.T no)))joint_update_expected_nodes ->
 VM.find condition old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find(if bit then yes else no)old=Some selected ->rf_reference_low_word word selected ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find node result=Some value /\rf_reference_low_word word value.
Proof.
 intros Member Condition Selected [width[raw[Value[Size[Wide Low]]]]] Step. subst selected.
 destruct(selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes node _ joint_update_node_positions joint_update_node_safety Member)as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false old result Position Step)as[value Eval].
 pose proof Eval as Original.
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]in Eval. rewrite Condition in Eval.
 destruct bit;cbn in Eval;rewrite Selected in Eval;
 destruct(eval_type_of_expr _)as[typ|]eqn:Branch;try discriminate;
 unfold extend_hvalue_as_type in Eval;destruct typ as[ground|elt length|fields];try discriminate;
 destruct ground;cbn[type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type]in Eval;try discriminate;
 inversion Eval;subst value.
 all: eexists;split;[eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Original|reflexivity|exact Step]|].
 all: destruct(rf_reference_low_resize word (Gval(Fuint width)raw) (maxn width n))as[adapted[Adapt Result]].
all: try (exists width,raw;repeat split;assumption).
all: try (intros source bits Equal;inversion Equal;subst;apply leq_maxl).
all: cbn[adapt_hvalue_as_type]in Adapt;inversion Adapt;subst;exact Result.
Qed.

Definition rf_bitwise_guard index :=nth 0 [::1293;1291;1289;1288;1287;1284;1281] index.
Lemma rf_bitwise_guard_two lane guard invalid s0 s1 s2 : (lane<3)%coq_nat ->(guard<7)%coq_nat ->
 VM.find 1153 s0=Some(Gval(Fuint 4)(from_N 4(N.of_nat(2+lane)))) ->
 VM.find 1153 s1=Some(Gval(Fuint 4)(from_N 4(N.of_nat(2+lane)))) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find(rf_bitwise_guard guard)s2=Some(Gval(Fuint 1)[::Nat.eqb guard(Nat.sub 2 lane)]).
Proof. intros Lane Guard Mode0 Mode1 S1 S2.
destruct lane as[|lane].
{
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1293 joint_update_expr_1293);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 838%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1293 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1291 joint_update_expr_1291);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 836%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1291 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1289 joint_update_expr_1289);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 834%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1289 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1288 joint_update_expr_1288);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 833%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1288 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
assert(H1285:VM.find 1285 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1285 joint_update_expr_1285);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 830%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1285 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1286:VM.find 1286 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1286 joint_update_expr_1286);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 831%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1286 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1287 joint_update_expr_1287);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 832%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1287 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1285 H1286. reflexivity.
}
destruct guard as[|guard].
{
assert(H1282:VM.find 1282 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1282 joint_update_expr_1282);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 827%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1282 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1283:VM.find 1283 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1283 joint_update_expr_1283);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 828%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1283 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1284 joint_update_expr_1284);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 829%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1284 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1282 H1283. reflexivity.
}
destruct guard as[|guard].
{
assert(H1279:VM.find 1279 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 824%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1280:VM.find 1280 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 825%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 826%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1279 H1280. reflexivity.
}
lia. }
destruct lane as[|lane].
{
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1293 joint_update_expr_1293);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 838%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1293 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1291 joint_update_expr_1291);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 836%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1291 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1289 joint_update_expr_1289);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 834%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1289 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1288 joint_update_expr_1288);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 833%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1288 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
assert(H1285:VM.find 1285 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1285 joint_update_expr_1285);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 830%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1285 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1286:VM.find 1286 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1286 joint_update_expr_1286);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 831%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1286 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1287 joint_update_expr_1287);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 832%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1287 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1285 H1286. reflexivity.
}
destruct guard as[|guard].
{
assert(H1282:VM.find 1282 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1282 joint_update_expr_1282);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 827%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1282 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1283:VM.find 1283 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1283 joint_update_expr_1283);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 828%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1283 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1284 joint_update_expr_1284);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 829%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1284 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1282 H1283. reflexivity.
}
destruct guard as[|guard].
{
assert(H1279:VM.find 1279 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 824%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1280:VM.find 1280 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 825%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 826%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1279 H1280. reflexivity.
}
lia. }
destruct lane as[|lane].
{
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1293 joint_update_expr_1293);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 838%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1293 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1291 joint_update_expr_1291);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 836%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1291 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1289 joint_update_expr_1289);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 834%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1289 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1288 joint_update_expr_1288);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 833%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1288 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode1. reflexivity.
}
destruct guard as[|guard].
{
assert(H1285:VM.find 1285 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1285 joint_update_expr_1285);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 830%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1285 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1286:VM.find 1286 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1286 joint_update_expr_1286);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 831%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1286 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1287 joint_update_expr_1287);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 832%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1287 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1285 H1286. reflexivity.
}
destruct guard as[|guard].
{
assert(H1282:VM.find 1282 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1282 joint_update_expr_1282);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 827%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1282 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1283:VM.find 1283 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1283 joint_update_expr_1283);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 828%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1283 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1284 joint_update_expr_1284);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 829%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1284 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1282 H1283. reflexivity.
}
destruct guard as[|guard].
{
assert(H1279:VM.find 1279 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1279 joint_update_expr_1279);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 824%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1279 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
assert(H1280:VM.find 1280 s1=Some(Gval(Fuint 1)[::false])).
{eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1280 joint_update_expr_1280);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 825%nat);vm_compute;reflexivity| |exact S1].
intros site. cbn[joint_update_expr_1280 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Mode0. reflexivity.
}
eapply(reference_redirect_ground_step joint_update_node_offsets joint_update_expected_nodes 1281 joint_update_expr_1281);[exact joint_update_node_positions|exact joint_update_node_safety|apply(List.nth_error_In joint_update_expected_nodes 826%nat);vm_compute;reflexivity| |exact S2].
intros site. cbn[joint_update_expr_1281 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite H1279 H1280. reflexivity.
}
lia. }
lia. Qed.

Require Import JointUpdateConnectionCertificates FormalDeclaredConnection.

Lemma rf_bitwise_word_size lane left right :size left=32%nat ->size right=32%nat ->size(rf_bitwise_word lane left right)=32%nat.
Proof. intros Left Right. unfold rf_bitwise_word. destruct(Nat.modulo lane 3)as[|[|n]];rewrite ?size_andB ?size_orB ?size_xorB Left Right;reflexivity. Qed.
Lemma rf_low_word_adapt32 word value :rf_reference_low_word word value ->adapt_hvalue_as_type value(Gtyp(Fuint 32))=Some(Gval(Fuint 32)word).
Proof.
 intros[width[raw[Value[Size[Wide Low]]]]]. subst value. cbn[adapt_hvalue_as_type]. rewrite Low.
 assert(WordSize:size word=32%nat).
 { rewrite -Low size_take Size. apply/minn_idPl. exact Wide. }
 unfold zext_to,zext. rewrite WordSize subnn cats0. reflexivity.
Qed.
Theorem rf_bitwise_alu_output_history lane invalid history left right : (lane<3)%coq_nat ->
 size left=32%nat ->size right=32%nat ->
 (forall t,(t<=9)%coq_nat ->VM.find 1151(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(t<=9)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<=9)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)(from_N 4(N.of_nat(2+lane))))) ->
 (forall t,(t<10)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 1154(history 10%nat)=Some(Gval(Fuint 32)(rf_bitwise_word lane left right)).
Proof.
 intros Lane LeftSize RightSize Left Right Mode Steps.
 assert(Guard:forall guard t,(guard<7)%coq_nat ->(2<=t)%coq_nat ->(t<=9)%coq_nat ->VM.find(rf_bitwise_guard guard)(history t)=Some(Gval(Fuint 1)[::Nat.eqb guard(Nat.sub 2 lane)])).
 { intros guard t G T U. destruct t as[|[|t]];try lia.
 exact(rf_bitwise_guard_two lane guard invalid(history t)(history(S t))(history(S(S t)))Lane G(Mode t ltac:(lia))(Mode(S t)ltac:(lia))(Steps t ltac:(lia))(Steps(S t)ltac:(lia))). }
 assert(Out:exists value,VM.find 1303(history 9%nat)=Some value /\rf_reference_low_word(rf_bitwise_word lane left right)value).
 {
destruct lane as[|lane].
{
pose proof(rf_dut_bitwise_step 0%nat invalid(history 3%nat)(history 4%nat)left right ltac:(lia)(Left 3%nat ltac:(lia))(Right 3%nat ltac:(lia))(Steps 3%nat ltac:(lia)))as V0.
assert(L0:rf_reference_low_word(rf_bitwise_word 0%nat left right)(Gval(Fuint 32)(rf_bitwise_word 0%nat left right))).
{ exists 32%nat,(rf_bitwise_word 0%nat left right). split;[reflexivity|]. split;[exact(rf_bitwise_word_size _ _ _ LeftSize RightSize)|]. split;[reflexivity|]. rewrite -(rf_bitwise_word_size 0%nat left right LeftSize RightSize) take_size. reflexivity. }
pose proof(Guard 2%nat 4%nat ltac:(lia)ltac:(lia)ltac:(lia))as G0.
destruct(rf_alu_selected_low_mux 1299 1289 1290 1298 invalid(history 4%nat)(history 5%nat)true (Gval(Fuint 32)(rf_bitwise_word 0%nat left right)) (rf_bitwise_word 0%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 844%nat);vm_compute;reflexivity)G0 V0 L0(Steps 4%nat ltac:(lia)))as[v1[V1 L1]].
pose proof(Guard 3%nat 5%nat ltac:(lia)ltac:(lia)ltac:(lia))as G1.
destruct(rf_alu_selected_low_mux 1300 1288 1278 1299 invalid(history 5%nat)(history 6%nat)false v1 (rf_bitwise_word 0%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 845%nat);vm_compute;reflexivity)G1 V1 L1(Steps 5%nat ltac:(lia)))as[v2[V2 L2]].
pose proof(Guard 4%nat 6%nat ltac:(lia)ltac:(lia)ltac:(lia))as G2.
destruct(rf_alu_selected_low_mux 1301 1287 1229 1300 invalid(history 6%nat)(history 7%nat)false v2 (rf_bitwise_word 0%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 846%nat);vm_compute;reflexivity)G2 V2 L2(Steps 6%nat ltac:(lia)))as[v3[V3 L3]].
pose proof(Guard 5%nat 7%nat ltac:(lia)ltac:(lia)ltac:(lia))as G3.
destruct(rf_alu_selected_low_mux 1302 1284 1170 1301 invalid(history 7%nat)(history 8%nat)false v3 (rf_bitwise_word 0%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 847%nat);vm_compute;reflexivity)G3 V3 L3(Steps 7%nat ltac:(lia)))as[v4[V4 L4]].
pose proof(Guard 6%nat 8%nat ltac:(lia)ltac:(lia)ltac:(lia))as G4.
destruct(rf_alu_selected_low_mux 1303 1281 1161 1302 invalid(history 8%nat)(history 9%nat)false v4 (rf_bitwise_word 0%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 848%nat);vm_compute;reflexivity)G4 V4 L4(Steps 8%nat ltac:(lia)))as[v5[V5 L5]].
exists v5. split;assumption. }
destruct lane as[|lane].
{
pose proof(rf_dut_bitwise_step 1%nat invalid(history 2%nat)(history 3%nat)left right ltac:(lia)(Left 2%nat ltac:(lia))(Right 2%nat ltac:(lia))(Steps 2%nat ltac:(lia)))as V0.
assert(L0:rf_reference_low_word(rf_bitwise_word 1%nat left right)(Gval(Fuint 32)(rf_bitwise_word 1%nat left right))).
{ exists 32%nat,(rf_bitwise_word 1%nat left right). split;[reflexivity|]. split;[exact(rf_bitwise_word_size _ _ _ LeftSize RightSize)|]. split;[reflexivity|]. rewrite -(rf_bitwise_word_size 1%nat left right LeftSize RightSize) take_size. reflexivity. }
pose proof(Guard 1%nat 3%nat ltac:(lia)ltac:(lia)ltac:(lia))as G0.
destruct(rf_alu_selected_low_mux 1298 1291 1292 1297 invalid(history 3%nat)(history 4%nat)true (Gval(Fuint 32)(rf_bitwise_word 1%nat left right)) (rf_bitwise_word 1%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 843%nat);vm_compute;reflexivity)G0 V0 L0(Steps 3%nat ltac:(lia)))as[v1[V1 L1]].
pose proof(Guard 2%nat 4%nat ltac:(lia)ltac:(lia)ltac:(lia))as G1.
destruct(rf_alu_selected_low_mux 1299 1289 1290 1298 invalid(history 4%nat)(history 5%nat)false v1 (rf_bitwise_word 1%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 844%nat);vm_compute;reflexivity)G1 V1 L1(Steps 4%nat ltac:(lia)))as[v2[V2 L2]].
pose proof(Guard 3%nat 5%nat ltac:(lia)ltac:(lia)ltac:(lia))as G2.
destruct(rf_alu_selected_low_mux 1300 1288 1278 1299 invalid(history 5%nat)(history 6%nat)false v2 (rf_bitwise_word 1%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 845%nat);vm_compute;reflexivity)G2 V2 L2(Steps 5%nat ltac:(lia)))as[v3[V3 L3]].
pose proof(Guard 4%nat 6%nat ltac:(lia)ltac:(lia)ltac:(lia))as G3.
destruct(rf_alu_selected_low_mux 1301 1287 1229 1300 invalid(history 6%nat)(history 7%nat)false v3 (rf_bitwise_word 1%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 846%nat);vm_compute;reflexivity)G3 V3 L3(Steps 6%nat ltac:(lia)))as[v4[V4 L4]].
pose proof(Guard 5%nat 7%nat ltac:(lia)ltac:(lia)ltac:(lia))as G4.
destruct(rf_alu_selected_low_mux 1302 1284 1170 1301 invalid(history 7%nat)(history 8%nat)false v4 (rf_bitwise_word 1%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 847%nat);vm_compute;reflexivity)G4 V4 L4(Steps 7%nat ltac:(lia)))as[v5[V5 L5]].
pose proof(Guard 6%nat 8%nat ltac:(lia)ltac:(lia)ltac:(lia))as G5.
destruct(rf_alu_selected_low_mux 1303 1281 1161 1302 invalid(history 8%nat)(history 9%nat)false v5 (rf_bitwise_word 1%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 848%nat);vm_compute;reflexivity)G5 V5 L5(Steps 8%nat ltac:(lia)))as[v6[V6 L6]].
exists v6. split;assumption. }
destruct lane as[|lane].
{
pose proof(rf_dut_bitwise_step 2%nat invalid(history 1%nat)(history 2%nat)left right ltac:(lia)(Left 1%nat ltac:(lia))(Right 1%nat ltac:(lia))(Steps 1%nat ltac:(lia)))as V0.
assert(L0:rf_reference_low_word(rf_bitwise_word 2%nat left right)(Gval(Fuint 32)(rf_bitwise_word 2%nat left right))).
{ exists 32%nat,(rf_bitwise_word 2%nat left right). split;[reflexivity|]. split;[exact(rf_bitwise_word_size _ _ _ LeftSize RightSize)|]. split;[reflexivity|]. rewrite -(rf_bitwise_word_size 2%nat left right LeftSize RightSize) take_size. reflexivity. }
pose proof(Guard 0%nat 2%nat ltac:(lia)ltac:(lia)ltac:(lia))as G0.
destruct(rf_alu_selected_low_mux 1297 1293 1294 1296 invalid(history 2%nat)(history 3%nat)true (Gval(Fuint 32)(rf_bitwise_word 2%nat left right)) (rf_bitwise_word 2%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 842%nat);vm_compute;reflexivity)G0 V0 L0(Steps 2%nat ltac:(lia)))as[v1[V1 L1]].
pose proof(Guard 1%nat 3%nat ltac:(lia)ltac:(lia)ltac:(lia))as G1.
destruct(rf_alu_selected_low_mux 1298 1291 1292 1297 invalid(history 3%nat)(history 4%nat)false v1 (rf_bitwise_word 2%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 843%nat);vm_compute;reflexivity)G1 V1 L1(Steps 3%nat ltac:(lia)))as[v2[V2 L2]].
pose proof(Guard 2%nat 4%nat ltac:(lia)ltac:(lia)ltac:(lia))as G2.
destruct(rf_alu_selected_low_mux 1299 1289 1290 1298 invalid(history 4%nat)(history 5%nat)false v2 (rf_bitwise_word 2%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 844%nat);vm_compute;reflexivity)G2 V2 L2(Steps 4%nat ltac:(lia)))as[v3[V3 L3]].
pose proof(Guard 3%nat 5%nat ltac:(lia)ltac:(lia)ltac:(lia))as G3.
destruct(rf_alu_selected_low_mux 1300 1288 1278 1299 invalid(history 5%nat)(history 6%nat)false v3 (rf_bitwise_word 2%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 845%nat);vm_compute;reflexivity)G3 V3 L3(Steps 5%nat ltac:(lia)))as[v4[V4 L4]].
pose proof(Guard 4%nat 6%nat ltac:(lia)ltac:(lia)ltac:(lia))as G4.
destruct(rf_alu_selected_low_mux 1301 1287 1229 1300 invalid(history 6%nat)(history 7%nat)false v4 (rf_bitwise_word 2%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 846%nat);vm_compute;reflexivity)G4 V4 L4(Steps 6%nat ltac:(lia)))as[v5[V5 L5]].
pose proof(Guard 5%nat 7%nat ltac:(lia)ltac:(lia)ltac:(lia))as G5.
destruct(rf_alu_selected_low_mux 1302 1284 1170 1301 invalid(history 7%nat)(history 8%nat)false v5 (rf_bitwise_word 2%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 847%nat);vm_compute;reflexivity)G5 V5 L5(Steps 7%nat ltac:(lia)))as[v6[V6 L6]].
pose proof(Guard 6%nat 8%nat ltac:(lia)ltac:(lia)ltac:(lia))as G6.
destruct(rf_alu_selected_low_mux 1303 1281 1161 1302 invalid(history 8%nat)(history 9%nat)false v6 (rf_bitwise_word 2%nat left right) ltac:(apply(List.nth_error_In joint_update_expected_nodes 848%nat);vm_compute;reflexivity)G6 V6 L6(Steps 8%nat ltac:(lia)))as[v7[V7 L7]].
exists v7. split;assumption. }
lia. }
 destruct Out as[value[Output Low]].
 eapply(declared_connection_value 1229 flat_statements joint_update_connection_1154_decl joint_update_connection_1154_mid joint_update_connection_1154_tail 1154 1303 32 value);
 [exact joint_update_connection_1154_position|exact joint_update_connection_1154_split|exact joint_update_connection_1154_straight|exact joint_update_connection_1154_mid_safe|exact joint_update_connection_1154_tail_safe|exact joint_update_connection_1154_nonregister|reflexivity|exact Output|exact(rf_low_word_adapt32 _ _ Low)|exact(Steps 9%nat ltac:(lia))].
Qed.

Require Import JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization FormalPipelineControlHistory FormalStallHistory FormalCheckerResetConnections ExceptionSourceNoTrap.
Theorem rf_alu_output_commit_full_history inputs path history result word :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 size word = 32%nat ->
 VM.find 1154 (history 9257%nat) = Some (Gval (Fuint 32) word) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7752 result = Some (Gval (Fuint 32) word).
Proof.
 intros Boundary Steps Resets NoTrap Size Output Commit.
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap) as NoException.
 assert (Member : List.In (7752%nat,32%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 57%nat). vm_compute;reflexivity. }
 pose proof (joint_update_register_history_concrete _ history 9259 7752 32 Member (Boundary 7752%nat 32%nat Member) Steps) as Old.
 destruct (Old 9257 ltac:(vm_compute;lia)) as [old4 [_ Old4]].
 destruct (Old 9258 ltac:(vm_compute;lia)) as [old5 [_ Old5]].
 destruct (Old 9259 ltac:(vm_compute;lia)) as [old6 [_ Old6]].
 assert (Stall : VM.find 7765 (history 9255%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9249%nat) (history 9250%nat) (history 9251%nat) (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (Reset6 : VM.find 65 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9255%nat) (history 9255%nat) (history 9256%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9254%nat) (history 9254%nat) (history 9255%nat) false); [apply Resets|apply Steps];vm_compute;lia.
 - apply Steps;vm_compute;lia. }
 assert (Reset9 : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false); [apply Resets|apply Steps];vm_compute;lia.
 - apply Steps;vm_compute;lia. }
 pose proof (pipeline_advance_after_two (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat) (history 9257%nat) false false Stall
 (NoException 9255 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) (Steps 9255 ltac:(vm_compute;lia)) (Steps 9256 ltac:(vm_compute;lia))) as Advance.
 pose proof (pipeline_flush_after_three (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false false false Stall
 (NoException 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Reset6
 (Steps 9255 ltac:(vm_compute;lia)) (Steps 9256 ltac:(vm_compute;lia)) (Steps 9257 ltac:(vm_compute;lia))) as Flush.
 pose proof(alu_output_normal_select (formal_invalid_policy inputs path)(history 9257%nat)(history 9258%nat)(history 9259%nat)word old4 old5 Size Advance Output Old4 Flush Old5 (Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia)))as Selected.
 exact(alu_output_normal_commit (formal_invalid_policy inputs path)(history 9259%nat)(history 9259%nat)result (Gval(Fuint 32)old6)word Old6 (Logic.eq_refl _) Reset9 Selected Size Commit).
Qed.

Definition rf_bitwise_tail_window (history:nat->VM.t hvalue) index :=match index with
|0%nat=>history 9247%nat
|1%nat=>history 9248%nat
|2%nat=>history 9249%nat
|3%nat=>history 9250%nat
|4%nat=>history 9251%nat
|5%nat=>history 9252%nat
|6%nat=>history 9253%nat
|7%nat=>history 9254%nat
|8%nat=>history 9255%nat
|9%nat=>history 9256%nat
|_=>history 9257%nat end.
Theorem rf_bitwise_commit_full_history inputs path history result lane left right :
 (lane<3)%coq_nat ->size left=32%nat ->size right=32%nat ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<9259)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=9259)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 45(history 9254%nat)=Some(Gval(Fuint 1)[::false]) ->
 (forall t,(9247<=t)%coq_nat ->(t<=9256)%coq_nat ->VM.find 1151(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(9247<=t)%coq_nat ->(t<=9256)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(9247<=t)%coq_nat ->(t<=9256)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)(from_N 4(N.of_nat(2+lane))))) ->
 formal_value_iter(formal_invalid_policy inputs path)flat_memories(history 9259%nat)true(history 9259%nat)flat_statements=Some result ->
 VM.find 7752 result=Some(Gval(Fuint 32)(rf_bitwise_word lane left right)).
Proof.
 intros Lane LeftSize RightSize Boundary Steps Resets NoTrap Left Right Mode Commit.
 apply(rf_alu_output_commit_full_history inputs path history result (rf_bitwise_word lane left right)Boundary Steps Resets NoTrap(rf_bitwise_word_size _ _ _ LeftSize RightSize));[|exact Commit].
 apply(rf_bitwise_alu_output_history lane(formal_invalid_policy inputs path)(rf_bitwise_tail_window history)left right Lane LeftSize RightSize).
 - intros t Bound. do 10(destruct t as[|t];[apply Left;vm_compute;lia|]);lia.
 - intros t Bound. do 10(destruct t as[|t];[apply Right;vm_compute;lia|]);lia.
 - intros t Bound. do 10(destruct t as[|t];[apply Mode;vm_compute;lia|]);lia.
 - intros t Bound. do 10(destruct t as[|t];[apply Steps;vm_compute;lia|]);lia.
Qed.
Require Import RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ControlWritebackKill ReferenceInstructionDecode.
Definition rf_bitwise_class lane :=if Nat.ltb lane 3 then Nat.add 14 lane else lane.
Definition rf_bitwise_control lane which :N :=match which with 0%nat=>1|1%nat=>if Nat.ltb lane 3 then 1 else 0|2%nat=>if Nat.ltb lane 3 then 0 else 1|_=>N.of_nat(Nat.add 2(Nat.modulo lane 3)) end.
Lemma rf_dut_decode_wb_choice instruction stage :(stage<49)%coq_nat ->
 dut_decode_test(to_N instruction)stage=wbkill_choice instruction(rf_wb_row(Nat.sub 48 stage)).
Proof.
 intro Bound. unfold dut_decode_test,wbkill_choice. rewrite redirect_to_N_and redirect_N_eqb N.eqb_sym.
 do 49(destruct stage as[|stage];[reflexivity|]);lia.
Qed.
Lemma rf_bitwise_decode_control instruction lane which :(lane<6)%coq_nat ->(which<4)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 load_execute_decode which(to_N instruction)49=from_N(load_execute_width which)(rf_bitwise_control lane which).
Proof.
 intros Lane Which Match.
 assert(Row:(rf_bitwise_class lane<37)%coq_nat).
 { unfold rf_bitwise_class. destruct(Nat.ltb lane 3)eqn:Small;[apply Nat.ltb_lt in Small|];lia. }
 cbn[load_execute_decode].
 repeat match goal with |-context[dut_decode_test(to_N instruction)?stage]=>rewrite(rf_dut_decode_wb_choice instruction stage ltac:(vm_compute;lia))(rf_wb_choice_onehot instruction(rf_bitwise_class lane)(Nat.sub 48 stage)Row ltac:(vm_compute;lia)Match)end.
 do 6(destruct lane as[|lane];[do 4(destruct which as[|which];[reflexivity|]);lia|]);lia.
Qed.
Theorem rf_bitwise_control_history inputs path history limit instruction lane which :
 (lane<6)%coq_nat ->(which<4)%coq_nat ->size instruction=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 forall time,(55<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find(load_execute_wire_target which true)(history time)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(rf_bitwise_control lane which))).
Proof.
 intros Lane Which Size Match Steps Front time Lower Upper.
 rewrite -(rf_bitwise_decode_control instruction lane which Lane Which Match).
 exact(load_execute_decode_history inputs path history limit instruction which Which Steps Front Size time Lower Upper).
Qed.

Require Import ConcreteRegisterInitialization ALUOperandTransfer LoadEffectiveAddress LoadImmediateSemantics RFReadPorts.
Definition rf_bitwise_right lane instruction right :=if Nat.ltb lane 3 then right else load_i_immediate instruction.
Theorem rf_bitwise_operand_history inputs path history limit instruction lane left right :
 (lane<6)%coq_nat ->size instruction=32%nat ->size left=32%nat ->size right=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)) ->
 forall time,(100<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1151(history time)=Some(Gval(Fuint 32)left) /\
 VM.find 1152(history time)=Some(Gval(Fuint 32)(rf_bitwise_right lane instruction right)) /\
 VM.find 1153(history time)=Some(Gval(Fuint 4)(from_N 4(N.of_nat(Nat.add 2(Nat.modulo lane 3))))).
Proof.
 intros Lane Size LeftSize RightSize Match Boundary Steps Front Left Right.
 pose proof(rf_bitwise_control_history inputs path history limit instruction lane)as Control.
 assert(Imm:Nat.ltb lane 3=false ->forall t,(68<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1308(history t)=Some(Gval(Fuint 32)(load_i_immediate instruction))).
 { intros Immediate t Lower Upper. eapply(load_imm_front_register_history _ history limit 55 instruction Size);[| |exact Steps|exact Lower|exact Upper].
 - pose proof(joint_update_register_history_same _ history limit 7748 32 load_imm_front_member Steps limit (Nat.le_refl _))as Hold. change(VM.find 7748(history limit)=VM.find 7748(history 0%nat))in Hold. rewrite<-Hold;exact Front.
 - intros u L U. pose proof(Control 2%nat Lane ltac:(lia)Size Match Steps Front u L U)as C. cbn[rf_bitwise_control]in C. rewrite Immediate in C. exact C. }
 assert(A:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1151(history time)=Some(Gval(Fuint 32)left)).
 { apply(alu_operand_selected_history _ history limit 68 true left LeftSize Steps false).
 - intros t L U. exact(Control 0%nat Lane ltac:(lia)Size Match Steps Front t ltac:(lia)U).
 - intros t L U. apply Left;lia.
 - intros t L U. destruct(joint_update_register_history_concrete _ history limit 7749 32 ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity) (Boundary 7749%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity)) Steps t U)as[word[W V]]. exists(Gval(Fuint 32)word);split;[exact V|reflexivity]. }
 assert(B:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1152(history time)=Some(Gval(Fuint 32)(rf_bitwise_right lane instruction right))).
 { assert(BSize:size(rf_bitwise_right lane instruction right)=32%nat).
 { unfold rf_bitwise_right. destruct(Nat.ltb lane 3);[exact RightSize|exact(load_i_immediate_size instruction Size)]. }
 apply(alu_operand_selected_history _ history limit 68 (Nat.ltb lane 3)(rf_bitwise_right lane instruction right) BSize Steps true).
 - intros t L U. pose proof(Control 1%nat Lane ltac:(lia)Size Match Steps Front t ltac:(lia)U)as C. cbn[rf_bitwise_control]in C. destruct(Nat.ltb lane 3);exact C.
 - intros t L U. unfold rf_bitwise_right. destruct(Nat.ltb lane 3)eqn:Reg;[apply Right;lia|apply Imm;[reflexivity|exact L|exact U]].
 - intros [|t] L U;try lia. destruct(Nat.ltb lane 3)eqn:Reg.
 + exact(alu_immediate_wire_type _ (history t)(history t)(history(S t))(Steps t ltac:(lia))).
 + exists(Gval(Fuint 32)right);split;[apply Right;lia|reflexivity]. }
 intros [|time] Lower Upper;try lia. split;[apply A;lia|]. split;[apply B;lia|].
 exact(load_operand_wire_value 2%nat _ (history time)(history time)(history(S time))(from_N 4(N.of_nat(Nat.add 2(Nat.modulo lane 3))))ltac:(lia)(size_from_N _ _)(Control 3%nat Lane ltac:(lia)Size Match Steps Front time ltac:(lia)ltac:(lia))(Steps time ltac:(lia))).
Qed.

Require Import FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap
 JointBoundaryReachable JointBoundaryPreparation FormalFetchType FormalResetPreparation.
Theorem rf_alu_observed_transfer_context memory inputs k observed next :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 exists history,
 history 9259%nat = top_environment observed /\
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) /\
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) /\
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) /\
 (forall word,size word=32%nat ->VM.find 1154(history 9257%nat)=Some(Gval(Fuint 32)word) ->VM.find 7752(top_environment next)=Some(Gval(Fuint 32)word)).
Proof.
 intros Observe Legal Next Reset.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width Member (Registers node width Member) Env Prepare). }
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [initial_env [InitialEnv InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite InitialEnv. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 rewrite <- Top in Step. rewrite <- Last in Step.
 exists history. split;[exact Last|]. split;[exact Boundary|]. split;[exact Steps|]. split;[exact Resets|].
 intros word Size Output.
 unfold top_environment. rewrite After.
 exact(rf_alu_output_commit_full_history (generated_observation_input inputs k)nil history after word Boundary Steps Resets NoTrap Size Output Step).
Qed.
Require Import ObservedJointRegisterConcrete EarlyControlStabilityHistory.
Theorem rf_bitwise_observed_commit memory inputs k observed next instruction lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<6)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_bitwise_class lane))=reference_instruction_code(rf_bitwise_class lane) ->
 size left=32%nat ->size right=32%nat ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(rf_bitwise_word lane left(rf_bitwise_right lane instruction right))).
Proof.
 intros Observe Legal Next Reset Lane Instruction Match LeftSize RightSize Left Right.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(rf_alu_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(L:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)).
 { intros t Lower Upper. rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)).
 { intros t Lower Upper. rewrite(early_control_stable_7819_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 pose proof(rf_bitwise_operand_history (generated_observation_input inputs k)nil history 9259 instruction lane left right Lane Size LeftSize RightSize Match Boundary Steps ltac:(rewrite Last;exact Instruction)L R)as Inputs.
 assert(RSize:size(rf_bitwise_right lane instruction right)=32%nat).
 { unfold rf_bitwise_right. destruct(Nat.ltb lane 3);[exact RightSize|exact(load_i_immediate_size instruction Size)]. }
 apply Transfer;[exact(rf_bitwise_word_size _ _ _ LeftSize RSize)|].
 assert(Mod:(Nat.modulo lane 3<3)%coq_nat)by(apply Nat.mod_upper_bound;lia).
 assert(Out:VM.find 1154(history 9257%nat)=Some(Gval(Fuint 32)(rf_bitwise_word (Nat.modulo lane 3)left(rf_bitwise_right lane instruction right)))).
 { apply(rf_bitwise_alu_output_history (Nat.modulo lane 3)(formal_invalid_policy(generated_observation_input inputs k)nil)(rf_bitwise_tail_window history)left(rf_bitwise_right lane instruction right)Mod LeftSize RSize).
 - intros t Bound.
 destruct t as[|t];[exact(proj1(Inputs 9247%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9248%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9249%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9254%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9255%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 destruct t as[|t];[exact(proj1(Inputs 9256%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))|].
 lia.
 - intros t Bound.
 destruct t as[|t];[exact(proj1(proj2(Inputs 9247%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9248%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9249%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9254%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9255%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj1(proj2(Inputs 9256%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 lia.
 - intros t Bound.
 destruct t as[|t];[exact(proj2(proj2(Inputs 9247%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9248%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9249%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9254%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9255%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 destruct t as[|t];[exact(proj2(proj2(Inputs 9256%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))))|].
 lia.
 - intros t Bound. do 10(destruct t as[|t];[apply Steps;vm_compute;lia|]);lia. }
 unfold rf_bitwise_word in Out. rewrite Nat.mod_mod in Out;[exact Out|lia].
Qed.
