Require Import RFShiftALUHistory RFShiftCycle RFShiftSemantics RFReferenceWriteEffect CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_ref_shift_expr_3450:=(@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_ref_shift_expr_3451:=(@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 3450))).
Definition rf_ref_shift_expr_3452:=(@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_ref_shift_expr_3453:=(@Eprim_unop VarOrder.T (Uextr 4 0) (@Eref VarOrder.T (@Eid VarOrder.T 3452))).
Definition rf_ref_shift_expr_3454:=(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3451)) (@Eref VarOrder.T (@Eid VarOrder.T 3453))).
Definition rf_ref_shift_expr_3455:=(@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 3454))).
Definition rf_ref_shift_expr_3456:=(@Eref VarOrder.T (@Eid VarOrder.T 3455)).
Definition rf_ref_shift_expr_3462:=(@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_ref_shift_expr_3463:=(@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_ref_shift_expr_3464:=(@Eprim_unop VarOrder.T (Uextr 4 0) (@Eref VarOrder.T (@Eid VarOrder.T 3463))).
Definition rf_ref_shift_expr_3465:=(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3462)) (@Eref VarOrder.T (@Eid VarOrder.T 3464))).
Definition rf_ref_shift_expr_3466:=(@Eref VarOrder.T (@Eid VarOrder.T 3465)).
Definition rf_ref_shift_expr_3467:=(@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_ref_shift_expr_3468:=(@Eref VarOrder.T (@Eid VarOrder.T 2804)).
Definition rf_ref_shift_expr_3469:=(@Eprim_unop VarOrder.T (Uextr 4 0) (@Eref VarOrder.T (@Eid VarOrder.T 3468))).
Definition rf_ref_shift_expr_3470:=(@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 3467)) (@Eref VarOrder.T (@Eid VarOrder.T 3469))).
Definition rf_ref_shift_expr_3471:=(@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 3470))).
Definition rf_ref_shift_expr_3505:=(@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_ref_shift_expr_3506:=(@Ecast VarOrder.T AsSInt (@Eref VarOrder.T (@Eid VarOrder.T 3505))).
Definition rf_ref_shift_expr_3507:=(@Eprim_unop VarOrder.T (Uextr 4 0) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_ref_shift_expr_3508:=(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3506)) (@Eref VarOrder.T (@Eid VarOrder.T 3507))).
Definition rf_ref_shift_expr_3509:=(@Ecast VarOrder.T AsUInt (@Eref VarOrder.T (@Eid VarOrder.T 3508))).
Definition rf_ref_shift_expr_3510:=(@Eref VarOrder.T (@Eid VarOrder.T 3509)).
Definition rf_ref_shift_expr_3511:=(@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_ref_shift_expr_3512:=(@Eprim_unop VarOrder.T (Uextr 4 0) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_ref_shift_expr_3513:=(@Eprim_binop VarOrder.T Bdshr (@Eref VarOrder.T (@Eid VarOrder.T 3511)) (@Eref VarOrder.T (@Eid VarOrder.T 3512))).
Definition rf_ref_shift_expr_3514:=(@Eref VarOrder.T (@Eid VarOrder.T 3513)).
Definition rf_ref_shift_expr_3515:=(@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition rf_ref_shift_expr_3516:=(@Eprim_unop VarOrder.T (Uextr 4 0) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition rf_ref_shift_expr_3517:=(@Eprim_binop VarOrder.T Bdshl (@Eref VarOrder.T (@Eid VarOrder.T 3515)) (@Eref VarOrder.T (@Eid VarOrder.T 3516))).
Definition rf_ref_shift_expr_3518:=(@Eprim_unop VarOrder.T (Uextr 31 0) (@Eref VarOrder.T (@Eid VarOrder.T 3517))).
Definition rf_ref_shift_nodes:=[::(3450,rf_ref_shift_expr_3450);(3451,rf_ref_shift_expr_3451);(3452,rf_ref_shift_expr_3452);(3453,rf_ref_shift_expr_3453);(3454,rf_ref_shift_expr_3454);(3455,rf_ref_shift_expr_3455);(3456,rf_ref_shift_expr_3456);(3462,rf_ref_shift_expr_3462);(3463,rf_ref_shift_expr_3463);(3464,rf_ref_shift_expr_3464);(3465,rf_ref_shift_expr_3465);(3466,rf_ref_shift_expr_3466);(3467,rf_ref_shift_expr_3467);(3468,rf_ref_shift_expr_3468);(3469,rf_ref_shift_expr_3469);(3470,rf_ref_shift_expr_3470);(3471,rf_ref_shift_expr_3471);(3505,rf_ref_shift_expr_3505);(3506,rf_ref_shift_expr_3506);(3507,rf_ref_shift_expr_3507);(3508,rf_ref_shift_expr_3508);(3509,rf_ref_shift_expr_3509);(3510,rf_ref_shift_expr_3510);(3511,rf_ref_shift_expr_3511);(3512,rf_ref_shift_expr_3512);(3513,rf_ref_shift_expr_3513);(3514,rf_ref_shift_expr_3514);(3515,rf_ref_shift_expr_3515);(3516,rf_ref_shift_expr_3516);(3517,rf_ref_shift_expr_3517);(3518,rf_ref_shift_expr_3518)].
Definition rf_ref_shift_offsets:=[::3529%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;5%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;33%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_ref_shift_positions:select_node_offsets rf_ref_shift_offsets flat_statements=Some rf_ref_shift_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_ref_shift_safety:selected_node_safety flat_memories flat_statements rf_ref_shift_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_ref_shift_output immediate lane :VarOrder.T:=if immediate then nth 0[::3518;3514;3510]lane else nth 0[::3471;3466;3456]lane.
Definition rf_ref_shift_word lane left right :=
 let amount:=to_nat(take 5 right)in
 match lane with O=>take 32(zext_to 63(zeros amount++left))|S O=>zext_to 32(drop amount left)|_=>sext_to 32(drop(minn amount 31)left)end.
Lemma rf_ref_shift_word_correct lane left right :(lane<3)%coq_nat ->size left=32%nat ->size right=32%nat ->
 rf_ref_shift_word lane left right=rf_shift_word(negb(Nat.eqb lane 0))(Nat.eqb lane 2)left right.
Proof.
 intros Lane Left Right. rewrite(rf_shift_word_correct _ _ _ _ Left Right).
 pose proof(to_nat_bounded(take 5 right))as Bound. rewrite size_take Right in Bound.
 assert(Small:(to_nat(take 5 right)<=31)%nat)by exact Bound.
 destruct lane as[|[|[|lane]]];try lia;unfold rf_ref_shift_word,rf_shift_spec;cbn[Nat.eqb negb].
 - unfold zext_to. rewrite rf_reference_take_extension;[reflexivity|rewrite size_cat size_zeros Left;apply leq_addl].
 - reflexivity.
 - rewrite(minn_idPl Small);reflexivity.
Qed.
Theorem rf_ref_shift_register_history invalid history limit left right :
 (forall t,(t<=limit)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 2804(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall lane t,(lane<3)%coq_nat ->(7<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find(rf_ref_shift_output false lane)(history t)=Some(Gval(Fuint 32)(rf_ref_shift_word lane left right)).
Proof.
 intros Left Right Steps.
 set(w3450:=left).
 assert(V3450:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3450(history t)=Some(Gval(Fuint 32)w3450)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3450 rf_ref_shift_expr_3450);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 0%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3450 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Left t ltac:(lia)).
 reflexivity. }
 set(w3451:=w3450).
 assert(V3451:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3451(history t)=Some(Gval(Fsint 32)w3451)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3451 rf_ref_shift_expr_3451);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 1%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3451 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3450 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3452:=right).
 assert(V3452:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3452(history t)=Some(Gval(Fuint 32)w3452)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3452 rf_ref_shift_expr_3452);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 2%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3452 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Right t ltac:(lia)).
 reflexivity. }
 set(w3453:=drop 0(take 5 w3452)).
 assert(V3453:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3453(history t)=Some(Gval(Fuint 5)w3453)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3453 rf_ref_shift_expr_3453);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 3%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3453 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3452 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3454:=sext_to 32(drop(minn(to_nat w3453)31)w3451)).
 assert(V3454:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3454(history t)=Some(Gval(Fsint 32)w3454)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3454 rf_ref_shift_expr_3454);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 4%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3454 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3451 t ltac:(lia)ltac:(lia)).
 rewrite(V3453 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3455:=w3454).
 assert(V3455:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3455(history t)=Some(Gval(Fuint 32)w3455)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3455 rf_ref_shift_expr_3455);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 5%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3455 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3454 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3456:=w3455).
 assert(V3456:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3456(history t)=Some(Gval(Fuint 32)w3456)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3456 rf_ref_shift_expr_3456);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 6%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3456 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3455 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3462:=left).
 assert(V3462:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3462(history t)=Some(Gval(Fuint 32)w3462)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3462 rf_ref_shift_expr_3462);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 7%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3462 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Left t ltac:(lia)).
 reflexivity. }
 set(w3463:=right).
 assert(V3463:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3463(history t)=Some(Gval(Fuint 32)w3463)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3463 rf_ref_shift_expr_3463);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 8%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3463 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Right t ltac:(lia)).
 reflexivity. }
 set(w3464:=drop 0(take 5 w3463)).
 assert(V3464:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3464(history t)=Some(Gval(Fuint 5)w3464)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3464 rf_ref_shift_expr_3464);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 9%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3464 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3463 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3465:=zext_to 32(drop(to_nat w3464)w3462)).
 assert(V3465:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3465(history t)=Some(Gval(Fuint 32)w3465)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3465 rf_ref_shift_expr_3465);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 10%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3465 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3462 t ltac:(lia)ltac:(lia)).
 rewrite(V3464 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3466:=w3465).
 assert(V3466:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3466(history t)=Some(Gval(Fuint 32)w3466)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3466 rf_ref_shift_expr_3466);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 11%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3466 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3465 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3467:=left).
 assert(V3467:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3467(history t)=Some(Gval(Fuint 32)w3467)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3467 rf_ref_shift_expr_3467);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 12%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3467 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Left t ltac:(lia)).
 reflexivity. }
 set(w3468:=right).
 assert(V3468:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3468(history t)=Some(Gval(Fuint 32)w3468)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3468 rf_ref_shift_expr_3468);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 13%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3468 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Right t ltac:(lia)).
 reflexivity. }
 set(w3469:=drop 0(take 5 w3468)).
 assert(V3469:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3469(history t)=Some(Gval(Fuint 5)w3469)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3469 rf_ref_shift_expr_3469);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 14%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3469 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3468 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3470:=zext_to 63(zeros(to_nat w3469)++w3467)).
 assert(V3470:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3470(history t)=Some(Gval(Fuint 63)w3470)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3470 rf_ref_shift_expr_3470);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 15%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3470 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3467 t ltac:(lia)ltac:(lia)).
 rewrite(V3469 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3471:=drop 0(take 32 w3470)).
 assert(V3471:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3471(history t)=Some(Gval(Fuint 32)w3471)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3471 rf_ref_shift_expr_3471);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 16%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3471 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3470 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 intros lane t Lane Lower Upper.
 destruct lane as[|lane]. { pose proof(V3471 t ltac:(lia)Upper)as V. unfold w3471,w3470,w3469,w3468,w3467,w3466,w3465,w3464,w3463,w3462,w3456,w3455,w3454,w3453,w3452,w3451,w3450 in V. rewrite ?drop0 in V. exact V. }
 destruct lane as[|lane]. { pose proof(V3466 t ltac:(lia)Upper)as V. unfold w3466,w3465,w3464,w3463,w3462,w3456,w3455,w3454,w3453,w3452,w3451,w3450 in V. rewrite ?drop0 in V. exact V. }
 destruct lane as[|lane]. { pose proof(V3456 t ltac:(lia)Upper)as V. unfold w3456,w3455,w3454,w3453,w3452,w3451,w3450 in V. rewrite ?drop0 in V. exact V. }
 lia.
Qed.
Theorem rf_ref_shift_immediate_history invalid history limit left right :
 (forall t,(t<=limit)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 2552(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall lane t,(lane<3)%coq_nat ->(7<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find(rf_ref_shift_output true lane)(history t)=Some(Gval(Fuint 32)(rf_ref_shift_word lane left right)).
Proof.
 intros Left Right Steps.
 set(w3505:=left).
 assert(V3505:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3505(history t)=Some(Gval(Fuint 32)w3505)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3505 rf_ref_shift_expr_3505);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 17%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3505 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Left t ltac:(lia)).
 reflexivity. }
 set(w3506:=w3505).
 assert(V3506:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3506(history t)=Some(Gval(Fsint 32)w3506)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3506 rf_ref_shift_expr_3506);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 18%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3506 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3505 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3507:=drop 0(take 5 right)).
 assert(V3507:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3507(history t)=Some(Gval(Fuint 5)w3507)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3507 rf_ref_shift_expr_3507);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 19%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3507 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Right t ltac:(lia)).
 reflexivity. }
 set(w3508:=sext_to 32(drop(minn(to_nat w3507)31)w3506)).
 assert(V3508:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3508(history t)=Some(Gval(Fsint 32)w3508)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3508 rf_ref_shift_expr_3508);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 20%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3508 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3506 t ltac:(lia)ltac:(lia)).
 rewrite(V3507 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3509:=w3508).
 assert(V3509:forall t,(4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3509(history t)=Some(Gval(Fuint 32)w3509)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3509 rf_ref_shift_expr_3509);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 21%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3509 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3508 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3510:=w3509).
 assert(V3510:forall t,(5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3510(history t)=Some(Gval(Fuint 32)w3510)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3510 rf_ref_shift_expr_3510);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 22%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3510 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3509 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3511:=left).
 assert(V3511:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3511(history t)=Some(Gval(Fuint 32)w3511)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3511 rf_ref_shift_expr_3511);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 23%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3511 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Left t ltac:(lia)).
 reflexivity. }
 set(w3512:=drop 0(take 5 right)).
 assert(V3512:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3512(history t)=Some(Gval(Fuint 5)w3512)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3512 rf_ref_shift_expr_3512);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 24%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3512 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Right t ltac:(lia)).
 reflexivity. }
 set(w3513:=zext_to 32(drop(to_nat w3512)w3511)).
 assert(V3513:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3513(history t)=Some(Gval(Fuint 32)w3513)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3513 rf_ref_shift_expr_3513);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 25%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3513 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3511 t ltac:(lia)ltac:(lia)).
 rewrite(V3512 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3514:=w3513).
 assert(V3514:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3514(history t)=Some(Gval(Fuint 32)w3514)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3514 rf_ref_shift_expr_3514);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 26%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3514 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3513 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3515:=left).
 assert(V3515:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3515(history t)=Some(Gval(Fuint 32)w3515)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3515 rf_ref_shift_expr_3515);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 27%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3515 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Left t ltac:(lia)).
 reflexivity. }
 set(w3516:=drop 0(take 5 right)).
 assert(V3516:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3516(history t)=Some(Gval(Fuint 5)w3516)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3516 rf_ref_shift_expr_3516);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 28%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3516 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Right t ltac:(lia)).
 reflexivity. }
 set(w3517:=zext_to 63(zeros(to_nat w3516)++w3515)).
 assert(V3517:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3517(history t)=Some(Gval(Fuint 63)w3517)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3517 rf_ref_shift_expr_3517);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 29%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3517 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3515 t ltac:(lia)ltac:(lia)).
 rewrite(V3516 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 set(w3518:=drop 0(take 32 w3517)).
 assert(V3518:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3518(history t)=Some(Gval(Fuint 32)w3518)).
 { intros [|t] Lower Upper;[lia|]. eapply(reference_redirect_ground_step rf_ref_shift_offsets rf_ref_shift_nodes 3518 rf_ref_shift_expr_3518);
 [exact rf_ref_shift_positions|exact rf_ref_shift_safety|apply(List.nth_error_In rf_ref_shift_nodes 30%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_ref_shift_expr_3518 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3517 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 intros lane t Lane Lower Upper.
 destruct lane as[|lane]. { pose proof(V3518 t ltac:(lia)Upper)as V. unfold w3518,w3517,w3516,w3515,w3514,w3513,w3512,w3511,w3510,w3509,w3508,w3507,w3506,w3505 in V. rewrite ?drop0 in V. exact V. }
 destruct lane as[|lane]. { pose proof(V3514 t ltac:(lia)Upper)as V. unfold w3514,w3513,w3512,w3511,w3510,w3509,w3508,w3507,w3506,w3505 in V. rewrite ?drop0 in V. exact V. }
 destruct lane as[|lane]. { pose proof(V3510 t ltac:(lia)Upper)as V. unfold w3510,w3509,w3508,w3507,w3506,w3505 in V. rewrite ?drop0 in V. exact V. }
 lia.
Qed.
Require Import FormalObservedHistory FormalLocalHistory ReferenceControlStabilityHistory.
Theorem rf_reference_shift_observed memory inputs k observed immediate lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->(lane<3)%coq_nat ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)left) ->
 VM.find(if immediate then 2552 else 2804)(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find(rf_ref_shift_output immediate lane)(top_environment observed)=Some(Gval(Fuint 32)(rf_ref_shift_word lane left right)).
Proof.
 intros Observe Legal Lane Left Right.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(L:forall t,(t<=7)%coq_nat ->VM.find 2209(history(Nat.add 9252 t))=Some(Gval(Fuint 32)left)).
 { intros t Bound. rewrite(reference_control_stable_2209_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps (Nat.add 9252 t)9259 ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia)ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall t,(t<=7)%coq_nat ->VM.find(if immediate then 2552 else 2804)(history(Nat.add 9252 t))=Some(Gval(Fuint 32)right)).
 { intros t Bound. destruct immediate.
 - rewrite(reference_control_stable_2552_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps (Nat.add 9252 t)9259 ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia)ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia))Last;exact Right.
 - rewrite(reference_control_stable_2804_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps (Nat.add 9252 t)9259 ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia)ltac:(do 8(destruct t as[|t];[vm_compute;lia|]);lia)ltac:(vm_compute;lia))Last;exact Right. }
 assert(S:forall t,(t<7)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(history(Nat.add 9252 t))false(history(Nat.add 9252 t))flat_statements=Some(history(Nat.add 9252(S t)))).
 { intros t Bound. replace(Nat.add 9252(S t))with(S(Nat.add 9252 t))by lia. apply Steps. do 7(destruct t as[|t];[vm_compute;lia|]);lia. }
 rewrite<-Last. destruct immediate.
 - exact(rf_ref_shift_immediate_history _ (fun i=>history(Nat.add 9252 i))7 left right L R S lane 7 Lane ltac:(lia)ltac:(lia)).
 - exact(rf_ref_shift_register_history _ (fun i=>history(Nat.add 9252 i))7 left right L R S lane 7 Lane ltac:(lia)ltac:(lia)).
Qed.
