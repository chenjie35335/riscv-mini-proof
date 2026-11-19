Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceLoadSemantics DUTRedirectDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_alignment_rows : seq (seq VarOrder.T) := [::[::1887;2210;2553;2554;2555;2556;2557;2558;2559;2560;2561;2562;2563;2564;2565];[::2635;2636;2637;2638;2639;2640;2641;2642;2643;2644;2645;2646;2647;2648;2649];[::2650;2651;2652;2653;2654;2655;2656;2657;2658;2659;2660;2661;2662;2663;2664];[::2665;2666;2667;2668;2669;2670;2671;2672;2673;2674;2675;2676;2677;2678;2679];[::2694;2695;2696;2697;2698;2699;2700;2701;2702;2703;2704;2705;2706;2707;2708];[::2709;2710;2711;2712;2713;2714;2715;2716;2717;2718;2719;2720;2721;2722;2723]].
Definition reference_alignment_expressions : seq (seq (hfexpr VarOrder.T)) := [::[::reference_control_expr_1887;reference_control_expr_2210;reference_control_expr_2553;reference_control_expr_2554;reference_control_expr_2555;reference_control_expr_2556;reference_control_expr_2557;reference_control_expr_2558;reference_control_expr_2559;reference_control_expr_2560;reference_control_expr_2561;reference_control_expr_2562;reference_control_expr_2563;reference_control_expr_2564;reference_control_expr_2565];[::reference_control_expr_2635;reference_control_expr_2636;reference_control_expr_2637;reference_control_expr_2638;reference_control_expr_2639;reference_control_expr_2640;reference_control_expr_2641;reference_control_expr_2642;reference_control_expr_2643;reference_control_expr_2644;reference_control_expr_2645;reference_control_expr_2646;reference_control_expr_2647;reference_control_expr_2648;reference_control_expr_2649];[::reference_control_expr_2650;reference_control_expr_2651;reference_control_expr_2652;reference_control_expr_2653;reference_control_expr_2654;reference_control_expr_2655;reference_control_expr_2656;reference_control_expr_2657;reference_control_expr_2658;reference_control_expr_2659;reference_control_expr_2660;reference_control_expr_2661;reference_control_expr_2662;reference_control_expr_2663;reference_control_expr_2664];[::reference_control_expr_2665;reference_control_expr_2666;reference_control_expr_2667;reference_control_expr_2668;reference_control_expr_2669;reference_control_expr_2670;reference_control_expr_2671;reference_control_expr_2672;reference_control_expr_2673;reference_control_expr_2674;reference_control_expr_2675;reference_control_expr_2676;reference_control_expr_2677;reference_control_expr_2678;reference_control_expr_2679];[::reference_control_expr_2694;reference_control_expr_2695;reference_control_expr_2696;reference_control_expr_2697;reference_control_expr_2698;reference_control_expr_2699;reference_control_expr_2700;reference_control_expr_2701;reference_control_expr_2702;reference_control_expr_2703;reference_control_expr_2704;reference_control_expr_2705;reference_control_expr_2706;reference_control_expr_2707;reference_control_expr_2708];[::reference_control_expr_2709;reference_control_expr_2710;reference_control_expr_2711;reference_control_expr_2712;reference_control_expr_2713;reference_control_expr_2714;reference_control_expr_2715;reference_control_expr_2716;reference_control_expr_2717;reference_control_expr_2718;reference_control_expr_2719;reference_control_expr_2720;reference_control_expr_2721;reference_control_expr_2722;reference_control_expr_2723]].
Definition reference_alignment_node lane stage := nth 0 (nth [::] reference_alignment_rows lane) stage.
Definition reference_alignment_expression lane stage := nth (@Econst VarOrder.T (Fuint 1) [::false]) (nth [::] reference_alignment_expressions lane) stage.
Definition reference_alignment_group lane stage := if Nat.eqb lane 0 then if Nat.eqb stage 0 then 0%nat else if Nat.eqb stage 1 then 1%nat else 2%nat else 2%nat.
Definition reference_alignment_nodes lane stage := match reference_alignment_group lane stage with O => reference_control_0_nodes | S O => reference_control_1_nodes | _ => reference_control_2_nodes end.
Definition reference_alignment_offsets lane stage := match reference_alignment_group lane stage with O => reference_control_0_offsets | S O => reference_control_1_offsets | _ => reference_control_2_offsets end.
Lemma reference_alignment_member lane stage : (lane < 6)%coq_nat -> (stage < 15)%coq_nat ->
 List.In (reference_alignment_node lane stage,reference_alignment_expression lane stage) (reference_alignment_nodes lane stage).
Proof.
 intros Lane Stage.
 destruct lane as [|lane].
 {
 destruct stage as [|stage];[exact reference_control_member_1887|].
 destruct stage as [|stage];[exact reference_control_member_2210|].
 destruct stage as [|stage];[exact reference_control_member_2553|].
 destruct stage as [|stage];[exact reference_control_member_2554|].
 destruct stage as [|stage];[exact reference_control_member_2555|].
 destruct stage as [|stage];[exact reference_control_member_2556|].
 destruct stage as [|stage];[exact reference_control_member_2557|].
 destruct stage as [|stage];[exact reference_control_member_2558|].
 destruct stage as [|stage];[exact reference_control_member_2559|].
 destruct stage as [|stage];[exact reference_control_member_2560|].
 destruct stage as [|stage];[exact reference_control_member_2561|].
 destruct stage as [|stage];[exact reference_control_member_2562|].
 destruct stage as [|stage];[exact reference_control_member_2563|].
 destruct stage as [|stage];[exact reference_control_member_2564|].
 destruct stage as [|stage];[exact reference_control_member_2565|].
 lia. }
 destruct lane as [|lane].
 {
 destruct stage as [|stage];[exact reference_control_member_2635|].
 destruct stage as [|stage];[exact reference_control_member_2636|].
 destruct stage as [|stage];[exact reference_control_member_2637|].
 destruct stage as [|stage];[exact reference_control_member_2638|].
 destruct stage as [|stage];[exact reference_control_member_2639|].
 destruct stage as [|stage];[exact reference_control_member_2640|].
 destruct stage as [|stage];[exact reference_control_member_2641|].
 destruct stage as [|stage];[exact reference_control_member_2642|].
 destruct stage as [|stage];[exact reference_control_member_2643|].
 destruct stage as [|stage];[exact reference_control_member_2644|].
 destruct stage as [|stage];[exact reference_control_member_2645|].
 destruct stage as [|stage];[exact reference_control_member_2646|].
 destruct stage as [|stage];[exact reference_control_member_2647|].
 destruct stage as [|stage];[exact reference_control_member_2648|].
 destruct stage as [|stage];[exact reference_control_member_2649|].
 lia. }
 destruct lane as [|lane].
 {
 destruct stage as [|stage];[exact reference_control_member_2650|].
 destruct stage as [|stage];[exact reference_control_member_2651|].
 destruct stage as [|stage];[exact reference_control_member_2652|].
 destruct stage as [|stage];[exact reference_control_member_2653|].
 destruct stage as [|stage];[exact reference_control_member_2654|].
 destruct stage as [|stage];[exact reference_control_member_2655|].
 destruct stage as [|stage];[exact reference_control_member_2656|].
 destruct stage as [|stage];[exact reference_control_member_2657|].
 destruct stage as [|stage];[exact reference_control_member_2658|].
 destruct stage as [|stage];[exact reference_control_member_2659|].
 destruct stage as [|stage];[exact reference_control_member_2660|].
 destruct stage as [|stage];[exact reference_control_member_2661|].
 destruct stage as [|stage];[exact reference_control_member_2662|].
 destruct stage as [|stage];[exact reference_control_member_2663|].
 destruct stage as [|stage];[exact reference_control_member_2664|].
 lia. }
 destruct lane as [|lane].
 {
 destruct stage as [|stage];[exact reference_control_member_2665|].
 destruct stage as [|stage];[exact reference_control_member_2666|].
 destruct stage as [|stage];[exact reference_control_member_2667|].
 destruct stage as [|stage];[exact reference_control_member_2668|].
 destruct stage as [|stage];[exact reference_control_member_2669|].
 destruct stage as [|stage];[exact reference_control_member_2670|].
 destruct stage as [|stage];[exact reference_control_member_2671|].
 destruct stage as [|stage];[exact reference_control_member_2672|].
 destruct stage as [|stage];[exact reference_control_member_2673|].
 destruct stage as [|stage];[exact reference_control_member_2674|].
 destruct stage as [|stage];[exact reference_control_member_2675|].
 destruct stage as [|stage];[exact reference_control_member_2676|].
 destruct stage as [|stage];[exact reference_control_member_2677|].
 destruct stage as [|stage];[exact reference_control_member_2678|].
 destruct stage as [|stage];[exact reference_control_member_2679|].
 lia. }
 destruct lane as [|lane].
 {
 destruct stage as [|stage];[exact reference_control_member_2694|].
 destruct stage as [|stage];[exact reference_control_member_2695|].
 destruct stage as [|stage];[exact reference_control_member_2696|].
 destruct stage as [|stage];[exact reference_control_member_2697|].
 destruct stage as [|stage];[exact reference_control_member_2698|].
 destruct stage as [|stage];[exact reference_control_member_2699|].
 destruct stage as [|stage];[exact reference_control_member_2700|].
 destruct stage as [|stage];[exact reference_control_member_2701|].
 destruct stage as [|stage];[exact reference_control_member_2702|].
 destruct stage as [|stage];[exact reference_control_member_2703|].
 destruct stage as [|stage];[exact reference_control_member_2704|].
 destruct stage as [|stage];[exact reference_control_member_2705|].
 destruct stage as [|stage];[exact reference_control_member_2706|].
 destruct stage as [|stage];[exact reference_control_member_2707|].
 destruct stage as [|stage];[exact reference_control_member_2708|].
 lia. }
 destruct lane as [|lane].
 {
 destruct stage as [|stage];[exact reference_control_member_2709|].
 destruct stage as [|stage];[exact reference_control_member_2710|].
 destruct stage as [|stage];[exact reference_control_member_2711|].
 destruct stage as [|stage];[exact reference_control_member_2712|].
 destruct stage as [|stage];[exact reference_control_member_2713|].
 destruct stage as [|stage];[exact reference_control_member_2714|].
 destruct stage as [|stage];[exact reference_control_member_2715|].
 destruct stage as [|stage];[exact reference_control_member_2716|].
 destruct stage as [|stage];[exact reference_control_member_2717|].
 destruct stage as [|stage];[exact reference_control_member_2718|].
 destruct stage as [|stage];[exact reference_control_member_2719|].
 destruct stage as [|stage];[exact reference_control_member_2720|].
 destruct stage as [|stage];[exact reference_control_member_2721|].
 destruct stage as [|stage];[exact reference_control_member_2722|].
 destruct stage as [|stage];[exact reference_control_member_2723|].
 lia. }
 lia.
Qed.
Theorem reference_alignment_node_step invalid old result lane stage ground word :
 (lane < 6)%coq_nat -> (stage < 15)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (reference_alignment_expression lane stage) old old = Some (Gval ground word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (reference_alignment_node lane stage) result = Some (Gval ground word).
Proof.
 intros Lane Stage Eval Step.
 eapply (reference_redirect_ground_step (reference_alignment_offsets lane stage) (reference_alignment_nodes lane stage) _ (reference_alignment_expression lane stage));
 [unfold reference_alignment_offsets,reference_alignment_nodes;destruct (reference_alignment_group lane stage) as [|[|group]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]
 |unfold reference_alignment_offsets;destruct (reference_alignment_group lane stage) as [|[|group]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]
 |apply reference_alignment_member;assumption|exact Eval|exact Step].
Qed.
Definition reference_alignment_test lane b0 b1 := if Nat.eqb lane 3 then true else if Nat.eqb lane 1 || Nat.eqb lane 4 then negb (b0 || b1) else negb b0.
Theorem reference_alignment_guard_history invalid history limit start lane b0 b1 b2 rest :
 (lane < 6)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find (reference_alignment_node lane 3) (history i) = Some (Gval (Fuint 32) (b0::b1::b2::rest))) ->
 forall time, (Nat.add start 15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (reference_alignment_node lane 14) (history time) = Some (Gval (Fuint 1) [::reference_alignment_test lane b0 b1]).
Proof.
 intros Lane Steps Address.
 assert (V0 : forall time, (Nat.add start 1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 0) (history time) = Some (Gval (Fuint 1) ([::false]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_1887 reference_control_expr_2635 reference_control_expr_2650 reference_control_expr_2665 reference_control_expr_2694 reference_control_expr_2709 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V4 : forall time, (Nat.add start 5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 4) (history time) = Some (Gval (Fuint 3) ([::b0;b1;b2]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (Address time ltac:(lia) ltac:(lia)) as HAddress.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2555 reference_control_expr_2639 reference_control_expr_2654 reference_control_expr_2669 reference_control_expr_2698 reference_control_expr_2713 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HAddress;
 rewrite HAddress;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HAddress;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V5 : forall time, (Nat.add start 6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 5) (history time) = Some (Gval (Fuint 1) ([::negb (b0 || b1 || b2)]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (V4 time ltac:(lia) ltac:(lia)) as HV4.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2556 reference_control_expr_2640 reference_control_expr_2655 reference_control_expr_2670 reference_control_expr_2699 reference_control_expr_2714 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HV4;
 rewrite HV4;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HV4;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V6 : forall time, (Nat.add start 7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 6) (history time) = Some (Gval (Fuint 1) ([::Nat.eqb lane 1 || Nat.eqb lane 4]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2557 reference_control_expr_2641 reference_control_expr_2656 reference_control_expr_2671 reference_control_expr_2700 reference_control_expr_2715 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V7 : forall time, (Nat.add start 8 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 7) (history time) = Some (Gval (Fuint 2) ([::b0;b1]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (Address time ltac:(lia) ltac:(lia)) as HAddress.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2558 reference_control_expr_2642 reference_control_expr_2657 reference_control_expr_2672 reference_control_expr_2701 reference_control_expr_2716 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HAddress;
 rewrite HAddress;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HAddress;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V8 : forall time, (Nat.add start 9 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 8) (history time) = Some (Gval (Fuint 1) ([::negb (b0 || b1)]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (V7 time ltac:(lia) ltac:(lia)) as HV7.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2559 reference_control_expr_2643 reference_control_expr_2658 reference_control_expr_2673 reference_control_expr_2702 reference_control_expr_2717 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HV7;
 rewrite HV7;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HV7;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V9 : forall time, (Nat.add start 10 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 9) (history time) = Some (Gval (Fuint 1) ([::negb (Nat.eqb lane 1 || Nat.eqb lane 3 || Nat.eqb lane 4)]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2560 reference_control_expr_2644 reference_control_expr_2659 reference_control_expr_2674 reference_control_expr_2703 reference_control_expr_2718 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V10 : forall time, (Nat.add start 11 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 10) (history time) = Some (Gval (Fuint 1) ([::b0]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (Address time ltac:(lia) ltac:(lia)) as HAddress.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2561 reference_control_expr_2645 reference_control_expr_2660 reference_control_expr_2675 reference_control_expr_2704 reference_control_expr_2719 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HAddress;
 rewrite HAddress;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HAddress;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V11 : forall time, (Nat.add start 12 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 11) (history time) = Some (Gval (Fuint 1) ([::negb b0]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (V10 time ltac:(lia) ltac:(lia)) as HV10.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2562 reference_control_expr_2646 reference_control_expr_2661 reference_control_expr_2676 reference_control_expr_2705 reference_control_expr_2720 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HV10;
 rewrite HV10;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HV10;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V12 : forall time, (Nat.add start 13 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 12) (history time) = Some (Gval (Fuint 1) ([::if Nat.eqb lane 1 || Nat.eqb lane 3 || Nat.eqb lane 4 then true else negb b0]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (V9 time ltac:(lia) ltac:(lia)) as HV9.
 pose proof (V11 time ltac:(lia) ltac:(lia)) as HV11.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2563 reference_control_expr_2647 reference_control_expr_2662 reference_control_expr_2677 reference_control_expr_2706 reference_control_expr_2721 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HV9,HV11;
 rewrite HV9 HV11;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HV9 ?HV11;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V13 : forall time, (Nat.add start 14 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 13) (history time) = Some (Gval (Fuint 1) ([::reference_alignment_test lane b0 b1]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (V6 time ltac:(lia) ltac:(lia)) as HV6.
 pose proof (V8 time ltac:(lia) ltac:(lia)) as HV8.
 pose proof (V12 time ltac:(lia) ltac:(lia)) as HV12.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2564 reference_control_expr_2648 reference_control_expr_2663 reference_control_expr_2678 reference_control_expr_2707 reference_control_expr_2722 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HV6,HV8,HV12;
 rewrite HV6 HV8 HV12;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HV6 ?HV8 ?HV12;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 assert (V14 : forall time, (Nat.add start 15 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find (reference_alignment_node lane 14) (history time) = Some (Gval (Fuint 1) ([::reference_alignment_test lane b0 b1]))).
 { intros [|time] Lower Upper;try lia. eapply reference_alignment_node_step;[exact Lane|lia| |apply Steps;lia].
 intro site.
 pose proof (V0 time ltac:(lia) ltac:(lia)) as HV0.
 pose proof (V5 time ltac:(lia) ltac:(lia)) as HV5.
 pose proof (V13 time ltac:(lia) ltac:(lia)) as HV13.
 do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth] ;
 cbn [reference_control_expr_2565 reference_control_expr_2649 reference_control_expr_2664 reference_control_expr_2679 reference_control_expr_2708 reference_control_expr_2723 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref];
 cbn [reference_alignment_node reference_alignment_rows nth] in HV0,HV5,HV13;
 rewrite HV0 HV5 HV13;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?HV0 ?HV5 ?HV13;
 destruct b0,b1,b2,rest;reflexivity|]);lia. }
 intros time Lower Upper. exact (V14 time Lower Upper).
Qed.
(* Alignment address and observed interfaces. *)
Theorem reference_alignment_address_history invalid s0 s1 s2 s3 lane rs1 immediate :
 (lane < 6)%coq_nat -> VM.find 2209 s0 = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 s1 = Some (Gval (Fuint 32) immediate) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find (reference_alignment_node lane 3) s3 = Some (Gval (Fuint 32) (reference_load_address rs1 immediate)).
Proof.
 intros Lane Rs1 Imm S1 S2 S3.
 assert (A : VM.find (reference_alignment_node lane 1) s1 = Some (Gval (Fuint 32) rs1)).
 { eapply reference_alignment_node_step;[exact Lane|lia| |exact S1].
   intro site. do 6 (destruct lane as [|lane];[exact Rs1|]);lia. }
 assert (B : VM.find (reference_alignment_node lane 2) s2 = Some (Gval (Fuint 33) (from_N 33 (to_N rs1+to_N immediate)))).
 { eapply reference_alignment_node_step;[exact Lane|lia| |exact S2].
   intro site. do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth];
   cbn [reference_control_expr_2553 reference_control_expr_2637 reference_control_expr_2652 reference_control_expr_2667 reference_control_expr_2696 reference_control_expr_2711 eval_hfexpr_validif_policy eval_href_validif_policy];
   cbn [reference_alignment_node reference_alignment_rows nth] in A;rewrite A Imm;reflexivity|]);lia. }
 eapply reference_alignment_node_step;[exact Lane|lia| |exact S3].
 intro site. do 6 (destruct lane as [|lane];[cbn [reference_alignment_expression reference_alignment_expressions nth];
 cbn [reference_control_expr_2554 reference_control_expr_2638 reference_control_expr_2653 reference_control_expr_2668 reference_control_expr_2697 reference_control_expr_2712 eval_hfexpr_validif_policy eval_href_validif_policy];
 cbn [reference_alignment_node reference_alignment_rows nth] in B;rewrite B;reflexivity|]);lia.
Qed.
Require Import ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory.
Theorem reference_alignment_observed memory inputs k observed lane rs1 immediate :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 6)%coq_nat ->
 VM.find 2209 (top_environment observed) = Some (Gval (Fuint 32) rs1) ->
 VM.find 2552 (top_environment observed) = Some (Gval (Fuint 32) immediate) ->
 VM.find (reference_alignment_node lane 14) (top_environment observed) = Some (Gval (Fuint 1)
 [::reference_alignment_test lane (nth false (reference_load_address rs1 immediate) 0) (nth false (reference_load_address rs1 immediate) 1)]).
Proof.
 intros Observe Legal Lane Rs1 Imm.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (R : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 2209 (history t) = Some (Gval (Fuint 32) rs1)).
 { intros t Lower Upper. rewrite (reference_control_stable_2209_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Rs1. }
 assert (I : forall t, (200 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find 2552 (history t) = Some (Gval (Fuint 32) immediate)).
 { intros t Lower Upper. rewrite (reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259%nat ltac:(lia) ltac:(lia) Upper ltac:(lia)) Last. exact Imm. }
 assert (A : forall t, (203 <= t)%coq_nat -> (t <= 9259)%coq_nat -> VM.find (reference_alignment_node lane 3) (history t) = Some (Gval (Fuint 32) (reference_load_address rs1 immediate))).
 { intros [|[|[|t]]] Lower Upper;try lia.
   eapply (reference_alignment_address_history _ (history t) (history (S t)) (history (S (S t))) (history (S (S (S t)))));[exact Lane|apply R;lia|apply I;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia]. }
 remember (reference_load_address rs1 immediate) as address eqn:Address.
 assert (Size : size address = 32%nat).
 { rewrite Address. unfold reference_load_address. rewrite size_take size_from_N. reflexivity. }
 destruct address as [|b0 [|b1 [|b2 rest]]];cbn in Size;try lia.
 rewrite <- Last.
 exact (reference_alignment_guard_history _ history 9259 203 lane b0 b1 b2 rest Lane Steps A 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia)).
Qed.
