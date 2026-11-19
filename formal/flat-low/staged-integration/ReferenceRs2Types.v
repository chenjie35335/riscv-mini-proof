Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate CoreSocModel ComparisonNodes ReferenceControlExpressions ReferenceControlNodeCongruence0 ReferenceControlNodeCongruence1 ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceRedirectSpine FormalSuccessfulNodeEvaluation SelectedNodeSafety FormalTypedNodeEquation ScalarSinkTypes DUTRedirectDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ReferenceImmediateTypes.
(* Generated rs2 type DAG. *)
Definition reference_rs2_ids : seq VarOrder.T := [::1890;1895;1900;1905;1910;1915;1920;1925;1942;1947;1952;1975;1976;1981;1982;1987;1988;1993;1994;1999;2000;2005;2006;2015;2020;2025;2030;2035;2040;2045;2050;2055;2060;2567;2568;2569;2570;2571;2572;2573;2574;2575;2576;2577;2578;2579;2580;2581;2582;2583;2584;2585;2586;2587;2588;2589;2590;2591;2592;2593;2594;2595;2596;2597;2598;2599;2600;2601;2602;2603;2604;2605;2606;2607;2608;2609;2610;2611;2612;2613;2614;2615;2616;2617;2618;2619;2620;2621;2622].
Definition reference_rs2_widths : seq nat := [::25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;31%nat;25%nat;31%nat;25%nat;31%nat;25%nat;31%nat;25%nat;31%nat;25%nat;31%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;25%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat;5%nat].
Definition reference_rs2_ranks : seq nat := [::1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;2%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;1%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;3%nat;3%nat;3%nat;3%nat;3%nat;3%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;8%nat;9%nat;10%nat;11%nat;12%nat;13%nat;14%nat;15%nat;16%nat;17%nat;18%nat;19%nat;20%nat;21%nat;22%nat;23%nat;24%nat;25%nat;26%nat;27%nat;28%nat;29%nat;30%nat;31%nat].
Definition reference_rs2_groups : seq nat := [::0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat;2%nat].
Definition reference_rs2_expressions : seq (hfexpr VarOrder.T) := [::reference_control_expr_1890;reference_control_expr_1895;reference_control_expr_1900;reference_control_expr_1905;reference_control_expr_1910;reference_control_expr_1915;reference_control_expr_1920;reference_control_expr_1925;reference_control_expr_1942;reference_control_expr_1947;reference_control_expr_1952;reference_control_expr_1975;reference_control_expr_1976;reference_control_expr_1981;reference_control_expr_1982;reference_control_expr_1987;reference_control_expr_1988;reference_control_expr_1993;reference_control_expr_1994;reference_control_expr_1999;reference_control_expr_2000;reference_control_expr_2005;reference_control_expr_2006;reference_control_expr_2015;reference_control_expr_2020;reference_control_expr_2025;reference_control_expr_2030;reference_control_expr_2035;reference_control_expr_2040;reference_control_expr_2045;reference_control_expr_2050;reference_control_expr_2055;reference_control_expr_2060;reference_control_expr_2567;reference_control_expr_2568;reference_control_expr_2569;reference_control_expr_2570;reference_control_expr_2571;reference_control_expr_2572;reference_control_expr_2573;reference_control_expr_2574;reference_control_expr_2575;reference_control_expr_2576;reference_control_expr_2577;reference_control_expr_2578;reference_control_expr_2579;reference_control_expr_2580;reference_control_expr_2581;reference_control_expr_2582;reference_control_expr_2583;reference_control_expr_2584;reference_control_expr_2585;reference_control_expr_2586;reference_control_expr_2587;reference_control_expr_2588;reference_control_expr_2589;reference_control_expr_2590;reference_control_expr_2591;reference_control_expr_2592;reference_control_expr_2593;reference_control_expr_2594;reference_control_expr_2595;reference_control_expr_2596;reference_control_expr_2597;reference_control_expr_2598;reference_control_expr_2599;reference_control_expr_2600;reference_control_expr_2601;reference_control_expr_2602;reference_control_expr_2603;reference_control_expr_2604;reference_control_expr_2605;reference_control_expr_2606;reference_control_expr_2607;reference_control_expr_2608;reference_control_expr_2609;reference_control_expr_2610;reference_control_expr_2611;reference_control_expr_2612;reference_control_expr_2613;reference_control_expr_2614;reference_control_expr_2615;reference_control_expr_2616;reference_control_expr_2617;reference_control_expr_2618;reference_control_expr_2619;reference_control_expr_2620;reference_control_expr_2621;reference_control_expr_2622].
Definition reference_rs2_dependencies : seq (seq VarOrder.T) := [::[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1975];[::1884];[::1981];[::1884];[::1987];[::1884];[::1993];[::1884];[::1999];[::1884];[::2005];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1884];[::1890];[::1895];[::1900];[::1905];[::1910];[::1915];[::1920];[::1925];[::1942];[::1947];[::1952];[::1976];[::1982];[::1988];[::1994];[::2000];[::2006];[::2015];[::2020];[::2025];[::2030];[::2035];[::2040];[::2045];[::2050];[::2055];[::2060];[::2593];[::2592;2594];[::2591;2595];[::2590;2596];[::2589;2597];[::2588;2598];[::2587;2599];[::2586;2600];[::2585;2601];[::2584;2602];[::2583;2603];[::2582;2604];[::2581;2605];[::2580;2606];[::2579;2607];[::2578;2608];[::2577;2609];[::2576;2610];[::2575;2611];[::2574;2612];[::2573;2613];[::2572;2614];[::2571;2615];[::2570;2616];[::2569;2617];[::2568;2618];[::2567;2619];[::2620];[::2621]].
Definition reference_rs2_node i := nth 0 reference_rs2_ids i.
Definition reference_rs2_width i := nth 0%nat reference_rs2_widths i.
Definition reference_rs2_rank i := nth 0%nat reference_rs2_ranks i.
Definition reference_rs2_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) reference_rs2_expressions i.
Definition reference_rs2_refs i := nth [::] reference_rs2_dependencies i.
Definition reference_rs2_width_of node := if node == 1884 then 32%nat else reference_rs2_width (index node reference_rs2_ids).
Definition reference_rs2_nodes i := match nth 2%nat reference_rs2_groups i with O => reference_control_0_nodes | S O => reference_control_1_nodes | _ => reference_control_2_nodes end.
Definition reference_rs2_offsets i := match nth 2%nat reference_rs2_groups i with O => reference_control_0_offsets | S O => reference_control_1_offsets | _ => reference_control_2_offsets end.
Lemma reference_rs2_plan i : (i < 89)%coq_nat ->
 immediate_expression_check reference_rs2_width_of (reference_rs2_expression i) = Some (reference_rs2_width i,reference_rs2_refs i) /\ (0 < reference_rs2_rank i)%coq_nat.
Proof. intro Bound. do 89 (destruct i as [|i];[split;[vm_compute;reflexivity|vm_compute;lia]|]);lia. Qed.
Lemma reference_rs2_member i : (i < 89)%coq_nat ->
 List.In (reference_rs2_node i,reference_rs2_expression i) (reference_rs2_nodes i).
Proof. intro Bound.
 destruct i as [|i];[exact reference_control_member_1890|].
 destruct i as [|i];[exact reference_control_member_1895|].
 destruct i as [|i];[exact reference_control_member_1900|].
 destruct i as [|i];[exact reference_control_member_1905|].
 destruct i as [|i];[exact reference_control_member_1910|].
 destruct i as [|i];[exact reference_control_member_1915|].
 destruct i as [|i];[exact reference_control_member_1920|].
 destruct i as [|i];[exact reference_control_member_1925|].
 destruct i as [|i];[exact reference_control_member_1942|].
 destruct i as [|i];[exact reference_control_member_1947|].
 destruct i as [|i];[exact reference_control_member_1952|].
 destruct i as [|i];[exact reference_control_member_1975|].
 destruct i as [|i];[exact reference_control_member_1976|].
 destruct i as [|i];[exact reference_control_member_1981|].
 destruct i as [|i];[exact reference_control_member_1982|].
 destruct i as [|i];[exact reference_control_member_1987|].
 destruct i as [|i];[exact reference_control_member_1988|].
 destruct i as [|i];[exact reference_control_member_1993|].
 destruct i as [|i];[exact reference_control_member_1994|].
 destruct i as [|i];[exact reference_control_member_1999|].
 destruct i as [|i];[exact reference_control_member_2000|].
 destruct i as [|i];[exact reference_control_member_2005|].
 destruct i as [|i];[exact reference_control_member_2006|].
 destruct i as [|i];[exact reference_control_member_2015|].
 destruct i as [|i];[exact reference_control_member_2020|].
 destruct i as [|i];[exact reference_control_member_2025|].
 destruct i as [|i];[exact reference_control_member_2030|].
 destruct i as [|i];[exact reference_control_member_2035|].
 destruct i as [|i];[exact reference_control_member_2040|].
 destruct i as [|i];[exact reference_control_member_2045|].
 destruct i as [|i];[exact reference_control_member_2050|].
 destruct i as [|i];[exact reference_control_member_2055|].
 destruct i as [|i];[exact reference_control_member_2060|].
 destruct i as [|i];[exact reference_control_member_2567|].
 destruct i as [|i];[exact reference_control_member_2568|].
 destruct i as [|i];[exact reference_control_member_2569|].
 destruct i as [|i];[exact reference_control_member_2570|].
 destruct i as [|i];[exact reference_control_member_2571|].
 destruct i as [|i];[exact reference_control_member_2572|].
 destruct i as [|i];[exact reference_control_member_2573|].
 destruct i as [|i];[exact reference_control_member_2574|].
 destruct i as [|i];[exact reference_control_member_2575|].
 destruct i as [|i];[exact reference_control_member_2576|].
 destruct i as [|i];[exact reference_control_member_2577|].
 destruct i as [|i];[exact reference_control_member_2578|].
 destruct i as [|i];[exact reference_control_member_2579|].
 destruct i as [|i];[exact reference_control_member_2580|].
 destruct i as [|i];[exact reference_control_member_2581|].
 destruct i as [|i];[exact reference_control_member_2582|].
 destruct i as [|i];[exact reference_control_member_2583|].
 destruct i as [|i];[exact reference_control_member_2584|].
 destruct i as [|i];[exact reference_control_member_2585|].
 destruct i as [|i];[exact reference_control_member_2586|].
 destruct i as [|i];[exact reference_control_member_2587|].
 destruct i as [|i];[exact reference_control_member_2588|].
 destruct i as [|i];[exact reference_control_member_2589|].
 destruct i as [|i];[exact reference_control_member_2590|].
 destruct i as [|i];[exact reference_control_member_2591|].
 destruct i as [|i];[exact reference_control_member_2592|].
 destruct i as [|i];[exact reference_control_member_2593|].
 destruct i as [|i];[exact reference_control_member_2594|].
 destruct i as [|i];[exact reference_control_member_2595|].
 destruct i as [|i];[exact reference_control_member_2596|].
 destruct i as [|i];[exact reference_control_member_2597|].
 destruct i as [|i];[exact reference_control_member_2598|].
 destruct i as [|i];[exact reference_control_member_2599|].
 destruct i as [|i];[exact reference_control_member_2600|].
 destruct i as [|i];[exact reference_control_member_2601|].
 destruct i as [|i];[exact reference_control_member_2602|].
 destruct i as [|i];[exact reference_control_member_2603|].
 destruct i as [|i];[exact reference_control_member_2604|].
 destruct i as [|i];[exact reference_control_member_2605|].
 destruct i as [|i];[exact reference_control_member_2606|].
 destruct i as [|i];[exact reference_control_member_2607|].
 destruct i as [|i];[exact reference_control_member_2608|].
 destruct i as [|i];[exact reference_control_member_2609|].
 destruct i as [|i];[exact reference_control_member_2610|].
 destruct i as [|i];[exact reference_control_member_2611|].
 destruct i as [|i];[exact reference_control_member_2612|].
 destruct i as [|i];[exact reference_control_member_2613|].
 destruct i as [|i];[exact reference_control_member_2614|].
 destruct i as [|i];[exact reference_control_member_2615|].
 destruct i as [|i];[exact reference_control_member_2616|].
 destruct i as [|i];[exact reference_control_member_2617|].
 destruct i as [|i];[exact reference_control_member_2618|].
 destruct i as [|i];[exact reference_control_member_2619|].
 destruct i as [|i];[exact reference_control_member_2620|].
 destruct i as [|i];[exact reference_control_member_2621|].
 destruct i as [|i];[exact reference_control_member_2622|].
 lia.
Qed.
Lemma reference_rs2_predecessors i node : (i < 89)%coq_nat -> List.In node (reference_rs2_refs i) ->
 node = 1884 \/ exists j, (j < i)%coq_nat /\ (j < 89)%coq_nat /\ reference_rs2_node j = node /\ reference_rs2_width_of node = reference_rs2_width j /\ (reference_rs2_rank j < reference_rs2_rank i)%coq_nat.
Proof.
 intro Bound.
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 11%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 13%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 17%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 19%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 21%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - left;reflexivity.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 0%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 2%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 4%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 5%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 7%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 8%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 14%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 16%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 22%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 23%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 24%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 26%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 27%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 28%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 29%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 30%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 31%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 32%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 59%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 58%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 60%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 57%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 61%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 56%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 62%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 55%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 63%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 54%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 64%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 53%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 65%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 52%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 66%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 51%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 67%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 50%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 68%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 49%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 69%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 48%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 70%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 47%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 71%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 46%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 72%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 45%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 73%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 44%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 74%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 43%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 75%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 42%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 76%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 41%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 77%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 40%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 78%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 39%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 79%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 38%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 80%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 37%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 81%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 36%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 82%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 83%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 34%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 84%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 33%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as [<-|Member].
 - right;exists 85%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 86%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as [|i].
 { cbn [reference_rs2_refs reference_rs2_dependencies nth List.In].
 intro Member.
 destruct Member as [<-|Member].
 - right;exists 87%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 lia.
Qed.
Theorem reference_rs2_node_type_step i invalid old result : (i < 89)%coq_nat ->
 (forall site value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (reference_rs2_expression i) old old = Some value -> type_of_val value = Gtyp (Fuint (reference_rs2_width i))) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (reference_rs2_node i) result = Some value /\ type_of_val value = Gtyp (Fuint (reference_rs2_width i)).
Proof.
 intros Bound Shape Step.
 assert (Position : select_node_offsets (reference_rs2_offsets i) flat_statements = Some (reference_rs2_nodes i)).
 { unfold reference_rs2_offsets,reference_rs2_nodes;destruct (nth 2%nat reference_rs2_groups i) as [|[|g]];[exact reference_control_0_positions|exact reference_control_1_positions|exact reference_control_2_positions]. }
 assert (Safety : selected_node_safety flat_memories flat_statements (reference_rs2_offsets i) flat_statements = true).
 { unfold reference_rs2_offsets;destruct (nth 2%nat reference_rs2_groups i) as [|[|g]];[exact reference_control_0_safety|exact reference_control_1_safety|exact reference_control_2_safety]. }
 destruct (selected_node_safe_position flat_memories flat_statements (reference_rs2_offsets i) flat_statements (reference_rs2_nodes i) _ _ Position Safety (reference_rs2_member i Bound)) as [count [tail [Pos [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Pos Step) as [value Eval]. rewrite add0n in Eval.
 exists value. split;[eapply formal_combinational_known_node;[exact Pos|exact Safe|exact Nonreg|exact Eval|eapply Shape;exact Eval|exact Step]|eapply Shape;exact Eval].
Qed.
Theorem reference_rs2_types_history invalid history limit start :
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (forall t, (start <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find 1884 (history t) = Some value /\ type_of_val value = Gtyp (Fuint 32)) ->
 forall i, (i < 89)%coq_nat -> forall t, (Nat.add start (reference_rs2_rank i) <= t)%coq_nat -> (t <= limit)%coq_nat ->
 exists value, VM.find (reference_rs2_node i) (history t) = Some value /\ type_of_val value = Gtyp (Fuint (reference_rs2_width i)).
Proof.
 intros Steps Source i. induction i using lt_wf_ind. intros Bound [|t] Lower Upper.
 - pose proof (proj2 (reference_rs2_plan i Bound));lia.
 - eapply reference_rs2_node_type_step;[exact Bound| |apply Steps;lia].
   intros site value Eval. eapply immediate_expression_check_sound;[exact (proj1 (reference_rs2_plan i Bound))| |exact Eval].
   intros node Member. destruct (reference_rs2_predecessors i node Bound Member) as [->|[j [Before [J [Node [Width Rank]]]]]].
   + change (exists value, VM.find 1884 (history t) = Some value /\ type_of_val value = Gtyp (Fuint 32)).
     apply Source;[pose proof (proj2 (reference_rs2_plan i Bound));lia|lia].
   + rewrite Width. rewrite <- Node. apply (H j Before J t);lia.
Qed.
