Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_event_nodes := [::(6323,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2966)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::true])));(6332,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2357)) (@Eref VarOrder.T (@Eid VarOrder.T 6323)) (@Econst VarOrder.T (Fuint 1) [::false])));(6354,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2949)) (@Eref VarOrder.T (@Eid VarOrder.T 6332)) (@Econst VarOrder.T (Fuint 1) [::true])));(6366,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2010)) (@Eref VarOrder.T (@Eid VarOrder.T 6354)) (@Eref VarOrder.T (@Eid VarOrder.T 6332))));(6376,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2929)) (@Eref VarOrder.T (@Eid VarOrder.T 6366)) (@Econst VarOrder.T (Fuint 1) [::true])));(6380,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2912)) (@Eref VarOrder.T (@Eid VarOrder.T 6376)) (@Eref VarOrder.T (@Eid VarOrder.T 6366))));(6390,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2004)) (@Eref VarOrder.T (@Eid VarOrder.T 6380)) (@Eref VarOrder.T (@Eid VarOrder.T 6366))));(6400,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2909)) (@Eref VarOrder.T (@Eid VarOrder.T 6390)) (@Econst VarOrder.T (Fuint 1) [::true])));(6404,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2892)) (@Eref VarOrder.T (@Eid VarOrder.T 6400)) (@Eref VarOrder.T (@Eid VarOrder.T 6390))));(6414,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1998)) (@Eref VarOrder.T (@Eid VarOrder.T 6404)) (@Eref VarOrder.T (@Eid VarOrder.T 6390))));(6424,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2889)) (@Eref VarOrder.T (@Eid VarOrder.T 6414)) (@Econst VarOrder.T (Fuint 1) [::true])));(6428,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2872)) (@Eref VarOrder.T (@Eid VarOrder.T 6424)) (@Eref VarOrder.T (@Eid VarOrder.T 6414))));(6438,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1992)) (@Eref VarOrder.T (@Eid VarOrder.T 6428)) (@Eref VarOrder.T (@Eid VarOrder.T 6414))));(6448,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2867)) (@Eref VarOrder.T (@Eid VarOrder.T 6438)) (@Econst VarOrder.T (Fuint 1) [::true])));(6452,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2850)) (@Eref VarOrder.T (@Eid VarOrder.T 6448)) (@Eref VarOrder.T (@Eid VarOrder.T 6438))));(6462,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1986)) (@Eref VarOrder.T (@Eid VarOrder.T 6452)) (@Eref VarOrder.T (@Eid VarOrder.T 6438))));(6472,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2847)) (@Eref VarOrder.T (@Eid VarOrder.T 6462)) (@Econst VarOrder.T (Fuint 1) [::true])));(6476,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2830)) (@Eref VarOrder.T (@Eid VarOrder.T 6472)) (@Eref VarOrder.T (@Eid VarOrder.T 6462))));(6486,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1980)) (@Eref VarOrder.T (@Eid VarOrder.T 6476)) (@Eref VarOrder.T (@Eid VarOrder.T 6462))));(6496,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2825)) (@Eref VarOrder.T (@Eid VarOrder.T 6486)) (@Econst VarOrder.T (Fuint 1) [::true])));(6500,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2806)) (@Eref VarOrder.T (@Eid VarOrder.T 6496)) (@Eref VarOrder.T (@Eid VarOrder.T 6486))));(6510,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1974)) (@Eref VarOrder.T (@Eid VarOrder.T 6500)) (@Eref VarOrder.T (@Eid VarOrder.T 6486))));(6523,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2679)) (@Eref VarOrder.T (@Eid VarOrder.T 6510)) (@Econst VarOrder.T (Fuint 1) [::true])));(6533,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6523)) (@Eref VarOrder.T (@Eid VarOrder.T 6510))));(6548,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2664)) (@Eref VarOrder.T (@Eid VarOrder.T 6533)) (@Econst VarOrder.T (Fuint 1) [::true])));(6557,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6548)) (@Eref VarOrder.T (@Eid VarOrder.T 6533))));(6573,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2649)) (@Eref VarOrder.T (@Eid VarOrder.T 6557)) (@Econst VarOrder.T (Fuint 1) [::true])));(6582,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6573)) (@Eref VarOrder.T (@Eid VarOrder.T 6557))));(6589,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2634)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6582))));(6595,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Eref VarOrder.T (@Eid VarOrder.T 6589)) (@Eref VarOrder.T (@Eid VarOrder.T 6582))));(6614,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2565)) (@Eref VarOrder.T (@Eid VarOrder.T 6595)) (@Econst VarOrder.T (Fuint 1) [::true])));(6623,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6614)) (@Eref VarOrder.T (@Eid VarOrder.T 6595))));(6630,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2736)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6623))));(6640,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Eref VarOrder.T (@Eid VarOrder.T 6630)) (@Eref VarOrder.T (@Eid VarOrder.T 6623))));(6663,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Eref VarOrder.T (@Eid VarOrder.T 6640)) (@Econst VarOrder.T (Fuint 1) [::true])));(6672,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6663)) (@Eref VarOrder.T (@Eid VarOrder.T 6640))));(6687,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Eref VarOrder.T (@Eid VarOrder.T 6672)) (@Econst VarOrder.T (Fuint 1) [::true])));(6696,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6687)) (@Eref VarOrder.T (@Eid VarOrder.T 6672))));(6701,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1937)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6696))));(6704,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2751)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6701))));(6705,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2750)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6704))));(6706,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2748)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6705))));(6709,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1933)) (@Eref VarOrder.T (@Eid VarOrder.T 6706)) (@Eref VarOrder.T (@Eid VarOrder.T 6701))));(6778,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3042)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6709))));(6779,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6778)) (@Econst VarOrder.T (Fuint 1) [::false])));(6780,(@Eref VarOrder.T (@Eid VarOrder.T 6779)))].
Definition reference_event_offsets := [::6402%nat;8%nat;21%nat;11%nat;9%nat;3%nat;9%nat;9%nat;3%nat;9%nat;9%nat;3%nat;9%nat;9%nat;3%nat;9%nat;9%nat;3%nat;9%nat;9%nat;3%nat;9%nat;12%nat;9%nat;14%nat;8%nat;15%nat;8%nat;6%nat;5%nat;18%nat;8%nat;6%nat;9%nat;22%nat;8%nat;14%nat;8%nat;4%nat;2%nat;0%nat;0%nat;2%nat;68%nat;0%nat;0%nat].
Lemma reference_event_positions : select_node_offsets reference_event_offsets flat_statements = Some reference_event_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_event_safety : selected_node_safety flat_memories flat_statements reference_event_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_event_guards : seq VarOrder.T := [::1707;1886;1933;1937;1941;1946;1951;1958;1962;1966;1970;1974;1980;1986;1992;1998;2004;2010;2357;2565;2634;2649;2664;2679;2708;2723;2736;2748;2750;2751;2806;2825;2830;2847;2850;2867;2872;2889;2892;2909;2912;2929;2949;2966;3042].
Definition reference_event_value (guards:VarOrder.T -> bool) :=
 let v6323 := if (guards 2966) then false else true in
 let v6332 := if (guards 2357) then (v6323) else false in
 let v6354 := if (guards 2949) then (v6332) else true in
 let v6366 := if (guards 2010) then (v6354) else (v6332) in
 let v6376 := if (guards 2929) then (v6366) else true in
 let v6380 := if (guards 2912) then (v6376) else (v6366) in
 let v6390 := if (guards 2004) then (v6380) else (v6366) in
 let v6400 := if (guards 2909) then (v6390) else true in
 let v6404 := if (guards 2892) then (v6400) else (v6390) in
 let v6414 := if (guards 1998) then (v6404) else (v6390) in
 let v6424 := if (guards 2889) then (v6414) else true in
 let v6428 := if (guards 2872) then (v6424) else (v6414) in
 let v6438 := if (guards 1992) then (v6428) else (v6414) in
 let v6448 := if (guards 2867) then (v6438) else true in
 let v6452 := if (guards 2850) then (v6448) else (v6438) in
 let v6462 := if (guards 1986) then (v6452) else (v6438) in
 let v6472 := if (guards 2847) then (v6462) else true in
 let v6476 := if (guards 2830) then (v6472) else (v6462) in
 let v6486 := if (guards 1980) then (v6476) else (v6462) in
 let v6496 := if (guards 2825) then (v6486) else true in
 let v6500 := if (guards 2806) then (v6496) else (v6486) in
 let v6510 := if (guards 1974) then (v6500) else (v6486) in
 let v6523 := if (guards 2679) then (v6510) else true in
 let v6533 := if (guards 1970) then (v6523) else (v6510) in
 let v6548 := if (guards 2664) then (v6533) else true in
 let v6557 := if (guards 1966) then (v6548) else (v6533) in
 let v6573 := if (guards 2649) then (v6557) else true in
 let v6582 := if (guards 1962) then (v6573) else (v6557) in
 let v6589 := if (guards 2634) then true else (v6582) in
 let v6595 := if (guards 1958) then (v6589) else (v6582) in
 let v6614 := if (guards 2565) then (v6595) else true in
 let v6623 := if (guards 1886) then (v6614) else (v6595) in
 let v6630 := if (guards 2736) then true else (v6623) in
 let v6640 := if (guards 1951) then (v6630) else (v6623) in
 let v6663 := if (guards 2723) then (v6640) else true in
 let v6672 := if (guards 1946) then (v6663) else (v6640) in
 let v6687 := if (guards 2708) then (v6672) else true in
 let v6696 := if (guards 1941) then (v6687) else (v6672) in
 let v6701 := if (guards 1937) then true else (v6696) in
 let v6704 := if (guards 2751) then true else (v6701) in
 let v6705 := if (guards 2750) then true else (v6704) in
 let v6706 := if (guards 2748) then true else (v6705) in
 let v6709 := if (guards 1933) then (v6706) else (v6701) in
 let v6778 := if (guards 3042) then true else (v6709) in
 let v6779 := if (guards 1707) then (v6778) else false in
 let v6780 := (v6779) in
 v6780.
Theorem reference_event_spine_history guards invalid history limit start :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall node i, List.In node reference_event_guards -> (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find node (history i) = Some (Gval (Fuint 1) [::guards node])) ->
 forall time, (Nat.add start 46 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 6780 (history time) = Some (Gval (Fuint 1) [::reference_event_value guards]).
Proof.
 intros Steps Guards.
 set v6323 := (if (guards 2966) then false else true).
 assert (V6323 : forall time, (Nat.add start 1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6323 (history time) = Some (Gval (Fuint 1) [::v6323])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6323 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2966)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 0%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)).
 unfold v6323. destruct (guards 2966);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6332 := (if (guards 2357) then (v6323) else false).
 assert (V6332 : forall time, (Nat.add start 2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6332 (history time) = Some (Gval (Fuint 1) [::v6332])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6332 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2357)) (@Eref VarOrder.T (@Eid VarOrder.T 6323)) (@Econst VarOrder.T (Fuint 1) [::false]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 1%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2357 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6323 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2357 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6323 time ltac:(lia) ltac:(lia)).
 unfold v6332. destruct (guards 2357);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6354 := (if (guards 2949) then (v6332) else true).
 assert (V6354 : forall time, (Nat.add start 3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6354 (history time) = Some (Gval (Fuint 1) [::v6354])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6354 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2949)) (@Eref VarOrder.T (@Eid VarOrder.T 6332)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 2%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2949 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6332 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2949 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6332 time ltac:(lia) ltac:(lia)).
 unfold v6354. destruct (guards 2949);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6366 := (if (guards 2010) then (v6354) else (v6332)).
 assert (V6366 : forall time, (Nat.add start 4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6366 (history time) = Some (Gval (Fuint 1) [::v6366])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6366 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2010)) (@Eref VarOrder.T (@Eid VarOrder.T 6354)) (@Eref VarOrder.T (@Eid VarOrder.T 6332)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 3%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2010 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6354 time ltac:(lia) ltac:(lia)) (V6332 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2010 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6354 time ltac:(lia) ltac:(lia)) ?(V6332 time ltac:(lia) ltac:(lia)).
 unfold v6366. destruct (guards 2010);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6376 := (if (guards 2929) then (v6366) else true).
 assert (V6376 : forall time, (Nat.add start 5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6376 (history time) = Some (Gval (Fuint 1) [::v6376])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6376 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2929)) (@Eref VarOrder.T (@Eid VarOrder.T 6366)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 4%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2929 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6366 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2929 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6366 time ltac:(lia) ltac:(lia)).
 unfold v6376. destruct (guards 2929);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6380 := (if (guards 2912) then (v6376) else (v6366)).
 assert (V6380 : forall time, (Nat.add start 6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6380 (history time) = Some (Gval (Fuint 1) [::v6380])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6380 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2912)) (@Eref VarOrder.T (@Eid VarOrder.T 6376)) (@Eref VarOrder.T (@Eid VarOrder.T 6366)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 5%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2912 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6376 time ltac:(lia) ltac:(lia)) (V6366 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2912 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6376 time ltac:(lia) ltac:(lia)) ?(V6366 time ltac:(lia) ltac:(lia)).
 unfold v6380. destruct (guards 2912);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6390 := (if (guards 2004) then (v6380) else (v6366)).
 assert (V6390 : forall time, (Nat.add start 7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6390 (history time) = Some (Gval (Fuint 1) [::v6390])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6390 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2004)) (@Eref VarOrder.T (@Eid VarOrder.T 6380)) (@Eref VarOrder.T (@Eid VarOrder.T 6366)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 6%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2004 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6380 time ltac:(lia) ltac:(lia)) (V6366 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2004 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6380 time ltac:(lia) ltac:(lia)) ?(V6366 time ltac:(lia) ltac:(lia)).
 unfold v6390. destruct (guards 2004);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6400 := (if (guards 2909) then (v6390) else true).
 assert (V6400 : forall time, (Nat.add start 8 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6400 (history time) = Some (Gval (Fuint 1) [::v6400])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6400 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2909)) (@Eref VarOrder.T (@Eid VarOrder.T 6390)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 7%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2909 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6390 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2909 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6390 time ltac:(lia) ltac:(lia)).
 unfold v6400. destruct (guards 2909);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6404 := (if (guards 2892) then (v6400) else (v6390)).
 assert (V6404 : forall time, (Nat.add start 9 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6404 (history time) = Some (Gval (Fuint 1) [::v6404])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6404 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2892)) (@Eref VarOrder.T (@Eid VarOrder.T 6400)) (@Eref VarOrder.T (@Eid VarOrder.T 6390)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 8%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2892 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6400 time ltac:(lia) ltac:(lia)) (V6390 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2892 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6400 time ltac:(lia) ltac:(lia)) ?(V6390 time ltac:(lia) ltac:(lia)).
 unfold v6404. destruct (guards 2892);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6414 := (if (guards 1998) then (v6404) else (v6390)).
 assert (V6414 : forall time, (Nat.add start 10 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6414 (history time) = Some (Gval (Fuint 1) [::v6414])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6414 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1998)) (@Eref VarOrder.T (@Eid VarOrder.T 6404)) (@Eref VarOrder.T (@Eid VarOrder.T 6390)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 9%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1998 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6404 time ltac:(lia) ltac:(lia)) (V6390 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1998 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6404 time ltac:(lia) ltac:(lia)) ?(V6390 time ltac:(lia) ltac:(lia)).
 unfold v6414. destruct (guards 1998);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6424 := (if (guards 2889) then (v6414) else true).
 assert (V6424 : forall time, (Nat.add start 11 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6424 (history time) = Some (Gval (Fuint 1) [::v6424])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6424 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2889)) (@Eref VarOrder.T (@Eid VarOrder.T 6414)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 10%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2889 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6414 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2889 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6414 time ltac:(lia) ltac:(lia)).
 unfold v6424. destruct (guards 2889);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6428 := (if (guards 2872) then (v6424) else (v6414)).
 assert (V6428 : forall time, (Nat.add start 12 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6428 (history time) = Some (Gval (Fuint 1) [::v6428])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6428 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2872)) (@Eref VarOrder.T (@Eid VarOrder.T 6424)) (@Eref VarOrder.T (@Eid VarOrder.T 6414)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 11%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2872 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6424 time ltac:(lia) ltac:(lia)) (V6414 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2872 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6424 time ltac:(lia) ltac:(lia)) ?(V6414 time ltac:(lia) ltac:(lia)).
 unfold v6428. destruct (guards 2872);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6438 := (if (guards 1992) then (v6428) else (v6414)).
 assert (V6438 : forall time, (Nat.add start 13 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6438 (history time) = Some (Gval (Fuint 1) [::v6438])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6438 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1992)) (@Eref VarOrder.T (@Eid VarOrder.T 6428)) (@Eref VarOrder.T (@Eid VarOrder.T 6414)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 12%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1992 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6428 time ltac:(lia) ltac:(lia)) (V6414 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1992 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6428 time ltac:(lia) ltac:(lia)) ?(V6414 time ltac:(lia) ltac:(lia)).
 unfold v6438. destruct (guards 1992);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6448 := (if (guards 2867) then (v6438) else true).
 assert (V6448 : forall time, (Nat.add start 14 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6448 (history time) = Some (Gval (Fuint 1) [::v6448])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6448 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2867)) (@Eref VarOrder.T (@Eid VarOrder.T 6438)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 13%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2867 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6438 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2867 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6438 time ltac:(lia) ltac:(lia)).
 unfold v6448. destruct (guards 2867);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6452 := (if (guards 2850) then (v6448) else (v6438)).
 assert (V6452 : forall time, (Nat.add start 15 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6452 (history time) = Some (Gval (Fuint 1) [::v6452])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6452 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2850)) (@Eref VarOrder.T (@Eid VarOrder.T 6448)) (@Eref VarOrder.T (@Eid VarOrder.T 6438)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 14%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2850 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6448 time ltac:(lia) ltac:(lia)) (V6438 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2850 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6448 time ltac:(lia) ltac:(lia)) ?(V6438 time ltac:(lia) ltac:(lia)).
 unfold v6452. destruct (guards 2850);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6462 := (if (guards 1986) then (v6452) else (v6438)).
 assert (V6462 : forall time, (Nat.add start 16 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6462 (history time) = Some (Gval (Fuint 1) [::v6462])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6462 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1986)) (@Eref VarOrder.T (@Eid VarOrder.T 6452)) (@Eref VarOrder.T (@Eid VarOrder.T 6438)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 15%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1986 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6452 time ltac:(lia) ltac:(lia)) (V6438 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1986 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6452 time ltac:(lia) ltac:(lia)) ?(V6438 time ltac:(lia) ltac:(lia)).
 unfold v6462. destruct (guards 1986);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6472 := (if (guards 2847) then (v6462) else true).
 assert (V6472 : forall time, (Nat.add start 17 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6472 (history time) = Some (Gval (Fuint 1) [::v6472])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6472 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2847)) (@Eref VarOrder.T (@Eid VarOrder.T 6462)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 16%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2847 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6462 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2847 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6462 time ltac:(lia) ltac:(lia)).
 unfold v6472. destruct (guards 2847);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6476 := (if (guards 2830) then (v6472) else (v6462)).
 assert (V6476 : forall time, (Nat.add start 18 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6476 (history time) = Some (Gval (Fuint 1) [::v6476])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6476 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2830)) (@Eref VarOrder.T (@Eid VarOrder.T 6472)) (@Eref VarOrder.T (@Eid VarOrder.T 6462)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 17%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2830 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6472 time ltac:(lia) ltac:(lia)) (V6462 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2830 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6472 time ltac:(lia) ltac:(lia)) ?(V6462 time ltac:(lia) ltac:(lia)).
 unfold v6476. destruct (guards 2830);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6486 := (if (guards 1980) then (v6476) else (v6462)).
 assert (V6486 : forall time, (Nat.add start 19 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6486 (history time) = Some (Gval (Fuint 1) [::v6486])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6486 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1980)) (@Eref VarOrder.T (@Eid VarOrder.T 6476)) (@Eref VarOrder.T (@Eid VarOrder.T 6462)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 18%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1980 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6476 time ltac:(lia) ltac:(lia)) (V6462 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1980 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6476 time ltac:(lia) ltac:(lia)) ?(V6462 time ltac:(lia) ltac:(lia)).
 unfold v6486. destruct (guards 1980);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6496 := (if (guards 2825) then (v6486) else true).
 assert (V6496 : forall time, (Nat.add start 20 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6496 (history time) = Some (Gval (Fuint 1) [::v6496])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6496 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2825)) (@Eref VarOrder.T (@Eid VarOrder.T 6486)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 19%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2825 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6486 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2825 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6486 time ltac:(lia) ltac:(lia)).
 unfold v6496. destruct (guards 2825);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6500 := (if (guards 2806) then (v6496) else (v6486)).
 assert (V6500 : forall time, (Nat.add start 21 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6500 (history time) = Some (Gval (Fuint 1) [::v6500])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6500 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2806)) (@Eref VarOrder.T (@Eid VarOrder.T 6496)) (@Eref VarOrder.T (@Eid VarOrder.T 6486)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 20%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2806 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6496 time ltac:(lia) ltac:(lia)) (V6486 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2806 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6496 time ltac:(lia) ltac:(lia)) ?(V6486 time ltac:(lia) ltac:(lia)).
 unfold v6500. destruct (guards 2806);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6510 := (if (guards 1974) then (v6500) else (v6486)).
 assert (V6510 : forall time, (Nat.add start 22 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6510 (history time) = Some (Gval (Fuint 1) [::v6510])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6510 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1974)) (@Eref VarOrder.T (@Eid VarOrder.T 6500)) (@Eref VarOrder.T (@Eid VarOrder.T 6486)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 21%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1974 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6500 time ltac:(lia) ltac:(lia)) (V6486 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1974 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6500 time ltac:(lia) ltac:(lia)) ?(V6486 time ltac:(lia) ltac:(lia)).
 unfold v6510. destruct (guards 1974);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6523 := (if (guards 2679) then (v6510) else true).
 assert (V6523 : forall time, (Nat.add start 23 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6523 (history time) = Some (Gval (Fuint 1) [::v6523])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6523 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2679)) (@Eref VarOrder.T (@Eid VarOrder.T 6510)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 22%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2679 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6510 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2679 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6510 time ltac:(lia) ltac:(lia)).
 unfold v6523. destruct (guards 2679);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6533 := (if (guards 1970) then (v6523) else (v6510)).
 assert (V6533 : forall time, (Nat.add start 24 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6533 (history time) = Some (Gval (Fuint 1) [::v6533])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6533 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6523)) (@Eref VarOrder.T (@Eid VarOrder.T 6510)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 23%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1970 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6523 time ltac:(lia) ltac:(lia)) (V6510 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1970 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6523 time ltac:(lia) ltac:(lia)) ?(V6510 time ltac:(lia) ltac:(lia)).
 unfold v6533. destruct (guards 1970);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6548 := (if (guards 2664) then (v6533) else true).
 assert (V6548 : forall time, (Nat.add start 25 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6548 (history time) = Some (Gval (Fuint 1) [::v6548])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6548 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2664)) (@Eref VarOrder.T (@Eid VarOrder.T 6533)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 24%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2664 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6533 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2664 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6533 time ltac:(lia) ltac:(lia)).
 unfold v6548. destruct (guards 2664);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6557 := (if (guards 1966) then (v6548) else (v6533)).
 assert (V6557 : forall time, (Nat.add start 26 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6557 (history time) = Some (Gval (Fuint 1) [::v6557])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6557 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6548)) (@Eref VarOrder.T (@Eid VarOrder.T 6533)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 25%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6548 time ltac:(lia) ltac:(lia)) (V6533 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6548 time ltac:(lia) ltac:(lia)) ?(V6533 time ltac:(lia) ltac:(lia)).
 unfold v6557. destruct (guards 1966);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6573 := (if (guards 2649) then (v6557) else true).
 assert (V6573 : forall time, (Nat.add start 27 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6573 (history time) = Some (Gval (Fuint 1) [::v6573])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6573 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2649)) (@Eref VarOrder.T (@Eid VarOrder.T 6557)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 26%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2649 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6557 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2649 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6557 time ltac:(lia) ltac:(lia)).
 unfold v6573. destruct (guards 2649);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6582 := (if (guards 1962) then (v6573) else (v6557)).
 assert (V6582 : forall time, (Nat.add start 28 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6582 (history time) = Some (Gval (Fuint 1) [::v6582])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6582 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6573)) (@Eref VarOrder.T (@Eid VarOrder.T 6557)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 27%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1962 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6573 time ltac:(lia) ltac:(lia)) (V6557 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1962 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6573 time ltac:(lia) ltac:(lia)) ?(V6557 time ltac:(lia) ltac:(lia)).
 unfold v6582. destruct (guards 1962);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6589 := (if (guards 2634) then true else (v6582)).
 assert (V6589 : forall time, (Nat.add start 29 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6589 (history time) = Some (Gval (Fuint 1) [::v6589])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6589 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2634)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6582)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 28%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2634 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6582 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2634 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6582 time ltac:(lia) ltac:(lia)).
 unfold v6589. destruct (guards 2634);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6595 := (if (guards 1958) then (v6589) else (v6582)).
 assert (V6595 : forall time, (Nat.add start 30 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6595 (history time) = Some (Gval (Fuint 1) [::v6595])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6595 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Eref VarOrder.T (@Eid VarOrder.T 6589)) (@Eref VarOrder.T (@Eid VarOrder.T 6582)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 29%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1958 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6589 time ltac:(lia) ltac:(lia)) (V6582 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1958 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6589 time ltac:(lia) ltac:(lia)) ?(V6582 time ltac:(lia) ltac:(lia)).
 unfold v6595. destruct (guards 1958);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6614 := (if (guards 2565) then (v6595) else true).
 assert (V6614 : forall time, (Nat.add start 31 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6614 (history time) = Some (Gval (Fuint 1) [::v6614])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6614 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2565)) (@Eref VarOrder.T (@Eid VarOrder.T 6595)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 30%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2565 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6595 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2565 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6595 time ltac:(lia) ltac:(lia)).
 unfold v6614. destruct (guards 2565);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6623 := (if (guards 1886) then (v6614) else (v6595)).
 assert (V6623 : forall time, (Nat.add start 32 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6623 (history time) = Some (Gval (Fuint 1) [::v6623])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6623 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6614)) (@Eref VarOrder.T (@Eid VarOrder.T 6595)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 31%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1886 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6614 time ltac:(lia) ltac:(lia)) (V6595 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1886 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6614 time ltac:(lia) ltac:(lia)) ?(V6595 time ltac:(lia) ltac:(lia)).
 unfold v6623. destruct (guards 1886);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6630 := (if (guards 2736) then true else (v6623)).
 assert (V6630 : forall time, (Nat.add start 33 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6630 (history time) = Some (Gval (Fuint 1) [::v6630])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6630 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2736)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6623)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 32%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2736 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6623 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2736 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6623 time ltac:(lia) ltac:(lia)).
 unfold v6630. destruct (guards 2736);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6640 := (if (guards 1951) then (v6630) else (v6623)).
 assert (V6640 : forall time, (Nat.add start 34 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6640 (history time) = Some (Gval (Fuint 1) [::v6640])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6640 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Eref VarOrder.T (@Eid VarOrder.T 6630)) (@Eref VarOrder.T (@Eid VarOrder.T 6623)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 33%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1951 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6630 time ltac:(lia) ltac:(lia)) (V6623 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1951 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6630 time ltac:(lia) ltac:(lia)) ?(V6623 time ltac:(lia) ltac:(lia)).
 unfold v6640. destruct (guards 1951);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6663 := (if (guards 2723) then (v6640) else true).
 assert (V6663 : forall time, (Nat.add start 35 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6663 (history time) = Some (Gval (Fuint 1) [::v6663])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6663 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Eref VarOrder.T (@Eid VarOrder.T 6640)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 34%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2723 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6640 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2723 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6640 time ltac:(lia) ltac:(lia)).
 unfold v6663. destruct (guards 2723);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6672 := (if (guards 1946) then (v6663) else (v6640)).
 assert (V6672 : forall time, (Nat.add start 36 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6672 (history time) = Some (Gval (Fuint 1) [::v6672])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6672 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6663)) (@Eref VarOrder.T (@Eid VarOrder.T 6640)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 35%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1946 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6663 time ltac:(lia) ltac:(lia)) (V6640 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1946 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6663 time ltac:(lia) ltac:(lia)) ?(V6640 time ltac:(lia) ltac:(lia)).
 unfold v6672. destruct (guards 1946);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6687 := (if (guards 2708) then (v6672) else true).
 assert (V6687 : forall time, (Nat.add start 37 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6687 (history time) = Some (Gval (Fuint 1) [::v6687])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6687 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Eref VarOrder.T (@Eid VarOrder.T 6672)) (@Econst VarOrder.T (Fuint 1) [::true]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 36%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2708 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6672 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2708 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6672 time ltac:(lia) ltac:(lia)).
 unfold v6687. destruct (guards 2708);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6696 := (if (guards 1941) then (v6687) else (v6672)).
 assert (V6696 : forall time, (Nat.add start 38 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6696 (history time) = Some (Gval (Fuint 1) [::v6696])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6696 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6687)) (@Eref VarOrder.T (@Eid VarOrder.T 6672)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 37%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1941 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6687 time ltac:(lia) ltac:(lia)) (V6672 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1941 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6687 time ltac:(lia) ltac:(lia)) ?(V6672 time ltac:(lia) ltac:(lia)).
 unfold v6696. destruct (guards 1941);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6701 := (if (guards 1937) then true else (v6696)).
 assert (V6701 : forall time, (Nat.add start 39 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6701 (history time) = Some (Gval (Fuint 1) [::v6701])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6701 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1937)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6696)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 38%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1937 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6696 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1937 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6696 time ltac:(lia) ltac:(lia)).
 unfold v6701. destruct (guards 1937);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6704 := (if (guards 2751) then true else (v6701)).
 assert (V6704 : forall time, (Nat.add start 40 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6704 (history time) = Some (Gval (Fuint 1) [::v6704])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6704 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2751)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6701)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 39%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2751 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6701 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2751 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6701 time ltac:(lia) ltac:(lia)).
 unfold v6704. destruct (guards 2751);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6705 := (if (guards 2750) then true else (v6704)).
 assert (V6705 : forall time, (Nat.add start 41 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6705 (history time) = Some (Gval (Fuint 1) [::v6705])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6705 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2750)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6704)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 40%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2750 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6704 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2750 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6704 time ltac:(lia) ltac:(lia)).
 unfold v6705. destruct (guards 2750);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6706 := (if (guards 2748) then true else (v6705)).
 assert (V6706 : forall time, (Nat.add start 42 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6706 (history time) = Some (Gval (Fuint 1) [::v6706])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6706 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2748)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6705)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 41%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2748 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6705 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2748 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6705 time ltac:(lia) ltac:(lia)).
 unfold v6706. destruct (guards 2748);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6709 := (if (guards 1933) then (v6706) else (v6701)).
 assert (V6709 : forall time, (Nat.add start 43 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6709 (history time) = Some (Gval (Fuint 1) [::v6709])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6709 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1933)) (@Eref VarOrder.T (@Eid VarOrder.T 6706)) (@Eref VarOrder.T (@Eid VarOrder.T 6701)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 42%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1933 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6706 time ltac:(lia) ltac:(lia)) (V6701 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1933 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6706 time ltac:(lia) ltac:(lia)) ?(V6701 time ltac:(lia) ltac:(lia)).
 unfold v6709. destruct (guards 1933);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6778 := (if (guards 3042) then true else (v6709)).
 assert (V6778 : forall time, (Nat.add start 44 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6778 (history time) = Some (Gval (Fuint 1) [::v6778])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6778 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 3042)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6709)))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 43%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 3042 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6709 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 3042 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6709 time ltac:(lia) ltac:(lia)).
 unfold v6778. destruct (guards 3042);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6779 := (if (guards 1707) then (v6778) else false).
 assert (V6779 : forall time, (Nat.add start 45 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6779 (history time) = Some (Gval (Fuint 1) [::v6779])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6779 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6778)) (@Econst VarOrder.T (Fuint 1) [::false]))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 44%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6778 time ltac:(lia) ltac:(lia)).
 unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6778 time ltac:(lia) ltac:(lia)).
 unfold v6779. destruct (guards 1707);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set v6780 := ((v6779)).
 assert (V6780 : forall time, (Nat.add start 46 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6780 (history time) = Some (Gval (Fuint 1) [::v6780])).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_event_offsets reference_event_nodes 6780 ((@Eref VarOrder.T (@Eid VarOrder.T 6779))));
 [exact reference_event_positions|exact reference_event_safety|apply (List.nth_error_In reference_event_nodes 45%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (V6779 time ltac:(lia) ltac:(lia)).
 reflexivity. }
 intros time Lower Upper. exact (V6780 time Lower Upper).
Qed.
