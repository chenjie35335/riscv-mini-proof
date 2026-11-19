Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode FormalDeclaredWireCheck.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_request_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(6517,(@Econst VarOrder.T (Fuint 1) [::false]));(6518,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2679)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6517))));(6520,(@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false]));(6521,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2679)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6520))));(6528,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6518)) (@Eref VarOrder.T (@Eid VarOrder.T 6517))));(6531,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6521)) (@Eref VarOrder.T (@Eid VarOrder.T 6520))));(6544,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2664)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6528))));(6546,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2664)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6531))));(6553,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6544)) (@Eref VarOrder.T (@Eid VarOrder.T 6528))));(6555,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6546)) (@Eref VarOrder.T (@Eid VarOrder.T 6531))));(6569,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2649)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6553))));(6571,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2649)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6555))));(6578,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6569)) (@Eref VarOrder.T (@Eid VarOrder.T 6553))));(6580,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6571)) (@Eref VarOrder.T (@Eid VarOrder.T 6555))));(6596,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6578))));(6598,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6580))));(6610,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2565)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6596))));(6612,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2565)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6598))));(6619,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6610)) (@Eref VarOrder.T (@Eid VarOrder.T 6596))));(6621,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6612)) (@Eref VarOrder.T (@Eid VarOrder.T 6598))));(6641,(@Econst VarOrder.T (Fuint 1) [::false]));(6642,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6641))));(6645,(@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false]));(6646,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6645))));(6659,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6642))));(6661,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6646))));(6668,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6659)) (@Eref VarOrder.T (@Eid VarOrder.T 6642))));(6670,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6661)) (@Eref VarOrder.T (@Eid VarOrder.T 6646))));(6683,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6668))));(6685,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6670))));(6692,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6683)) (@Eref VarOrder.T (@Eid VarOrder.T 6668))));(6694,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6685)) (@Eref VarOrder.T (@Eid VarOrder.T 6670))));(7111,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6619)) (@Eref VarOrder.T (@Eid VarOrder.T 6517))));(7112,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6621)) (@Eref VarOrder.T (@Eid VarOrder.T 6520))));(7113,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6692)) (@Eref VarOrder.T (@Eid VarOrder.T 6641))));(7114,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6694)) (@Eref VarOrder.T (@Eid VarOrder.T 6645))));(7186,(@Eref VarOrder.T (@Eid VarOrder.T 7111)));(7187,(@Eref VarOrder.T (@Eid VarOrder.T 7112)));(7188,(@Eref VarOrder.T (@Eid VarOrder.T 7113)));(7189,(@Eref VarOrder.T (@Eid VarOrder.T 7114)))].
Definition reference_request_offsets := [::6596%nat;0%nat;1%nat;0%nat;6%nat;2%nat;12%nat;1%nat;6%nat;1%nat;13%nat;1%nat;6%nat;1%nat;15%nat;1%nat;11%nat;1%nat;6%nat;1%nat;19%nat;0%nat;2%nat;0%nat;12%nat;1%nat;6%nat;1%nat;12%nat;1%nat;6%nat;1%nat;416%nat;0%nat;0%nat;0%nat;71%nat;0%nat;0%nat;0%nat].
Definition reference_request_wire_positions := [::1788%nat;1598%nat;1790%nat;1600%nat;1792%nat;1602%nat;1794%nat;1604%nat].
Definition reference_request_wire_distances := [::5561%nat;6138%nat;5561%nat;6138%nat;5560%nat;6137%nat;5560%nat;6137%nat].
Definition reference_request_field_width field := if Nat.even field then 1%nat else 6%nat.
Definition reference_request_wire_target field outer : VarOrder.T := (if outer then 1519 else 1709)+2*N.of_nat field.
Definition reference_request_wire_source field outer : VarOrder.T := if outer then 1709+2*N.of_nat field else 7186+N.of_nat field.
Lemma reference_request_wire_certificate field outer : (field < 4)%coq_nat ->
 declared_wire_check flat_memories flat_statements
 (nth 0%nat reference_request_wire_positions (Nat.add (Nat.mul 2 field) (if outer then 1 else 0)))
 (nth 0%nat reference_request_wire_distances (Nat.add (Nat.mul 2 field) (if outer then 1 else 0)))
 (reference_request_wire_target field outer) (reference_request_wire_source field outer) (reference_request_field_width field) = true.
Proof. intro Field. destruct outer;do 4 (destruct field as [|field];[vm_compute;reflexivity|]);lia. Qed.
Lemma reference_request_positions : select_node_offsets reference_request_offsets flat_statements = Some reference_request_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_request_safety : selected_node_safety flat_memories flat_statements reference_request_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_request_valid (writing:bool) (guards:VarOrder.T -> bool) : bool :=
 if writing then
 let v0 := false in
 let v1 := if guards 1951 then true else v0 in
 let v2 := if guards 2723 then true else v1 in
 let v3 := if guards 1946 then v2 else v1 in
 let v4 := if guards 2708 then true else v3 in
 let v5 := if guards 1941 then v4 else v3 in
 let v6 := if guards 1707 then v5 else v0 in
 v6 else
 let v0 := false in
 let v1 := if guards 2679 then true else v0 in
 let v2 := if guards 1970 then v1 else v0 in
 let v3 := if guards 2664 then true else v2 in
 let v4 := if guards 1966 then v3 else v2 in
 let v5 := if guards 2649 then true else v4 in
 let v6 := if guards 1962 then v5 else v4 in
 let v7 := if guards 1958 then true else v6 in
 let v8 := if guards 2565 then true else v7 in
 let v9 := if guards 1886 then v8 else v7 in
 let v10 := if guards 1707 then v9 else v0 in
 v10.
Definition reference_request_width (writing:bool) (guards:VarOrder.T -> bool) : N :=
 if writing then
 let v0 := 0 in
 let v1 := if guards 1951 then 8 else v0 in
 let v2 := if guards 2723 then 16 else v1 in
 let v3 := if guards 1946 then v2 else v1 in
 let v4 := if guards 2708 then 32 else v3 in
 let v5 := if guards 1941 then v4 else v3 in
 let v6 := if guards 1707 then v5 else v0 in
 v6 else
 let v0 := 0 in
 let v1 := if guards 2679 then 8 else v0 in
 let v2 := if guards 1970 then v1 else v0 in
 let v3 := if guards 2664 then 16 else v2 in
 let v4 := if guards 1966 then v3 else v2 in
 let v5 := if guards 2649 then 32 else v4 in
 let v6 := if guards 1962 then v5 else v4 in
 let v7 := if guards 1958 then 8 else v6 in
 let v8 := if guards 2565 then 16 else v7 in
 let v9 := if guards 1886 then v8 else v7 in
 let v10 := if guards 1707 then v9 else v0 in
 v10.
Definition reference_request_guard_nodes : seq VarOrder.T := [::1707;1886;1941;1946;1951;1958;1962;1966;1970;2565;2649;2664;2679;2708;2723].
Theorem reference_request_spine_history writing guards invalid history limit start :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall node i, List.In node reference_request_guard_nodes -> (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find node (history i) = Some (Gval (Fuint 1) [::guards node])) ->
 forall time, (Nat.add start 11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if writing then 7113 else 7111) (history time) = Some (Gval (Fuint 1) [::reference_request_valid writing guards]) /\
 VM.find (if writing then 7114 else 7112) (history time) = Some (Gval (Fuint 6) (from_N 6 (reference_request_width writing guards))).
Proof.
 intros Steps Guards. destruct writing.
 -
 set b0 := (false).
 assert (V6641 : forall time, (Nat.add start 1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6641 (history time) = Some (Gval (Fuint 1) ([::b0]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6641 ((@Econst VarOrder.T (Fuint 1) [::false])));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 20%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 reflexivity. }
 set w0 := (0).
 assert (V6645 : forall time, (Nat.add start 1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6645 (history time) = Some (Gval (Fuint 6) (from_N 6 w0))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6645 ((@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false])));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 22%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 reflexivity. }
 set b1 := (if guards 1951 then true else b0).
 assert (V6642 : forall time, (Nat.add start 2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6642 (history time) = Some (Gval (Fuint 1) ([::b1]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6642 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6641)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 21%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1951 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6641 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1951 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6641 time ltac:(lia) ltac:(lia)).
 unfold b1. destruct (guards 1951);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w1 := (if guards 1951 then 8 else w0).
 assert (V6646 : forall time, (Nat.add start 2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6646 (history time) = Some (Gval (Fuint 6) (from_N 6 w1))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6646 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6645)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 23%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1951 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6645 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1951 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6645 time ltac:(lia) ltac:(lia)).
 unfold w1. destruct (guards 1951);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b2 := (if guards 2723 then true else b1).
 assert (V6659 : forall time, (Nat.add start 3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6659 (history time) = Some (Gval (Fuint 1) ([::b2]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6659 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6642)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 24%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2723 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6642 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2723 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6642 time ltac:(lia) ltac:(lia)).
 unfold b2. destruct (guards 2723);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w2 := (if guards 2723 then 16 else w1).
 assert (V6661 : forall time, (Nat.add start 3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6661 (history time) = Some (Gval (Fuint 6) (from_N 6 w2))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6661 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6646)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 25%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2723 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6646 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2723 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6646 time ltac:(lia) ltac:(lia)).
 unfold w2. destruct (guards 2723);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b3 := (if guards 1946 then b2 else b1).
 assert (V6668 : forall time, (Nat.add start 4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6668 (history time) = Some (Gval (Fuint 1) ([::b3]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6668 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6659)) (@Eref VarOrder.T (@Eid VarOrder.T 6642)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 26%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1946 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6659 time ltac:(lia) ltac:(lia)) (V6642 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1946 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6659 time ltac:(lia) ltac:(lia)) ?(V6642 time ltac:(lia) ltac:(lia)).
 unfold b3. destruct (guards 1946);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w3 := (if guards 1946 then w2 else w1).
 assert (V6670 : forall time, (Nat.add start 4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6670 (history time) = Some (Gval (Fuint 6) (from_N 6 w3))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6670 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6661)) (@Eref VarOrder.T (@Eid VarOrder.T 6646)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 27%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1946 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6661 time ltac:(lia) ltac:(lia)) (V6646 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1946 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6661 time ltac:(lia) ltac:(lia)) ?(V6646 time ltac:(lia) ltac:(lia)).
 unfold w3. destruct (guards 1946);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b4 := (if guards 2708 then true else b3).
 assert (V6683 : forall time, (Nat.add start 5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6683 (history time) = Some (Gval (Fuint 1) ([::b4]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6683 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6668)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 28%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2708 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6668 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2708 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6668 time ltac:(lia) ltac:(lia)).
 unfold b4. destruct (guards 2708);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w4 := (if guards 2708 then 32 else w3).
 assert (V6685 : forall time, (Nat.add start 5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6685 (history time) = Some (Gval (Fuint 6) (from_N 6 w4))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6685 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6670)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 29%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2708 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6670 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2708 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6670 time ltac:(lia) ltac:(lia)).
 unfold w4. destruct (guards 2708);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b5 := (if guards 1941 then b4 else b3).
 assert (V6692 : forall time, (Nat.add start 6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6692 (history time) = Some (Gval (Fuint 1) ([::b5]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6692 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6683)) (@Eref VarOrder.T (@Eid VarOrder.T 6668)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 30%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1941 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6683 time ltac:(lia) ltac:(lia)) (V6668 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1941 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6683 time ltac:(lia) ltac:(lia)) ?(V6668 time ltac:(lia) ltac:(lia)).
 unfold b5. destruct (guards 1941);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w5 := (if guards 1941 then w4 else w3).
 assert (V6694 : forall time, (Nat.add start 6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6694 (history time) = Some (Gval (Fuint 6) (from_N 6 w5))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6694 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6685)) (@Eref VarOrder.T (@Eid VarOrder.T 6670)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 31%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1941 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6685 time ltac:(lia) ltac:(lia)) (V6670 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1941 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6685 time ltac:(lia) ltac:(lia)) ?(V6670 time ltac:(lia) ltac:(lia)).
 unfold w5. destruct (guards 1941);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b6 := (if guards 1707 then b5 else b0).
 assert (V7113 : forall time, (Nat.add start 7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7113 (history time) = Some (Gval (Fuint 1) ([::b6]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 7113 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6692)) (@Eref VarOrder.T (@Eid VarOrder.T 6641)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 34%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6692 time ltac:(lia) ltac:(lia)) (V6641 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6692 time ltac:(lia) ltac:(lia)) ?(V6641 time ltac:(lia) ltac:(lia)).
 unfold b6. destruct (guards 1707);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w6 := (if guards 1707 then w5 else w0).
 assert (V7114 : forall time, (Nat.add start 7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7114 (history time) = Some (Gval (Fuint 6) (from_N 6 w6))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 7114 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6694)) (@Eref VarOrder.T (@Eid VarOrder.T 6645)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 35%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6694 time ltac:(lia) ltac:(lia)) (V6645 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6694 time ltac:(lia) ltac:(lia)) ?(V6645 time ltac:(lia) ltac:(lia)).
 unfold w6. destruct (guards 1707);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 intros time Lower Upper. split;[exact (V7113 time ltac:(lia) Upper)|exact (V7114 time ltac:(lia) Upper)].
 -
 set b0 := (false).
 assert (V6517 : forall time, (Nat.add start 1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6517 (history time) = Some (Gval (Fuint 1) ([::b0]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6517 ((@Econst VarOrder.T (Fuint 1) [::false])));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 0%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 reflexivity. }
 set w0 := (0).
 assert (V6520 : forall time, (Nat.add start 1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6520 (history time) = Some (Gval (Fuint 6) (from_N 6 w0))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6520 ((@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false])));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 2%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 reflexivity. }
 set b1 := (if guards 2679 then true else b0).
 assert (V6518 : forall time, (Nat.add start 2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6518 (history time) = Some (Gval (Fuint 1) ([::b1]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6518 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2679)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6517)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 1%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2679 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6517 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2679 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6517 time ltac:(lia) ltac:(lia)).
 unfold b1. destruct (guards 2679);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w1 := (if guards 2679 then 8 else w0).
 assert (V6521 : forall time, (Nat.add start 2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6521 (history time) = Some (Gval (Fuint 6) (from_N 6 w1))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6521 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2679)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6520)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 3%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2679 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6520 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2679 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6520 time ltac:(lia) ltac:(lia)).
 unfold w1. destruct (guards 2679);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b2 := (if guards 1970 then b1 else b0).
 assert (V6528 : forall time, (Nat.add start 3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6528 (history time) = Some (Gval (Fuint 1) ([::b2]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6528 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6518)) (@Eref VarOrder.T (@Eid VarOrder.T 6517)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 4%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1970 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6518 time ltac:(lia) ltac:(lia)) (V6517 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1970 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6518 time ltac:(lia) ltac:(lia)) ?(V6517 time ltac:(lia) ltac:(lia)).
 unfold b2. destruct (guards 1970);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w2 := (if guards 1970 then w1 else w0).
 assert (V6531 : forall time, (Nat.add start 3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6531 (history time) = Some (Gval (Fuint 6) (from_N 6 w2))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6531 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6521)) (@Eref VarOrder.T (@Eid VarOrder.T 6520)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 5%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1970 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6521 time ltac:(lia) ltac:(lia)) (V6520 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1970 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6521 time ltac:(lia) ltac:(lia)) ?(V6520 time ltac:(lia) ltac:(lia)).
 unfold w2. destruct (guards 1970);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b3 := (if guards 2664 then true else b2).
 assert (V6544 : forall time, (Nat.add start 4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6544 (history time) = Some (Gval (Fuint 1) ([::b3]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6544 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2664)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6528)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 6%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2664 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6528 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2664 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6528 time ltac:(lia) ltac:(lia)).
 unfold b3. destruct (guards 2664);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w3 := (if guards 2664 then 16 else w2).
 assert (V6546 : forall time, (Nat.add start 4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6546 (history time) = Some (Gval (Fuint 6) (from_N 6 w3))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6546 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2664)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6531)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 7%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2664 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6531 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2664 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6531 time ltac:(lia) ltac:(lia)).
 unfold w3. destruct (guards 2664);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b4 := (if guards 1966 then b3 else b2).
 assert (V6553 : forall time, (Nat.add start 5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6553 (history time) = Some (Gval (Fuint 1) ([::b4]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6553 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6544)) (@Eref VarOrder.T (@Eid VarOrder.T 6528)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 8%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6544 time ltac:(lia) ltac:(lia)) (V6528 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6544 time ltac:(lia) ltac:(lia)) ?(V6528 time ltac:(lia) ltac:(lia)).
 unfold b4. destruct (guards 1966);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w4 := (if guards 1966 then w3 else w2).
 assert (V6555 : forall time, (Nat.add start 5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6555 (history time) = Some (Gval (Fuint 6) (from_N 6 w4))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6555 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6546)) (@Eref VarOrder.T (@Eid VarOrder.T 6531)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 9%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6546 time ltac:(lia) ltac:(lia)) (V6531 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1966 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6546 time ltac:(lia) ltac:(lia)) ?(V6531 time ltac:(lia) ltac:(lia)).
 unfold w4. destruct (guards 1966);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b5 := (if guards 2649 then true else b4).
 assert (V6569 : forall time, (Nat.add start 6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6569 (history time) = Some (Gval (Fuint 1) ([::b5]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6569 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2649)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6553)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 10%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2649 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6553 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2649 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6553 time ltac:(lia) ltac:(lia)).
 unfold b5. destruct (guards 2649);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w5 := (if guards 2649 then 32 else w4).
 assert (V6571 : forall time, (Nat.add start 6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6571 (history time) = Some (Gval (Fuint 6) (from_N 6 w5))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6571 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2649)) (@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6555)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 11%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2649 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6555 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2649 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6555 time ltac:(lia) ltac:(lia)).
 unfold w5. destruct (guards 2649);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b6 := (if guards 1962 then b5 else b4).
 assert (V6578 : forall time, (Nat.add start 7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6578 (history time) = Some (Gval (Fuint 1) ([::b6]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6578 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6569)) (@Eref VarOrder.T (@Eid VarOrder.T 6553)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 12%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1962 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6569 time ltac:(lia) ltac:(lia)) (V6553 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1962 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6569 time ltac:(lia) ltac:(lia)) ?(V6553 time ltac:(lia) ltac:(lia)).
 unfold b6. destruct (guards 1962);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w6 := (if guards 1962 then w5 else w4).
 assert (V6580 : forall time, (Nat.add start 7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6580 (history time) = Some (Gval (Fuint 6) (from_N 6 w6))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6580 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6571)) (@Eref VarOrder.T (@Eid VarOrder.T 6555)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 13%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1962 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6571 time ltac:(lia) ltac:(lia)) (V6555 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1962 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6571 time ltac:(lia) ltac:(lia)) ?(V6555 time ltac:(lia) ltac:(lia)).
 unfold w6. destruct (guards 1962);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b7 := (if guards 1958 then true else b6).
 assert (V6596 : forall time, (Nat.add start 8 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6596 (history time) = Some (Gval (Fuint 1) ([::b7]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6596 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6578)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 14%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1958 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6578 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1958 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6578 time ltac:(lia) ltac:(lia)).
 unfold b7. destruct (guards 1958);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w7 := (if guards 1958 then 8 else w6).
 assert (V6598 : forall time, (Nat.add start 8 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6598 (history time) = Some (Gval (Fuint 6) (from_N 6 w7))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6598 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6580)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 15%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1958 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6580 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1958 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6580 time ltac:(lia) ltac:(lia)).
 unfold w7. destruct (guards 1958);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b8 := (if guards 2565 then true else b7).
 assert (V6610 : forall time, (Nat.add start 9 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6610 (history time) = Some (Gval (Fuint 1) ([::b8]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6610 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2565)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6596)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 16%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2565 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6596 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2565 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6596 time ltac:(lia) ltac:(lia)).
 unfold b8. destruct (guards 2565);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w8 := (if guards 2565 then 16 else w7).
 assert (V6612 : forall time, (Nat.add start 9 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6612 (history time) = Some (Gval (Fuint 6) (from_N 6 w8))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6612 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2565)) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6598)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 17%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 2565 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6598 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 2565 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6598 time ltac:(lia) ltac:(lia)).
 unfold w8. destruct (guards 2565);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b9 := (if guards 1886 then b8 else b7).
 assert (V6619 : forall time, (Nat.add start 10 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6619 (history time) = Some (Gval (Fuint 1) ([::b9]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6619 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6610)) (@Eref VarOrder.T (@Eid VarOrder.T 6596)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 18%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1886 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6610 time ltac:(lia) ltac:(lia)) (V6596 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1886 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6610 time ltac:(lia) ltac:(lia)) ?(V6596 time ltac:(lia) ltac:(lia)).
 unfold b9. destruct (guards 1886);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w9 := (if guards 1886 then w8 else w7).
 assert (V6621 : forall time, (Nat.add start 10 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 6621 (history time) = Some (Gval (Fuint 6) (from_N 6 w9))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 6621 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6612)) (@Eref VarOrder.T (@Eid VarOrder.T 6598)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 19%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1886 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6612 time ltac:(lia) ltac:(lia)) (V6598 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1886 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6612 time ltac:(lia) ltac:(lia)) ?(V6598 time ltac:(lia) ltac:(lia)).
 unfold w9. destruct (guards 1886);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 set b10 := (if guards 1707 then b9 else b0).
 assert (V7111 : forall time, (Nat.add start 11 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7111 (history time) = Some (Gval (Fuint 1) ([::b10]))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 7111 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6619)) (@Eref VarOrder.T (@Eid VarOrder.T 6517)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 32%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6619 time ltac:(lia) ltac:(lia)) (V6517 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6619 time ltac:(lia) ltac:(lia)) ?(V6517 time ltac:(lia) ltac:(lia)).
 unfold b10. destruct (guards 1707);cbn;try reflexivity;apply dut_decode_adapt;reflexivity. }
 set w10 := (if guards 1707 then w9 else w0).
 assert (V7112 : forall time, (Nat.add start 11 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 7112 (history time) = Some (Gval (Fuint 6) (from_N 6 w10))).
 { intros [|time] Lower Upper;try lia.
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes 7112 ((@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6621)) (@Eref VarOrder.T (@Eid VarOrder.T 6520)))));
 [exact reference_request_positions|exact reference_request_safety|apply (List.nth_error_In reference_request_nodes 33%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) (V6621 time ltac:(lia) ltac:(lia)) (V6520 time ltac:(lia) ltac:(lia)). unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite ?(Guards 1707 time ltac:(vm_compute;tauto) ltac:(lia) ltac:(lia)) ?(V6621 time ltac:(lia) ltac:(lia)) ?(V6520 time ltac:(lia) ltac:(lia)).
 unfold w10. destruct (guards 1707);cbn;try reflexivity;apply dut_decode_adapt;apply size_from_N. }
 intros time Lower Upper. split;[exact (V7111 time ltac:(lia) Upper)|exact (V7112 time ltac:(lia) Upper)].
Qed.
(* Request output aliases. *)
Theorem reference_request_alias_history field word invalid history limit start :
 (field < 4)%coq_nat -> size word = reference_request_field_width field ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find (7111+N.of_nat field) (history i) = Some (Gval (Fuint (reference_request_field_width field)) word)) ->
 forall time, (Nat.add start 3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (reference_request_wire_target field true) (history time) = Some (Gval (Fuint (reference_request_field_width field)) word).
Proof.
 intros Field Size Steps Source [|[|[|time]]] Lower Upper;try lia.
 eapply declared_wire_checked_value;[apply reference_request_wire_certificate;exact Field| |apply dut_decode_adapt;exact Size|apply Steps;lia].
 change (VM.find (reference_request_wire_target field false) (history (S (S time))) = Some (Gval (Fuint (reference_request_field_width field)) word)).
 eapply declared_wire_checked_value;[apply reference_request_wire_certificate;exact Field| |apply dut_decode_adapt;exact Size|apply Steps;lia].
 eapply (reference_redirect_ground_step reference_request_offsets reference_request_nodes _ (@Eref VarOrder.T (@Eid VarOrder.T (7111+N.of_nat field))));
 [exact reference_request_positions|exact reference_request_safety| | |apply Steps;lia].
 - apply (List.nth_error_In reference_request_nodes (Nat.add 36 field)).
   do 4 (destruct field as [|field];[vm_compute;reflexivity|]);lia.
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Source;lia.
Qed.
