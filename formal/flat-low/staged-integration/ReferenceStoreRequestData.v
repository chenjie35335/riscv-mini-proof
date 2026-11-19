Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode FormalDeclaredWireCheck ReferenceStoreData.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_store_request_data_nodes : seq(VarOrder.T*hfexpr VarOrder.T) := [::(6647,(@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]));(6648,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Eref VarOrder.T (@Eid VarOrder.T 6635)) (@Eref VarOrder.T (@Eid VarOrder.T 6647))));(6662,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Eref VarOrder.T (@Eid VarOrder.T 6655)) (@Eref VarOrder.T (@Eid VarOrder.T 6648))));(6671,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6662)) (@Eref VarOrder.T (@Eid VarOrder.T 6648))));(6686,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Eref VarOrder.T (@Eid VarOrder.T 6679)) (@Eref VarOrder.T (@Eid VarOrder.T 6671))));(6695,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6686)) (@Eref VarOrder.T (@Eid VarOrder.T 6671))));(7115,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6695)) (@Eref VarOrder.T (@Eid VarOrder.T 6647))));(7190,(@Eref VarOrder.T (@Eid VarOrder.T 7115)))].
Definition reference_store_request_data_offsets := [::6726%nat;0%nat;13%nat;8%nat;14%nat;8%nat;419%nat;74%nat].
Lemma reference_store_request_data_positions : select_node_offsets reference_store_request_data_offsets flat_statements=Some reference_store_request_data_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_store_request_data_safety : selected_node_safety flat_memories flat_statements reference_store_request_data_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_store_request_wire_1716 : declared_wire_check flat_memories flat_statements 1795 5560 1716 7190 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_store_request_wire_1526 : declared_wire_check flat_memories flat_statements 1605 6137 1526 1716 32=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Shared store request data semantics. *)
Lemma store_data_mux_eval invalid site old condition yes no width y n result bit :
 (width<=32)%nat ->size n=32%nat ->
 VM.find condition old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find yes old=Some(Gval(Fuint width)y) ->VM.find no old=Some(Gval(Fuint 32)n) ->
 adapt_hvalue_as_type(Gval(Fuint width)y)(Gtyp(Fuint 32))=Some(Gval(Fuint 32)result) ->
 eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories
 (@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T condition))(@Eref VarOrder.T(@Eid VarOrder.T yes))(@Eref VarOrder.T(@Eid VarOrder.T no)))old old=
 Some(Gval(Fuint 32)(if bit then result else n)).
Proof.
 intros Width Size Condition Yes No Adapt.
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Condition.
 destruct bit;cbn[is_zero eval_hfexpr_validif_policy eval_href_validif_policy];unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Yes No;
 cbn[option_map make_ftype_explicit extend_hvalue_as_type type_of_val ftype_mux fgtyp_mux];rewrite ?(maxn_idPr Width) ?(maxn_idPl Width).
 - exact Adapt.
 - apply dut_decode_adapt;exact Size.
Qed.
Definition reference_store_request_piece width word := zext_to 32(take 32(take width word)).
Lemma reference_store_request_piece_size width word :size(reference_store_request_piece width word)=32%nat.
Proof. unfold reference_store_request_piece,zext_to. rewrite size_zext. apply subnKC. rewrite size_take. apply geq_minl. Qed.
Definition reference_store_request_word (guards:VarOrder.T->bool) word :=
 let v0:=zeros 32 in
 let v1:=if guards 1951 then reference_store_request_piece 8 word else v0 in
 let v2:=if guards 2723 then reference_store_request_piece 16 word else v1 in
 let v3:=if guards 1946 then v2 else v1 in
 let v4:=if guards 2708 then reference_store_request_piece 32 word else v3 in
 let v5:=if guards 1941 then v4 else v3 in
 if guards 1707 then v5 else v0.
(* Store data batch history. *)
Definition reference_store_request_data_guards : seq VarOrder.T := [::1951;2723;1946;2708;1941;1707].
Theorem reference_store_request_data_history invalid history limit start guards word :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2804(history t)=Some(Gval(Fuint 32)word)) ->
 (forall node t,List.In node reference_store_request_data_guards ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])) ->
 forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 7115(history t)=Some(Gval(Fuint 32)(reference_store_request_word guards word)).
Proof.
 intros Steps Source Guards.
 assert(Pieces:forall lane t,(lane<3)%coq_nat ->(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find(reference_store_data_base lane+1)(history t)=Some(Gval(Fuint(reference_store_data_width lane))(take(reference_store_data_width lane)word))).
 { intros lane [|[|t]] Lane Lower Upper;try lia.
 exact(reference_store_data_steps lane invalid(history t)(history(S t))(history(S(S t)))word Lane(Source t ltac:(lia)ltac:(lia))(Steps t ltac:(lia))(Steps(S t)ltac:(lia))). }
 set v0 := (zeros 32).
 assert(Size0:size v0=32%nat).
 { reflexivity. }
 assert(V0:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6647(history t)=Some(Gval(Fuint 32)v0)).
 { intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 6647 (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes 0)));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 0%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site;reflexivity. }
 set v1 := (if guards 1951 then reference_store_request_piece 8 word else v0).
 assert(Size1:size v1=32%nat).
 { unfold v1. destruct(guards 1951);[apply reference_store_request_piece_size|exact Size0]. }
 assert(V1:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6648(history t)=Some(Gval(Fuint 32)v1)).
 { intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 6648 (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes 1)));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 1%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold v1. eapply(store_data_mux_eval _ _ _ 1951 6635 6647 8);
 [reflexivity|exact Size0|apply Guards;[vm_compute;tauto|lia|lia]| |apply V0;lia|].
 - exact(Pieces 2 t ltac:(vm_compute;lia)ltac:(lia)ltac:(lia)).
 - reflexivity. }
 set v2 := (if guards 2723 then reference_store_request_piece 16 word else v1).
 assert(Size2:size v2=32%nat).
 { unfold v2. destruct(guards 2723);[apply reference_store_request_piece_size|exact Size1]. }
 assert(V2:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6662(history t)=Some(Gval(Fuint 32)v2)).
 { intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 6662 (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes 2)));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 2%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold v2. eapply(store_data_mux_eval _ _ _ 2723 6655 6648 16);
 [reflexivity|exact Size1|apply Guards;[vm_compute;tauto|lia|lia]| |apply V1;lia|].
 - exact(Pieces 1 t ltac:(vm_compute;lia)ltac:(lia)ltac:(lia)).
 - reflexivity. }
 set v3 := (if guards 1946 then v2 else v1).
 assert(Size3:size v3=32%nat).
 { unfold v3. destruct(guards 1946);[exact Size2|exact Size1]. }
 assert(V3:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6671(history t)=Some(Gval(Fuint 32)v3)).
 { intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 6671 (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes 3)));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 3%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold v3. eapply(store_data_mux_eval _ _ _ 1946 6662 6648 32);
 [reflexivity|exact Size1|apply Guards;[vm_compute;tauto|lia|lia]| |apply V1;lia|].
 - apply V2;lia.
 - apply dut_decode_adapt;exact Size2. }
 set v4 := (if guards 2708 then reference_store_request_piece 32 word else v3).
 assert(Size4:size v4=32%nat).
 { unfold v4. destruct(guards 2708);[apply reference_store_request_piece_size|exact Size3]. }
 assert(V4:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6686(history t)=Some(Gval(Fuint 32)v4)).
 { intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 6686 (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes 4)));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 4%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold v4. eapply(store_data_mux_eval _ _ _ 2708 6679 6671 32);
 [reflexivity|exact Size3|apply Guards;[vm_compute;tauto|lia|lia]| |apply V3;lia|].
 - exact(Pieces 0 t ltac:(vm_compute;lia)ltac:(lia)ltac:(lia)).
 - reflexivity. }
 set v5 := (if guards 1941 then v4 else v3).
 assert(Size5:size v5=32%nat).
 { unfold v5. destruct(guards 1941);[exact Size4|exact Size3]. }
 assert(V5:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6695(history t)=Some(Gval(Fuint 32)v5)).
 { intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 6695 (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes 5)));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 5%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold v5. eapply(store_data_mux_eval _ _ _ 1941 6686 6671 32);
 [reflexivity|exact Size3|apply Guards;[vm_compute;tauto|lia|lia]| |apply V3;lia|].
 - apply V4;lia.
 - apply dut_decode_adapt;exact Size4. }
 set v6 := (if guards 1707 then v5 else v0).
 assert(Size6:size v6=32%nat).
 { unfold v6. destruct(guards 1707);[exact Size5|exact Size0]. }
 assert(V6:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7115(history t)=Some(Gval(Fuint 32)v6)).
 { intros [|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step reference_store_request_data_offsets reference_store_request_data_nodes 7115 (snd(nth (0,@Econst VarOrder.T(Fuint 1)[::false])reference_store_request_data_nodes 6)));[exact reference_store_request_data_positions|exact reference_store_request_data_safety|apply(List.nth_error_In reference_store_request_data_nodes 6%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold v6. eapply(store_data_mux_eval _ _ _ 1707 6695 6647 32);
 [reflexivity|exact Size0|apply Guards;[vm_compute;tauto|lia|lia]| |apply V0;lia|].
 - apply V5;lia.
 - apply dut_decode_adapt;exact Size5. }
 intros t Lower Upper. exact(V6 t Lower Upper).
Qed.
