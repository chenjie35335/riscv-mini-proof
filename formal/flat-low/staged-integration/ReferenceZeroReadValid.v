Require Import CoreSocModel ComparisonNodes ReferenceRequestSpine ReferenceRedirectSpine SelectedZeroMux FormalDeclaredWireCheck.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition zero_read_valid_expression_6517 :=(@Econst VarOrder.T (Fuint 1) [::false]).
Lemma zero_read_valid_member_6517 :List.In(6517,zero_read_valid_expression_6517)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_valid_expression_6528 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6518)) (@Eref VarOrder.T (@Eid VarOrder.T 6517))).
Lemma zero_read_valid_member_6528 :List.In(6528,zero_read_valid_expression_6528)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_valid_expression_6553 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6544)) (@Eref VarOrder.T (@Eid VarOrder.T 6528))).
Lemma zero_read_valid_member_6553 :List.In(6553,zero_read_valid_expression_6553)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_valid_expression_6578 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6569)) (@Eref VarOrder.T (@Eid VarOrder.T 6553))).
Lemma zero_read_valid_member_6578 :List.In(6578,zero_read_valid_expression_6578)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_valid_expression_6596 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6578))).
Lemma zero_read_valid_member_6596 :List.In(6596,zero_read_valid_expression_6596)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_valid_expression_6619 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6610)) (@Eref VarOrder.T (@Eid VarOrder.T 6596))).
Lemma zero_read_valid_member_6619 :List.In(6619,zero_read_valid_expression_6619)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_valid_expression_7111 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6619)) (@Eref VarOrder.T (@Eid VarOrder.T 6517))).
Lemma zero_read_valid_member_7111 :List.In(7111,zero_read_valid_expression_7111)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_valid_expression_7186 :=(@Eref VarOrder.T (@Eid VarOrder.T 7111)).
Lemma zero_read_valid_member_7186 :List.In(7186,zero_read_valid_expression_7186)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Theorem reference_zero_read_valid_history invalid history limit start enabled :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::enabled])) ->
 (forall node,List.In node [::1970;1966;1962;1958;1886] ->forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1519(history t)=Some(Gval(Fuint 1)(zeros 1)).
Proof.
 intros Steps Enable Guards.
 assert(Base:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6517(history t)=Some(Gval(Fuint 1)(zeros 1))).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 6517 zero_read_valid_expression_6517);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_valid_member_6517| |apply Steps;lia]. intros site;reflexivity. }
 assert(Z6528:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6528(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 pose proof(Base t ltac:(lia) ltac:(lia))as Zero.
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6528 _ _ _ invalid(history t)(history(S t))false 1);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_valid_member_6528| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6553:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6553(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6528 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6553 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_valid_member_6553| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6578:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6578(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6553 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6578 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_valid_member_6578| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6596:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6596(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6578 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6596 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_valid_member_6596| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6619:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6619(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6596 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6619 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_valid_member_6619| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z7111:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 7111(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia. destruct(Z6619 t ltac:(lia) ltac:(lia))as[width Zero].
 destruct enabled;
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 7111 _ _ _ invalid(history t)(history(S t)));
 try exact reference_request_positions;try exact reference_request_safety;try exact zero_read_valid_member_7111;
 try (intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];apply Enable;lia);
 try (intros site;exact Zero);try (intros site;apply Base;lia);try (apply Steps;lia). }
 assert(Z7186:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 7186(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia. destruct(Z7111 t ltac:(lia) ltac:(lia))as[width Zero]. exists width.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 7186 zero_read_valid_expression_7186);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_valid_member_7186|intros site;exact Zero|apply Steps;lia]. }
 assert(Z1709:forall t,(Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1709(history t)=Some(Gval(Fuint 1)(zeros 1))).
 { intros[|t] Lower Upper;try lia. destruct(Z7186 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply declared_wire_checked_value;[exact(reference_request_wire_certificate 0%nat false ltac:(lia))|exact Zero| |apply Steps;lia].
 cbn [adapt_hvalue_as_type]. rewrite zero_word_resize;reflexivity. }
 intros[|t] Lower Upper;try lia.
 pose proof(Z1709 t ltac:(lia) ltac:(lia))as Zero.
 eapply declared_wire_checked_value;[exact(reference_request_wire_certificate 0%nat true ltac:(lia))|exact Zero|reflexivity|apply Steps;lia].
Qed.
