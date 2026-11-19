Require Import CoreSocModel ComparisonNodes ReferenceRequestSpine ReferenceRedirectSpine SelectedZeroMux FormalDeclaredWireCheck.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition zero_read_expression_6520 :=(@Econst VarOrder.T (Fuint 6) [::false; false; false; false; false; false]).
Lemma zero_read_member_6520 :List.In(6520,zero_read_expression_6520)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_expression_6531 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6521)) (@Eref VarOrder.T (@Eid VarOrder.T 6520))).
Lemma zero_read_member_6531 :List.In(6531,zero_read_expression_6531)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_expression_6555 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6546)) (@Eref VarOrder.T (@Eid VarOrder.T 6531))).
Lemma zero_read_member_6555 :List.In(6555,zero_read_expression_6555)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_expression_6580 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6571)) (@Eref VarOrder.T (@Eid VarOrder.T 6555))).
Lemma zero_read_member_6580 :List.In(6580,zero_read_expression_6580)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_expression_6598 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 6580))).
Lemma zero_read_member_6598 :List.In(6598,zero_read_expression_6598)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_expression_6621 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6612)) (@Eref VarOrder.T (@Eid VarOrder.T 6598))).
Lemma zero_read_member_6621 :List.In(6621,zero_read_expression_6621)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_expression_7112 :=(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6621)) (@Eref VarOrder.T (@Eid VarOrder.T 6520))).
Lemma zero_read_member_7112 :List.In(7112,zero_read_expression_7112)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Definition zero_read_expression_7187 :=(@Eref VarOrder.T (@Eid VarOrder.T 7112)).
Lemma zero_read_member_7187 :List.In(7187,zero_read_expression_7187)reference_request_nodes.
Proof. vm_compute;tauto. Qed.
Theorem reference_zero_read_width_history invalid history limit start enabled :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::enabled])) ->
 (forall node,List.In node [::1970;1966;1962;1958;1886] ->forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1521(history t)=Some(Gval(Fuint 6)(zeros 6)).
Proof.
 intros Steps Enable Guards.
 assert(Base:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6520(history t)=Some(Gval(Fuint 6)(zeros 6))).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 6520 zero_read_expression_6520);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_6520| |apply Steps;lia]. intros site;reflexivity. }
 assert(Z6531:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6531(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 pose proof(Base t ltac:(lia) ltac:(lia))as Zero.
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6531 _ _ _ invalid(history t)(history(S t))false 6);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_6531| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6555:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6555(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6531 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6555 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_6555| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6580:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6580(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6555 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6580 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_6580| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6598:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6598(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6580 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6598 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_6598| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6621:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6621(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6598 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 6621 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_6621| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z7112:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 7112(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia. destruct(Z6621 t ltac:(lia) ltac:(lia))as[width Zero].
 destruct enabled;
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 7112 _ _ _ invalid(history t)(history(S t)));
 try exact reference_request_positions;try exact reference_request_safety;try exact zero_read_member_7112;
 try (intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];apply Enable;lia);
 try (intros site;exact Zero);try (intros site;apply Base;lia);try (apply Steps;lia). }
 assert(Z7187:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 7187(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia. destruct(Z7112 t ltac:(lia) ltac:(lia))as[width Zero]. exists width.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 7187 zero_read_expression_7187);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_7187|intros site;exact Zero|apply Steps;lia]. }
 assert(Z1711:forall t,(Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1711(history t)=Some(Gval(Fuint 6)(zeros 6))).
 { intros[|t] Lower Upper;try lia. destruct(Z7187 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply declared_wire_checked_value;[exact(reference_request_wire_certificate 1%nat false ltac:(lia))|exact Zero| |apply Steps;lia].
 cbn [adapt_hvalue_as_type]. rewrite zero_word_resize;reflexivity. }
 intros[|t] Lower Upper;try lia.
 pose proof(Z1711 t ltac:(lia) ltac:(lia))as Zero.
 eapply declared_wire_checked_value;[exact(reference_request_wire_certificate 1%nat true ltac:(lia))|exact Zero|reflexivity|apply Steps;lia].
Qed.
