Require Import ReferenceImmediateTypes ReferenceControlExpressions ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence3 ReferenceRedirectSpine FormalSuccessfulNodeEvaluation SelectedNodeSafety FormalTypedNodeEquation ScalarSinkTypes DUTRedirectDecode FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia Arith.Wf_nat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_redirect_type_nodes := [::(6314,reference_control_expr_6314);(6325,reference_control_expr_6325);(6346,reference_control_expr_6346);(6359,reference_control_expr_6359);(6373,reference_control_expr_6373);(6377,reference_control_expr_6377);(6387,reference_control_expr_6387);(6397,reference_control_expr_6397);(6401,reference_control_expr_6401);(6411,reference_control_expr_6411);(6421,reference_control_expr_6421);(6425,reference_control_expr_6425);(6435,reference_control_expr_6435);(6445,reference_control_expr_6445);(6449,reference_control_expr_6449);(6459,reference_control_expr_6459);(6469,reference_control_expr_6469);(6473,reference_control_expr_6473);(6483,reference_control_expr_6483);(6493,reference_control_expr_6493);(6497,reference_control_expr_6497);(6507,reference_control_expr_6507)].
Definition reference_redirect_spine_node i :=fst(nth (0,(@Econst VarOrder.T(Fuint 1)[::false]))reference_redirect_type_nodes i).
Definition reference_redirect_spine_expression i :=snd(nth (0,(@Econst VarOrder.T(Fuint 1)[::false]))reference_redirect_type_nodes i).
Definition reference_redirect_spine_rank i :=S i.
Definition reference_redirect_spine_dependencies := [::[::];[::6314];[::6325];[::6346;6325];[::6359];[::6373;6359];[::6377;6359];[::6387];[::6397;6387];[::6401;6387];[::6411];[::6421;6411];[::6425;6411];[::6435];[::6445;6435];[::6449;6435];[::6459];[::6469;6459];[::6473;6459];[::6483];[::6493;6483];[::6497;6483]].
Definition reference_redirect_spine_refs i :=nth [::]reference_redirect_spine_dependencies i.
Lemma reference_redirect_spine_type_plan i :(i<22)%coq_nat ->
 immediate_expression_check(fun _=>1%nat)(reference_redirect_spine_expression i)=Some(1%nat,reference_redirect_spine_refs i).
Proof. intro Bound. do 22(destruct i as[|i];[vm_compute;reflexivity|]);lia. Qed.
Lemma reference_redirect_spine_type_member i :(i<22)%coq_nat ->
 List.In(reference_redirect_spine_node i,reference_redirect_spine_expression i)reference_control_3_nodes.
Proof.
 intro Bound.
 destruct i as[|i];[exact reference_control_member_6314|].
 destruct i as[|i];[exact reference_control_member_6325|].
 destruct i as[|i];[exact reference_control_member_6346|].
 destruct i as[|i];[exact reference_control_member_6359|].
 destruct i as[|i];[exact reference_control_member_6373|].
 destruct i as[|i];[exact reference_control_member_6377|].
 destruct i as[|i];[exact reference_control_member_6387|].
 destruct i as[|i];[exact reference_control_member_6397|].
 destruct i as[|i];[exact reference_control_member_6401|].
 destruct i as[|i];[exact reference_control_member_6411|].
 destruct i as[|i];[exact reference_control_member_6421|].
 destruct i as[|i];[exact reference_control_member_6425|].
 destruct i as[|i];[exact reference_control_member_6435|].
 destruct i as[|i];[exact reference_control_member_6445|].
 destruct i as[|i];[exact reference_control_member_6449|].
 destruct i as[|i];[exact reference_control_member_6459|].
 destruct i as[|i];[exact reference_control_member_6469|].
 destruct i as[|i];[exact reference_control_member_6473|].
 destruct i as[|i];[exact reference_control_member_6483|].
 destruct i as[|i];[exact reference_control_member_6493|].
 destruct i as[|i];[exact reference_control_member_6497|].
 destruct i as[|i];[exact reference_control_member_6507|].
 lia.
Qed.
Lemma reference_redirect_spine_type_predecessors i node :(i<22)%coq_nat ->List.In node(reference_redirect_spine_refs i) ->
 exists j,(j<i)%coq_nat /\(j<22)%coq_nat /\reference_redirect_spine_node j=node.
Proof.
 intro Bound.
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 0%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 2%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 4%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 5%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 7%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 8%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 11%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 13%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 14%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 16%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 17%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 19%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_redirect_spine_refs reference_redirect_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 lia.
Qed.
Theorem reference_redirect_spine_type_step i invalid old result :(i<22)%coq_nat ->
 (forall node,List.In node(reference_redirect_spine_refs i) ->exists value,VM.find node old=Some value /\type_of_val value=Gtyp(Fuint 1)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find(reference_redirect_spine_node i)result=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Bound Dependencies Step.
 destruct(selected_node_safe_position flat_memories flat_statements reference_control_3_offsets flat_statements reference_control_3_nodes _ _ reference_control_3_positions reference_control_3_safety(reference_redirect_spine_type_member i Bound))as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Position Step)as[value Eval]. rewrite add0n in Eval.
 assert(Typed:type_of_val value=Gtyp(Fuint 1)).
 { eapply immediate_expression_check_sound;[exact(reference_redirect_spine_type_plan i Bound)|exact Dependencies|exact Eval]. }
 exists value;split;[|exact Typed].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Theorem reference_redirect_spine_types_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall i,(i<22)%coq_nat ->forall t,(Nat.add start(reference_redirect_spine_rank i)<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find(reference_redirect_spine_node i)(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Steps i. induction i using lt_wf_ind. intros Bound[|t]Lower Upper.
 - unfold reference_redirect_spine_rank in Lower;lia.
 - eapply reference_redirect_spine_type_step;[exact Bound| |apply Steps;lia].
   intros node Member. destruct(reference_redirect_spine_type_predecessors i node Bound Member)as[j[Before[J Node]]].
   rewrite<-Node. apply(H j Before J t);unfold reference_redirect_spine_rank in *;lia.
Qed.
Theorem reference_redirect_spine_types_observed memory inputs k observed i :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->(i<22)%coq_nat ->
 exists value,VM.find(reference_redirect_spine_node i)(top_environment observed)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Observe Legal Bound.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite<-Last. assert(Big:(22<=9259)%coq_nat)by(vm_compute;lia). apply(reference_redirect_spine_types_history _ history 9259 0 Steps i Bound 9259);unfold reference_redirect_spine_rank;cbn[Nat.add];lia.
Qed.
Corollary reference_redirect_spine_6314_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6314(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 0%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6325_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6325(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 1%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6346_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6346(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 2%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6359_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6359(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 3%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6373_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6373(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 4%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6377_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6377(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 5%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6387_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6387(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 6%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6397_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6397(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 7%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6401_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6401(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 8%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6411_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6411(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 9%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6421_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 11<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6421(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 10%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6425_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 12<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6425(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 11%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6435_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 13<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6435(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 12%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6445_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 14<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6445(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 13%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6449_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 15<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6449(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 14%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6459_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 16<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6459(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 15%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6469_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 17<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6469(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 16%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6473_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 18<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6473(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 17%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6483_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 19<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6483(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 18%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6493_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 20<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6493(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 19%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6497_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 21<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6497(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 20%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_redirect_spine_6507_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 22<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6507(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_redirect_spine_types_history invalid history limit start Steps 21%nat ltac:(lia)t Lower Upper). Qed.
