Require Import ReferenceImmediateTypes ReferenceEventSpine FormalSuccessfulNodeEvaluation SelectedNodeSafety FormalTypedNodeEquation ScalarSinkTypes DUTRedirectDecode FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import NArith List Lia Arith.Wf_nat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_event_spine_node i :=fst(nth (0,(@Econst VarOrder.T(Fuint 1)[::false]))reference_event_nodes i).
Definition reference_event_spine_expression i :=snd(nth (0,(@Econst VarOrder.T(Fuint 1)[::false]))reference_event_nodes i).
Definition reference_event_spine_rank i :=S i.
Definition reference_event_spine_dependencies := [::[::];[::6323];[::6332];[::6354;6332];[::6366];[::6376;6366];[::6380;6366];[::6390];[::6400;6390];[::6404;6390];[::6414];[::6424;6414];[::6428;6414];[::6438];[::6448;6438];[::6452;6438];[::6462];[::6472;6462];[::6476;6462];[::6486];[::6496;6486];[::6500;6486];[::6510];[::6523;6510];[::6533];[::6548;6533];[::6557];[::6573;6557];[::6582];[::6589;6582];[::6595];[::6614;6595];[::6623];[::6630;6623];[::6640];[::6663;6640];[::6672];[::6687;6672];[::6696];[::6701];[::6704];[::6705];[::6706;6701];[::6709];[::6778];[::6779]].
Definition reference_event_spine_refs i :=nth [::]reference_event_spine_dependencies i.
Lemma reference_event_spine_type_plan i :(i<46)%coq_nat ->
 immediate_expression_check(fun _=>1%nat)(reference_event_spine_expression i)=Some(1%nat,reference_event_spine_refs i).
Proof. intro Bound. do 46(destruct i as[|i];[vm_compute;reflexivity|]);lia. Qed.
Lemma reference_event_spine_type_member i :(i<46)%coq_nat ->
 List.In(reference_event_spine_node i,reference_event_spine_expression i)reference_event_nodes.
Proof.
 intro Bound. apply(List.nth_error_In reference_event_nodes i).
 do 46(destruct i as[|i];[vm_compute;reflexivity|]);lia.
Qed.
Lemma reference_event_spine_type_predecessors i node :(i<46)%coq_nat ->List.In node(reference_event_spine_refs i) ->
 exists j,(j<i)%coq_nat /\(j<46)%coq_nat /\reference_event_spine_node j=node.
Proof.
 intro Bound.
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 0%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 2%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 4%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 5%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 7%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 8%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 11%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 13%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 14%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 16%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 17%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 19%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 21%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 22%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 21%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 23%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 24%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 23%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 26%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 27%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 28%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 27%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 29%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 30%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 29%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 31%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 32%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 31%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 33%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 34%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 33%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 36%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 37%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 38%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 39%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 40%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 41%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - exists 38%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 42%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 43%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 destruct i as[|i].
 { cbn [reference_event_spine_refs reference_event_spine_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - exists 44%nat;vm_compute;repeat split;try reflexivity;lia.
 - contradiction. }
 lia.
Qed.
Theorem reference_event_spine_type_step i invalid old result :(i<46)%coq_nat ->
 (forall node,List.In node(reference_event_spine_refs i) ->exists value,VM.find node old=Some value /\type_of_val value=Gtyp(Fuint 1)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find(reference_event_spine_node i)result=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Bound Dependencies Step.
 destruct(selected_node_safe_position flat_memories flat_statements reference_event_offsets flat_statements reference_event_nodes _ _ reference_event_positions reference_event_safety(reference_event_spine_type_member i Bound))as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false old result Position Step)as[value Eval]. rewrite add0n in Eval.
 assert(Typed:type_of_val value=Gtyp(Fuint 1)).
 { eapply immediate_expression_check_sound;[exact(reference_event_spine_type_plan i Bound)|exact Dependencies|exact Eval]. }
 exists value;split;[|exact Typed].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Theorem reference_event_spine_types_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall i,(i<46)%coq_nat ->forall t,(Nat.add start(reference_event_spine_rank i)<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find(reference_event_spine_node i)(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Steps i. induction i using lt_wf_ind. intros Bound[|t]Lower Upper.
 - unfold reference_event_spine_rank in Lower;lia.
 - eapply reference_event_spine_type_step;[exact Bound| |apply Steps;lia].
   intros node Member. destruct(reference_event_spine_type_predecessors i node Bound Member)as[j[Before[J Node]]].
   rewrite<-Node. apply(H j Before J t);unfold reference_event_spine_rank in *;lia.
Qed.
Theorem reference_event_spine_types_observed memory inputs k observed i :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->(i<46)%coq_nat ->
 exists value,VM.find(reference_event_spine_node i)(top_environment observed)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros Observe Legal Bound.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite<-Last. assert(Big:(46<=9259)%coq_nat)by(vm_compute;lia). apply(reference_event_spine_types_history _ history 9259 0 Steps i Bound 9259);unfold reference_event_spine_rank;cbn[Nat.add];lia.
Qed.
Corollary reference_event_spine_6323_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6323(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 0%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6332_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6332(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 1%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6354_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6354(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 2%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6366_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6366(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 3%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6376_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6376(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 4%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6380_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6380(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 5%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6390_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6390(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 6%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6400_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6400(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 7%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6404_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6404(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 8%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6414_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6414(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 9%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6424_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 11<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6424(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 10%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6428_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 12<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6428(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 11%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6438_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 13<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6438(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 12%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6448_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 14<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6448(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 13%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6452_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 15<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6452(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 14%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6462_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 16<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6462(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 15%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6472_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 17<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6472(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 16%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6476_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 18<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6476(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 17%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6486_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 19<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6486(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 18%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6496_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 20<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6496(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 19%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6500_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 21<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6500(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 20%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6510_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 22<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6510(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 21%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6523_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 23<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6523(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 22%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6533_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 24<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6533(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 23%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6548_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 25<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6548(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 24%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6557_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 26<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6557(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 25%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6573_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 27<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6573(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 26%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6582_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 28<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6582(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 27%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6589_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 29<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6589(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 28%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6595_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 30<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6595(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 29%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6614_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 31<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6614(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 30%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6623_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 32<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6623(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 31%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6630_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 33<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6630(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 32%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6640_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 34<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6640(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 33%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6663_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 35<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6663(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 34%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6672_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 36<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6672(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 35%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6687_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 37<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6687(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 36%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6696_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 38<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6696(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 37%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6701_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 39<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6701(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 38%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6704_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 40<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6704(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 39%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6705_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 41<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6705(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 40%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6706_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 42<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6706(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 41%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6709_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 43<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6709(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 42%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6778_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 44<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6778(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 43%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6779_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 45<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6779(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 44%nat ltac:(lia)t Lower Upper). Qed.
Corollary reference_event_spine_6780_type_history invalid history limit start t :
 (forall j,(j<limit)%coq_nat ->formal_value_iter invalid flat_memories(history j)false(history j)flat_statements=Some(history(S j))) ->
 (Nat.add start 46<=t)%coq_nat ->(t<=limit)%coq_nat ->
 exists value,VM.find 6780(history t)=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof. intros Steps Lower Upper;exact(reference_event_spine_types_history invalid history limit start Steps 45%nat ltac:(lia)t Lower Upper). Qed.
