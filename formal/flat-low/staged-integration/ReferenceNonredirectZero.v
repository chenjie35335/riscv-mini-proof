Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservedHistory ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence3 ReferenceRedirectSpineTypes ReferenceControlExpressions ReferenceControlStabilityHistory SelectedZeroMux.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition reference_nonredirect_guards :seq VarOrder.T := [::2357;2010;2004;1998;1992;1986;1980;1974].
Theorem reference_nonredirect_zero_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_flat_local_step invalid(history t)(history(S t))) ->
 (forall node,List.In node reference_nonredirect_guards ->forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6507(history t)=Some(Gval(Fuint width)(zeros width)).
Proof.
 intros Steps Guards.
 assert(Z6325:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6325(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6325 _ _ _ invalid(history t)(history(S t))false 1);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6325| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;reflexivity. }
 assert(Z6359:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6359(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6325 t ltac:(lia)ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6359 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6359| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6387:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6387(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6359 t ltac:(lia)ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6387 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6387| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6411:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6411(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6387 t ltac:(lia)ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6411 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6411| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6435:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6435(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6411 t ltac:(lia)ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6435 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6435| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6459:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6459(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6435 t ltac:(lia)ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6459 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6459| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6483:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6483(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6459 t ltac:(lia)ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6483 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6483| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;exact Zero. }
 assert(Z6507:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 6507(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia.
 destruct(Z6483 t ltac:(lia)ltac:(lia))as[width Zero].
 eapply(selected_zero_mux reference_control_3_offsets reference_control_3_nodes 6507 _ _ _ invalid(history t)(history(S t))false width);
 [exact reference_control_3_positions|exact reference_control_3_safety|exact reference_control_member_6507| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn[reference_nonredirect_guards List.In];tauto|lia|lia].
 - intros site;exact Zero. }
 exact Z6507.
Qed.
Theorem reference_nonredirect_zero_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (forall node,List.In node reference_nonredirect_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::false])) ->
 exists width,VM.find 6507(top_environment observed)=Some(Gval(Fuint width)(zeros width)).
Proof.
 intros Observe Legal Guards.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Stable:forall node,List.In node reference_nonredirect_guards ->forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=VM.find node(history 9259%nat)).
 { intros node Member t Lower Upper. cbn[reference_nonredirect_guards List.In]in Member.
 destruct Member as[<-|Member];[apply(reference_control_stable_2357_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 destruct Member as[<-|Member];[apply(reference_control_stable_2010_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 destruct Member as[<-|Member];[apply(reference_control_stable_2004_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 destruct Member as[<-|Member];[apply(reference_control_stable_1998_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 destruct Member as[<-|Member];[apply(reference_control_stable_1992_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 destruct Member as[<-|Member];[apply(reference_control_stable_1986_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 destruct Member as[<-|Member];[apply(reference_control_stable_1980_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 destruct Member as[<-|Member];[apply(reference_control_stable_1974_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps t 9259%nat);lia|].
 contradiction. }
 rewrite <-Last. apply(reference_nonredirect_zero_history _ history 9259 200 Steps).
 - intros node Member t Lower Upper. rewrite(Stable node Member t Lower Upper)Last. exact(Guards node Member).
 - vm_compute;lia.
 - lia.
Qed.
Theorem reference_nonredirect_false_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 (forall node,List.In node reference_nonredirect_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 6507(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Guards.
 destruct(reference_nonredirect_zero_observed memory inputs k observed Observe Legal Guards)as[width Zero].
 destruct(reference_redirect_spine_types_observed memory inputs k observed 21%nat Observe Legal ltac:(lia))as[value[Value Typed]].
 change(VM.find 6507(top_environment observed)=Some value)in Value.
 rewrite Zero in Value;inversion Value;subst value.
 cbn[type_of_val]in Typed. inversion Typed;subst width. exact Zero.
Qed.
