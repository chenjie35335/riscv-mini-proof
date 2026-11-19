Require Import ReferenceControlStabilityHistory.
Require Import CoreSocModel ComparisonNodes ReferencePCTargetStability SelectedNodeSafety ReferenceControlNodeGeneric ReferenceControlGroundExpressions.
From Coq Require Import NArith List Lia Arith.Wf_nat PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma ref_pc_target_member i :(i<41)%coq_nat ->List.In(ref_pc_target_node i,ref_pc_target_expression i)ref_pc_target_nodes.
Proof. intro Bound. apply(List.nth_error_In ref_pc_target_nodes i).
 do 41(destruct i as[|i];[vm_compute;reflexivity|]);lia. Qed.
Lemma ref_pc_target_rank_positive i :(i<41)%coq_nat ->(0<ref_pc_target_rank i)%coq_nat.
Proof. intro Bound. do 41(destruct i as[|i];[vm_compute;lia|]);lia. Qed.
Theorem ref_pc_target_history inputs path history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall node t,List.In node ref_pc_target_cuts ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find node(history t)=Some value /\type_of_val value=Gtyp ground) ->
 (forall node t u,List.In node ref_pc_target_cuts ->(start<=t)%coq_nat ->(start<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history u)) ->
 forall i,(i<41)%coq_nat ->
 (forall t,(Nat.add start(ref_pc_target_rank i)<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find(ref_pc_target_node i)(history t)=Some value /\type_of_val value=Gtyp ground) /\
 (forall t u,(Nat.add start(ref_pc_target_rank i)<=t)%coq_nat ->(Nat.add start(ref_pc_target_rank i)<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find(ref_pc_target_node i)(history t)=VM.find(ref_pc_target_node i)(history u)).
Proof.
 intros Steps CutGround CutStable i. induction i using lt_wf_ind. intro Bound.
 pose proof(ref_pc_target_rank_positive i Bound)as Positive.
 destruct(selected_node_safe_position flat_memories flat_statements ref_pc_target_offsets flat_statements ref_pc_target_nodes _ _ ref_pc_target_positions ref_pc_target_safety(ref_pc_target_member i Bound))as[count[tail[Position[Safe Nonreg]]]].
 assert(Ready:forall t,(Nat.add start(ref_pc_target_rank i)<=S t)%coq_nat ->(S t<=limit)%coq_nat ->reference_control_ready(history t)(ref_pc_target_expression i)).
 { intros t Lower Upper. apply(ref_pc_target_ready i(history t)Bound). intros node Member.
 destruct(ref_pc_target_predecessors i node Bound Member)as[Cut|[j[Prior[Inside[Node Rank]]]]].
 - apply(CutGround node t Cut);lia.
 - rewrite <-Node. apply(proj1(H j Prior Inside));lia. }
 split.
 - intros[|t]Lower Upper;[lia|].
 exact(reference_control_node_ground count tail(ref_pc_target_node i)(ref_pc_target_expression i)inputs path(history t)(history t)(history(S t))Position Safe Nonreg(Ready t Lower Upper)(Steps t ltac:(lia))).
 - intros[|t][|u]Lower Other Upper OtherUpper;try lia.
 eapply(reference_control_node_congruent count tail(ref_pc_target_node i)(ref_pc_target_expression i)inputs path(history t)(history u)(history(S t))(history(S u)));[exact Position|exact Safe|exact Nonreg|apply Ready;assumption| |apply Steps;lia|apply Steps;lia].
 apply(ref_pc_target_eval_equal i inputs path(history t)(history u)Bound). intros node Member.
 destruct(ref_pc_target_predecessors i node Bound Member)as[Cut|[j[Prior[Inside[Node Rank]]]]].
 + apply(CutStable node t u Cut);lia.
 + rewrite <-Node. apply(proj2(H j Prior Inside));lia.
Qed.
Theorem ref_pc_target_cut_facts inputs path history limit bit :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall node,List.In node ref_pc_target_cuts ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find node(history t)=Some value /\type_of_val value=Gtyp ground) /\
 (forall t u,(200<=t)%coq_nat ->(200<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history u)).
Proof. intros Resets Steps node Member.
 cbn[ref_pc_target_cuts List.In]in Member. repeat destruct Member as[<-|Member];try contradiction.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1974_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1974_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1980_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1980_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1986_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1986_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1992_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1992_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_1998_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_1998_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2004_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2004_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2010_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2010_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2209_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2209_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2357_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2357_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2552_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2552_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2806_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2806_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2812_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2812_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2825_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2825_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2830_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2830_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2847_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2847_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2850_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2850_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2867_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2867_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2872_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2872_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2889_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2889_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2892_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2892_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2909_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2909_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2912_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2912_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2929_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2929_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2949_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2949_history inputs path history limit bit Resets Steps t u);lia.
 - split.
 + intros t Lower Upper. apply(reference_control_ground_2966_history inputs path history limit bit Resets Steps t);lia.
 + intros t u Lower Other Upper OtherUpper. apply(reference_control_stable_2966_history inputs path history limit bit Resets Steps t u);lia.
Qed.
Theorem reference_pc_target_6508_stable inputs path history limit bit :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::bit])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t u,(225<=t)%coq_nat ->(225<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find 6508(history t)=VM.find 6508(history u).
Proof.
 intros Resets Steps t u Lower Other Upper OtherUpper.
 pose proof(ref_pc_target_cut_facts inputs path history limit bit Resets Steps)as Cuts.
 destruct(ref_pc_target_history inputs path history limit 200 Steps
 (fun node t Member Lower Upper=>proj1(Cuts node Member)t Lower Upper)
 (fun node t u Member Lower Other Upper OtherUpper=>proj2(Cuts node Member)t u Lower Other Upper OtherUpper)
 40%nat ltac:(lia))as[Ground Stable].
 change(forall t u,(225<=t)%coq_nat ->(225<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find 6508(history t)=VM.find 6508(history u))in Stable.
 exact(Stable t u Lower Other Upper OtherUpper).
Qed.
