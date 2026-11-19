Require Import CoreSocModel ComparisonNodes ReferenceBankCycleStability SelectedNodeSafety ReferenceControlNodeGeneric ReferenceControlGroundExpressions.
From Coq Require Import NArith List Lia Arith.Wf_nat PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma ref_bank_cycle_member i :(i<438)%coq_nat ->List.In(ref_bank_cycle_node i,ref_bank_cycle_expression i)ref_bank_cycle_nodes.
Proof. intro Bound. apply(List.nth_error_In ref_bank_cycle_nodes i).
 do 438(destruct i as[|i];[vm_compute;reflexivity|]);lia. Qed.
Lemma ref_bank_cycle_rank_positive i :(i<438)%coq_nat ->(0<ref_bank_cycle_rank i)%coq_nat.
Proof. intro Bound. do 438(destruct i as[|i];[vm_compute;lia|]);lia. Qed.
Theorem ref_bank_cycle_history inputs path history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall node t,List.In node ref_bank_cycle_cuts ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find node(history t)=Some value /\type_of_val value=Gtyp ground) ->
 (forall node t u,List.In node ref_bank_cycle_cuts ->(start<=t)%coq_nat ->(start<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find node(history t)=VM.find node(history u)) ->
 forall i,(i<438)%coq_nat ->
 (forall t,(Nat.add start(ref_bank_cycle_rank i)<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value ground,VM.find(ref_bank_cycle_node i)(history t)=Some value /\type_of_val value=Gtyp ground) /\
 (forall t u,(Nat.add start(ref_bank_cycle_rank i)<=t)%coq_nat ->(Nat.add start(ref_bank_cycle_rank i)<=u)%coq_nat ->(t<=limit)%coq_nat ->(u<=limit)%coq_nat ->VM.find(ref_bank_cycle_node i)(history t)=VM.find(ref_bank_cycle_node i)(history u)).
Proof.
 intros Steps CutGround CutStable i. induction i using lt_wf_ind. intro Bound.
 pose proof(ref_bank_cycle_rank_positive i Bound)as Positive.
 destruct(selected_node_safe_position flat_memories flat_statements ref_bank_cycle_offsets flat_statements ref_bank_cycle_nodes _ _ ref_bank_cycle_positions ref_bank_cycle_safety(ref_bank_cycle_member i Bound))as[count[tail[Position[Safe Nonreg]]]].
 assert(Ready:forall t,(Nat.add start(ref_bank_cycle_rank i)<=S t)%coq_nat ->(S t<=limit)%coq_nat ->reference_control_ready(history t)(ref_bank_cycle_expression i)).
 { intros t Lower Upper. apply(ref_bank_cycle_ready i(history t)Bound). intros node Member.
 destruct(ref_bank_cycle_predecessors i node Bound Member)as[Cut|[j[Prior[Inside[Node Rank]]]]].
 - apply(CutGround node t Cut);lia.
 - rewrite <-Node. apply(proj1(H j Prior Inside));lia. }
 split.
 - intros[|t]Lower Upper;[lia|].
 exact(reference_control_node_ground count tail(ref_bank_cycle_node i)(ref_bank_cycle_expression i)inputs path(history t)(history t)(history(S t))Position Safe Nonreg(Ready t Lower Upper)(Steps t ltac:(lia))).
 - intros[|t][|u]Lower Other Upper OtherUpper;try lia.
 eapply(reference_control_node_congruent count tail(ref_bank_cycle_node i)(ref_bank_cycle_expression i)inputs path(history t)(history u)(history(S t))(history(S u)));[exact Position|exact Safe|exact Nonreg|apply Ready;assumption| |apply Steps;lia|apply Steps;lia].
 apply(ref_bank_cycle_eval_equal i inputs path(history t)(history u)Bound). intros node Member.
 destruct(ref_bank_cycle_predecessors i node Bound Member)as[Cut|[j[Prior[Inside[Node Rank]]]]].
 + apply(CutStable node t u Cut);lia.
 + rewrite <-Node. apply(proj2(H j Prior Inside));lia.
Qed.
