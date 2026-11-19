Require Import ComparisonNodes.
Require Import CoreSocModel ReferencePCTargetStability ReferencePCTargetHistory ReferenceRedirectSpine ReferenceControlGroundExpressions.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma ref_pc_target_rank_bound i :(i<41)%coq_nat ->(ref_pc_target_rank i<=25)%coq_nat.
Proof. intro Bound. do 41(destruct i as[|i];[vm_compute;lia|]);lia. Qed.
Theorem reference_pc_target_equation inputs path history limit reset time i :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (225<=time)%coq_nat ->(time<limit)%coq_nat ->(i<41)%coq_nat ->
 exists site,VM.find(ref_pc_target_node i)(history time)=
 eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(ref_pc_target_expression i)(history time)(history time).
Proof.
 intros Resets Steps Lower Upper Bound.
 pose proof(ref_pc_target_cut_facts inputs path history limit reset Resets Steps)as Cuts.
 pose proof(ref_pc_target_history inputs path history limit 200 Steps
 (fun node t Member Lower Upper=>proj1(Cuts node Member)t Lower Upper)
 (fun node t u Member Lower Other Upper OtherUpper=>proj2(Cuts node Member)t u Lower Other Upper OtherUpper))as Facts.
 pose proof(ref_pc_target_rank_bound i Bound)as RankBound.
 eapply(reference_redirect_node_equation ref_pc_target_offsets ref_pc_target_nodes _ _ inputs path(history time)(history(S time)));
 [exact ref_pc_target_positions|exact ref_pc_target_safety|exact(ref_pc_target_member i Bound)| |apply Steps;exact Upper|apply(proj2(Facts i Bound));lia].
 apply(ref_pc_target_ready i(history time)Bound). intros node Member.
 destruct(ref_pc_target_predecessors i node Bound Member)as[Cut|[j[Prior[Inside[Node Rank]]]]].
 - apply(proj1(Cuts node Cut));lia.
 - rewrite <-Node. apply(proj1(Facts j Inside)).
   + pose proof(ref_pc_target_rank_bound j Inside). lia.
   + lia.
Qed.
