Require Import CoreSocModel FormalLocalHistory Assertion43Enable PipelinePCRelation CheckerValidBubbleHistory ObservedAssertion43EventContext ObservedAssertion43CommitValid ObservedAssertion43FromPCSources.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top generated_run generated_observe.
Lemma pipeline_pc_relation_bubble env :
 pipeline_pc_relation env -> exists bit, VM.find 7947 env = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros [bits [Size [Aligned [Reference Phase]]]].
 destruct Phase as [[Flag Rest]|[[Flag Rest]|[Flag Rest]]]; eexists; exact Flag.
Qed.
Theorem observed_assertion43_from_pipeline memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 pipeline_pc_relation (top_environment states) ->
 generated_assert_m0_43_all states.
Proof.
 intros Observe Legal Relation.
 apply (observed_assertion43_from_pc_sources memory inputs k states Observe Legal).
 intro Enabled.
 pose proof (observed_assertion43_commit_valid memory inputs k states Observe Legal Enabled) as Valid.
 destruct (observed_assertion43_event_context memory inputs k states Observe Legal Enabled)
 as [history [Last [Steps [Resets Rest]]]].
 destruct (pipeline_pc_relation_bubble _ Relation) as [bit Bubble].
 assert (FalseBit : bit = false).
 { apply (checker_valid_history_bubble_false (formal_invalid_policy (generated_observation_input inputs k) nil) history bit);
   try assumption; rewrite Last; assumption. }
 apply pipeline_pc_relation_commit; [exact Relation|]. rewrite <- FalseBit. exact Bubble.
Qed.
Print Assumptions observed_assertion43_from_pipeline.
