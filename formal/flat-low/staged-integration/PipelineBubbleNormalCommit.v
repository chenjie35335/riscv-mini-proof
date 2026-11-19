Require Import CoreSocModel ComparisonNodes PipelineBubbleCommitSources.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_bubble_7945_normal_commit invalid old current result old_value bit :
 VM.find 7945 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7944 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7945 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Old Typed Reset Input Step.
 destruct (pipeline_bubble_7945_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 cbn [pipeline_bubble_7945_cond pipeline_bubble_7945_yes pipeline_bubble_7945_no
 eval_hfexpr_with_memory eval_href_with_memory] in Source.
 rewrite Reset in Source. cbn in Source. rewrite Input in Source.
 destruct bit; inversion Source; subst source; inversion Adapt; subst value; exact Value.
Qed.
Print Assumptions pipeline_bubble_7945_normal_commit.
Theorem pipeline_bubble_7947_normal_commit invalid old current result old_value bit :
 VM.find 7947 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7946 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7947 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Old Typed Reset Input Step.
 destruct (pipeline_bubble_7947_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 cbn [pipeline_bubble_7947_cond pipeline_bubble_7947_yes pipeline_bubble_7947_no
 eval_hfexpr_with_memory eval_href_with_memory] in Source.
 rewrite Reset in Source. cbn in Source. rewrite Input in Source.
 destruct bit; inversion Source; subst source; inversion Adapt; subst value; exact Value.
Qed.
Print Assumptions pipeline_bubble_7947_normal_commit.
