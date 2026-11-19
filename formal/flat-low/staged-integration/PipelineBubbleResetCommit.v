Require Import CoreSocModel ComparisonNodes PipelineBubbleCommitSources SelectedBitConstantMux.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_bubble_7945_reset_commit invalid old current result old_value :
 VM.find 7945 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7945 result = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Old Typed Reset Step.
 destruct (pipeline_bubble_7945_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold pipeline_bubble_7945_cond, pipeline_bubble_7945_yes, pipeline_bubble_7945_no in Source.
 pose proof (selected_bit_constant_mux_identity flat_memories old 65 7944 true source value Reset Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Print Assumptions pipeline_bubble_7945_reset_commit.
Theorem pipeline_bubble_7947_reset_commit invalid old current result old_value :
 VM.find 7947 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7947 result = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Old Typed Reset Step.
 destruct (pipeline_bubble_7947_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold pipeline_bubble_7947_cond, pipeline_bubble_7947_yes, pipeline_bubble_7947_no in Source.
 pose proof (selected_bit_constant_mux_identity flat_memories old 65 7946 true source value Reset Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Print Assumptions pipeline_bubble_7947_reset_commit.
