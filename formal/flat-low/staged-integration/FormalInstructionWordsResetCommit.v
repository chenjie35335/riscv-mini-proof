Require Import CoreSocModel ComparisonNodes FormalInstructionWordsCommitSource SelectedUIntMuxIdentity.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem instruction_7748_formal_reset_commit invalid old current result old_value word :
 VM.find 7748 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 8158 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7748 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (instruction_7748_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold instruction_7748_cond, instruction_7748_yes, instruction_7748_no in Source.
 pose proof (selected_uint_mux_identity flat_memories old 65 8158 7801 32 word source value
 Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem instruction_7750_formal_reset_commit invalid old current result old_value word :
 VM.find 7750 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 8160 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7750 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (instruction_7750_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold instruction_7750_cond, instruction_7750_yes, instruction_7750_no in Source.
 pose proof (selected_uint_mux_identity flat_memories old 65 8160 7878 32 word source value
 Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Print Assumptions instruction_7750_formal_reset_commit.
