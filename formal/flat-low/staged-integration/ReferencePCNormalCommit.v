Require Import CoreSocModel ComparisonNodes ReferencePCCommitSource FalseUIntMuxIdentity.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_pc_formal_normal_commit invalid old current result old_value word :
 VM.find 7331 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1819 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7331 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (reference_pc_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold reference_pc_cond, reference_pc_yes, reference_pc_no in Source.
 pose proof (false_uint_mux_identity flat_memories old 1515 7433 1819 32 word source value
 Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Print Assumptions reference_pc_formal_normal_commit.
