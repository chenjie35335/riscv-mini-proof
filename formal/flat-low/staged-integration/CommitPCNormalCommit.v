Require Import CoreSocModel ComparisonNodes CommitPCCommitSource FalseUIntMuxIdentity.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem commit_pc_formal_normal_commit invalid old current result old_value word :
 VM.find 7751 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7877 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7751 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (commit_pc_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold commit_pc_cond, commit_pc_yes, commit_pc_no in Source.
 pose proof (false_uint_mux_identity flat_memories old 65 8161 7877 32 word source value
 Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Print Assumptions commit_pc_formal_normal_commit.
