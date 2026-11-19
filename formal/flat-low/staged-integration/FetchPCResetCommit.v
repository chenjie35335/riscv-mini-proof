Require Import CoreSocModel ComparisonNodes FetchPCCommitSource SelectedUIntMuxWiden.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem fetch_pc_formal_reset_commit invalid old current result old_value word :
 VM.find 7768 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 33) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7767 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7768 result = Some (Gval (Fuint 33) (zext_to 33 word)).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (fetch_pc_formal_commit_source invalid old current result old_value Old Typed Step)
 as [source [value [Source [Adapt Value]]]].
 unfold fetch_pc_cond, fetch_pc_yes, fetch_pc_no in Source.
 pose proof (selected_uint_mux_widen flat_memories old 65 7767 7781 32 33 word source value
 Size (Logic.eq_refl true) Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Print Assumptions fetch_pc_formal_reset_commit.
