Require Import StoreDataCommit StoreDataResetCommit ConcreteRegisterInitialization CoreSocModel ComparisonNodes.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_data_commit_step invalid old current result reset word :
 map_uint_concrete 7925 32 old ->
 VM.find 65 old=Some(Gval(Fuint 1)[::reset]) ->
 VM.find 79 old=Some(Gval(Fuint 32)word) ->size word=32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 VM.find 7925 result=Some(Gval(Fuint 32)(if reset then zeros 32 else word)).
Proof.
 intros[previous[SizePrevious Previous]] Reset Data Size Step.
 destruct reset.
 - exact(store_data_commit_reset invalid old current result _ word Previous (Logic.eq_refl _) Reset Data Size Step).
 - exact(store_data_commit_normal invalid old current result _ word Previous (Logic.eq_refl _) Reset Data Size Step).
Qed.
Theorem store_data_commit_concrete invalid old current result reset :
 map_uint_concrete 7925 32 old ->
 VM.find 65 old=Some(Gval(Fuint 1)[::reset]) ->map_uint_concrete 79 32 old ->
 formal_value_iter invalid flat_memories old true current flat_statements=Some result ->
 map_uint_concrete 7925 32 result.
Proof.
 intros Old Reset[word[Size Data]] Step.
 exists(if reset then zeros 32 else word). split.
 - destruct reset;[apply size_zeros|exact Size].
 - exact(store_data_commit_step invalid old current result reset word Old Reset Data Size Step).
Qed.
Print Assumptions store_data_commit_concrete.
