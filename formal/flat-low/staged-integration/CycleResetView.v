Require Import CycleBanksReset CycleViewClosure CycleViewConstruction CycleView
 RFArchitecturalRelation RFArchitecturalResetRelation RFArchitecturalObservedRelation RFReferenceNopCycle
 FormalObservationCommit FormalFetchType ConcreteRegisterInitialization FormalLocalHistory CoreSocModel.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_reset_architecture memory inputs k current next before :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment current)before ->rf_architectural_relation(top_environment next).
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before.
 pose proof Run as Cycle. rewrite generated_run_successor in Cycle.
 destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Cycle].
 destruct(fetch9220_run_type memory inputs k previous Previous)as[old[value[Old Rest]]].
 pose proof(cycle_architectural_concrete_from_reference memory inputs k current(cv_reference_bank before)Observe Legal(cva_reference_bank _ _ Before))as Concrete.
 pose proof(cycle_architectural_concrete_before_observation memory inputs k previous old current Previous Old Observe Concrete)as PriorConcrete.
 destruct(rf_architectural_real_reset_cycle _ previous old committed Old PriorConcrete Reset Cycle)as[env[Env Relation]].
 exact(rf_architectural_observe_preserves memory inputs(S k)committed env next Run Env Relation NextObserve).
Qed.
Theorem cycle_view_reset_next memory inputs k current next before :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment current)before ->
 map_uint_concrete 7331 32(top_environment next) ->
 cycle_view_at(top_environment next)(cycle_snapshot(top_environment next)).
Proof.
 intros Transition Reset Before PC.
 pose proof(cycle_reset_architecture memory inputs k current next before Transition Reset Before)as Relation.
 destruct(rf_architectural_relation_banks _ Relation)as[Dut Bank].
 destruct Transition as[Observe[Legal[NextObserve[NextLegal Run]]]].
 exact(cycle_view_from_reference_bank memory inputs(S k)next _ NextObserve NextLegal Bank PC).
Qed.
