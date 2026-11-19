Require Import CycleView CycleRFRelation CycleViewClosure RFArchitecturalRelation RFArchitecturalResetRelation RFArchitecturalObservedRelation
 FormalObservationCommit FormalFetchType StagedObservedRegister StagedCircuitRegisterHold FormalLocalHistory CoreSocModel.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_banks_agree_base memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->cycle_banks_agree v.
Proof.
 intros Observe View. exact(cycle_rf_relation_complete _ v View(rf_architectural_observe_zero memory inputs observed Observe)).
Qed.
Lemma cycle_architectural_concrete_before_observation memory inputs k previous old observed :
 generated_run memory inputs k=Some previous ->SVM.find nil previous=Some old ->
 generated_observe memory inputs k=Some observed ->rf_architectural_registers_concrete(top_environment observed) ->
 rf_architectural_registers_concrete old.
Proof.
 intros Run Old Observe Concrete node Member.
 destruct(Concrete node Member)as[word[Size Value]]. exists word;split;[exact Size|].
 destruct(rf_architectural_register_properties node Member)as[Present[Typed Safe]].
 destruct(rf_architectural_nonexternal node Member)as[Clock Reset].
 pose proof(staged_observed_register_copies memory inputs k previous old observed(N.of_nat node)Clock Reset Safe Present Run Old Observe)as Copy.
 unfold staged_register_lookup in Copy. unfold top_environment in Value.
 destruct(SVM.find nil observed)as[env|];[rewrite Value in Copy;exact(Logic.eq_sym Copy)|discriminate Value].
Qed.
Theorem cycle_banks_agree_reset memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k true ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->cycle_banks_agree after.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After.
 pose proof Run as Cycle. rewrite generated_run_successor in Cycle.
 destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Cycle].
 destruct(fetch9220_run_type memory inputs k previous Previous)as[old[value[Old Rest]]].
 pose proof(cycle_architectural_concrete_from_reference memory inputs k current(cv_reference_bank before)Observe Legal(cva_reference_bank _ _ Before))as Concrete.
 pose proof(cycle_architectural_concrete_before_observation memory inputs k previous old current Previous Old Observe Concrete)as PriorConcrete.
 destruct(rf_architectural_real_reset_cycle _ previous old committed Old PriorConcrete Reset Cycle)as[env[Env Relation]].
 apply(cycle_rf_relation_complete _ after After).
 exact(rf_architectural_observe_preserves memory inputs(S k)committed env next Run Env Relation NextObserve).
Qed.
