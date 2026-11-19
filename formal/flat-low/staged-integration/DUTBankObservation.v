Require Import RFArchitecturalNormalRelation StagedCircuitRegisterHold CoreSocModel ComparisonNodes RFReferenceNopHistory RFArchitecturalRelation StagedObservedRegister FormalFetchType FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_run generated_observe generated_modules generated_top flat_statements flat_memories.
Theorem dut_bank_run_observed memory inputs k states observed bank :
 generated_run memory inputs k=Some states ->generated_observe memory inputs k=Some observed ->
 rf_dut_bank_at(top_environment states)bank ->rf_dut_bank_at(top_environment observed)bank.
Proof.
 intros Run Observe Bank.
 destruct(fetch9220_run_type memory inputs k states Run)as[old[value[Old Rest]]].
 assert(BankOld:rf_dut_bank_at old bank).
 { unfold top_environment in Bank. rewrite Old in Bank;exact Bank. }
 intros index Bound. destruct(BankOld index Bound)as[Size Value]. split;[exact Size|].
 destruct(rf_architectural_register_properties _ (rf_dut_register_member index Bound))as[Present[Typed Safe]].
 destruct(rf_architectural_nonexternal _ (rf_dut_register_member index Bound))as[NotClock NotReset].
 pose proof(staged_observed_register_copies memory inputs k states old observed (N.of_nat(851+index)%nat) NotClock NotReset Safe Present Run Old Observe)as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy. unfold top_environment.
 destruct(SVM.find nil observed);[exact Copy|discriminate Copy].
Qed.
Require Import FormalObservationCommit StagedFlatCircuitIteration.
Theorem dut_bank_next_observed memory inputs k observed next next_observed bank :
 generated_observe memory inputs k=Some observed ->generated_run memory inputs(S k)=Some next ->
 generated_observe memory inputs(S k)=Some next_observed ->
 (forall result,formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(top_environment observed)true(top_environment observed)flat_statements=Some result ->rf_dut_bank_at result bank) ->
 rf_dut_bank_at(top_environment next_observed)bank.
Proof.
 intros Observe Next NextObserve CommitBank. pose proof Next as Commit.
 rewrite(observation_then_commit memory inputs k observed Observe)in Commit.
 destruct(flat_iteration_projection _ observed true next Commit)as[before[after[Before[Step After]]]].
 assert(Top:top_environment observed=before)by(unfold top_environment;rewrite Before;reflexivity).
 apply(dut_bank_run_observed memory inputs(S k)next next_observed bank Next NextObserve).
 unfold top_environment;rewrite After. apply CommitBank. rewrite Top;exact Step.
Qed.
