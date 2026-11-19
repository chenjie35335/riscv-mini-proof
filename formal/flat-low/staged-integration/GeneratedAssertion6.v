Require Import CycleStoreWidthAssertion Assertion6Disabled CycleWriteDataAssertion CycleJointInvariant CycleJointReachability CycleDataReachability CoreSocModel FormalLocalHistory AssertionInstances StagedFlatObservation ExternalReset CycleView.
From Coq Require Import Lia.
From mathcomp Require Import seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem cycle_observed_store_width_assertion memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_assert_m0_6_local(top_environment observed).
Proof.
 intros Observe Legal.
 destruct(cycle_joint_observed_invariant memory inputs k observed Observe Legal)as[v[View[PC[Data Rest]]]].
 destruct Data as[Banks[Arithmetic[Memory[StorePending Data]]]].
 destruct(legal_observation_reset memory inputs k Legal)as[reset Reset]. destruct reset.
 - exact(assertion6_reset_observed memory inputs k observed Observe Reset).
 - destruct(store_instruction_cases(cv_commit_instruction v))as[[lane[Lane Store]]|NonStore].
   + exact(cycle_store_width_assertion memory inputs k observed v lane Observe Legal Reset View Memory Lane Store).
   + exact(nonstore_assertion6_observed memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)NonStore).
Qed.
Theorem generated_assert_6 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_6_all states.
Proof.
 intros memory inputs k observed Observe Legal.
 destruct(observed_last_iteration memory inputs k observed Observe)as[committed[initial[previous[old[next[Run[Prepare[Prefix[Old[Step State]]]]]]]]]].
 apply(proj2(assertion_6_at_top observed)). rewrite State.
 pose proof(cycle_observed_store_width_assertion memory inputs k observed Observe Legal)as Assertion.
 unfold top_environment in Assertion;rewrite State in Assertion;exact Assertion.
Qed.
