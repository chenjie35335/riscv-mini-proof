Require Import CoreSocModel CycleJointInvariant CycleJointReachability CycleDataReachability CycleView MemoryPendingInvariant CycleLoadWidthAssertion NonloadWidthAssertion Assertion2Reset LoadPipelineClassification LoadTypeCorrespondence ExternalReset FormalLocalHistory AssertionInstances StagedFlatObservation.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem generated_assert_2 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_2_all states.
Proof.
 intros memory inputs k observed Observe Legal.
 assert(Assertion:generated_assert_m0_2_local(top_environment observed)).
 { destruct(legal_observation_reset memory inputs k Legal)as[bit Reset].
   destruct bit.
   - exact(assertion2_reset_observed memory inputs k observed Observe Reset).
   - destruct(cycle_joint_observed_invariant memory inputs k observed Observe Legal)as[v[View[PC[[Banks[Arithmetic[Memory Rest]]]Control]]]].
     destruct(load_pipeline_decode_classify(to_N(cv_commit_instruction v))49 ltac:(lia))as[Zero|[lane[Lane[Load Mode]]]].
     + exact(nonload_width_assertion memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)Zero).
     + exact(cycle_load_width_assertion memory inputs k observed v lane Observe Legal Reset View Memory Lane Load). }
 destruct(observed_last_iteration memory inputs k observed Observe)as[committed[initial[previous[old[next[Run[Prepare[Prefix[Old[Step State]]]]]]]]]].
 apply(proj2(assertion_2_at_top observed)). rewrite State.
 unfold top_environment in Assertion;rewrite State in Assertion;exact Assertion.
Qed.
