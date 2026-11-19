Require Import CoreSocModel CycleJointInvariant CycleJointReachability CycleDataReachability CycleView MemoryPendingInvariant CycleStoreValidAssertion Assertion3Disabled StoreTypeCorrespondence ExternalReset FormalLocalHistory AssertionInstances StagedFlatObservation.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Lemma store_instruction_cases instruction :
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) \/
 exists lane,(lane<3)%coq_nat /\store_type_is_store instruction lane.
Proof.
 destruct(N.eq_dec(N.land(to_N instruction)28799)(store_type_lane_code 0%nat))as[A|A].
 { right;exists 0%nat;split;[lia|exact A]. }
 destruct(N.eq_dec(N.land(to_N instruction)28799)(store_type_lane_code 1%nat))as[B|B].
 { right;exists 1%nat;split;[lia|exact B]. }
 destruct(N.eq_dec(N.land(to_N instruction)28799)(store_type_lane_code 2%nat))as[C|C].
 { right;exists 2%nat;split;[lia|exact C]. }
 left;intros[|[|[|lane]]]Bound;try assumption;lia.
Qed.
Theorem generated_assert_3 : forall memory_init inputs (k:nat)states,
 generated_observe memory_init inputs k=Some states ->generated_legal_trace memory_init inputs k ->generated_assert_m0_3_all states.
Proof.
 intros memory inputs k observed Observe Legal.
 assert(Assertion:generated_assert_m0_3_local(top_environment observed)).
 { destruct(legal_observation_reset memory inputs k Legal)as[bit Reset]. destruct bit.
   - exact(assertion3_reset_observed memory inputs k observed Observe Reset).
   - destruct(cycle_joint_observed_invariant memory inputs k observed Observe Legal)as[v[View[PC[[Banks[Arithmetic[Memory Rest]]]Control]]]].
     destruct(store_instruction_cases(cv_commit_instruction v))as[NonStore|[lane[Lane Store]]].
     + exact(nonstore_write_valid_assertion_observed memory inputs k observed(cv_commit_instruction v)Observe Legal Reset(cva_commit_instruction _ _ View)NonStore).
     + exact(cycle_store_valid_assertion memory inputs k observed v lane Observe Legal Reset View Memory Lane Store). }
 destruct(observed_last_iteration memory inputs k observed Observe)as[committed[initial[previous[old[next[Run[Prepare[Prefix[Old[Step State]]]]]]]]]].
 apply(proj2(assertion_3_at_top observed)). rewrite State.
 unfold top_environment in Assertion;rewrite State in Assertion;exact Assertion.
Qed.
