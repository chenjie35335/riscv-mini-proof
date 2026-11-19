Require Import EventAssertionsDisabled Assertion40Enable CoreSocModel FormalLocalHistory AssertionInstances StagedFlatObservation.
From mathcomp Require Import seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem generated_assert_40 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_40_all states.
Proof.
 intros memory inputs k observed Observe Legal.
 destruct(observed_last_iteration memory inputs k observed Observe)as[committed[initial[previous[old[next[Run[Prepare[Prefix[Old[Step State]]]]]]]]]].
 apply(proj2(assertion_40_at_top observed)). rewrite State.
 assert(Top:top_environment observed=next)by(unfold top_environment;rewrite State;reflexivity).
 rewrite <-Top. unfold generated_assert_m0_40_local. intro Enabled.
 exfalso. exact(event_assertion40_not_enabled memory inputs k observed Observe Legal Enabled).
Qed.
