Require Import CoreSocModel FormalObservedAssertions FormalLocalHistory ComparisonTruth InterruptZeroNodes InterruptZeroHistory.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem generated_assert_41 : forall memory_init inputs (k : nat) states,
 generated_observe memory_init inputs k = Some states ->
 generated_legal_trace memory_init inputs k -> generated_assert_m0_41_all states.
Proof.
 intros memory inputs k states Observe Legal.
 apply (observed_assertion_41_from_agreement memory inputs k states Observe).
 intros committed initial previous old next Run Prepare Iterations Old Step Next Enabled.
 destruct (local_iteration_history (generated_observation_input inputs k) 9258 initial previous Iterations)
 as [history [First [Last Steps]]].
 destruct (interrupt_zero_history _ history 9258 Steps 9258 ltac:(vm_compute; lia) (Nat.le_refl 9258)) as [Left Right].
 rewrite Last in Left. rewrite Last in Right.
 unfold top_environment in Left, Right. rewrite Old in Left. rewrite Old in Right.
 exists 32%nat, 32%nat, interrupt_zero, interrupt_zero.
 split; [exact Left|]. split; [exact Right|reflexivity].
Qed.
Print Assumptions generated_assert_41.
