Require Import CycleRFAssertionsInvariant CoreSocModel.
From Coq Require Import Lia.
Local Opaque generated_modules generated_top.
Theorem generated_assert_17 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_17_all states.
Proof.
 intros memory inputs k observed Observe Legal.
 exact(cycle_rf_original_assertion_reachable memory inputs k observed 9%nat Observe Legal ltac:(lia)).
Qed.
