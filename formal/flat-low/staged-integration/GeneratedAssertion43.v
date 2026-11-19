Require Import CycleJointInvariant CycleView PipelinePCAssertions CoreSocModel FormalLocalHistory.
Local Opaque generated_modules generated_top.
Theorem generated_assert_43 : forall memory_init inputs (k : nat) states, generated_observe memory_init inputs k = Some states -> generated_legal_trace memory_init inputs k -> generated_assert_m0_43_all states.
Proof.
 intros memory inputs k observed Observe Legal.
 destruct(cycle_joint_observed_invariant memory inputs k observed Observe Legal)as[v[View[PC Joint]]].
 exact(proj2(observed_pc_assertions_from_pipeline memory inputs k observed Observe Legal(cycle_pc_relation_sound _ _ View PC))).
Qed.
