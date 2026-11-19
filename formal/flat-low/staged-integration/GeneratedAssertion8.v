Require Import CoreSocModel JointBoundaryReachable JointBoundaryConsequences FormalFetchType.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem generated_assert_8 : forall memory_init inputs (k : nat) states,
 generated_observe memory_init inputs k = Some states ->
 generated_legal_trace memory_init inputs k -> generated_assert_m0_8_all states.
Proof.
 intros memory inputs k states Observe Legal.
 pose proof Observe as Expanded. unfold generated_observe, generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run; [|discriminate Expanded].
 destruct (fetch9220_run_type memory inputs k committed Run) as [old [value [Old Rest]]].
 exact (joint_boundary_x0 memory inputs k committed old states Run Old Observe Legal
   (joint_boundary_reachable memory inputs k committed Run Legal)).
Qed.
Print Assumptions generated_assert_8.
