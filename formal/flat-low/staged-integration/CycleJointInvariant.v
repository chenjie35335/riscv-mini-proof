Require Import CycleJointBase CycleJointStep CycleJointReachability CycleDataReachability
 CycleReferenceNoException CycleView ExternalReset JointBoundaryInduction CoreSocModel FormalLocalHistory.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem cycle_joint_observed_invariant memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 exists v,cycle_view_at(top_environment observed)v /\cycle_pc_aligned v /\cycle_joint_pending(top_environment observed)v.
Proof.
 revert observed. induction k as[|k IH];intros observed Observe Legal.
 - exact(cycle_joint_initial memory inputs observed Observe Legal).
 - assert(PriorLegal:generated_legal_trace memory inputs k).
   { exact(joint_legal_trace_prefix memory inputs(S k)k Legal ltac:(lia)). }
   destruct(proj2 PriorLegal k ltac:(lia))as[Defined[current[Current Assumptions]]].
   destruct(IH current Current PriorLegal)as[before[Before[PC Joint]]].
   assert(Transition:cycle_transition memory inputs k current observed).
   { split;[exact Current|]. split;[exact PriorLegal|]. split;[exact Observe|]. split;[exact Legal|].
     pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
     destruct(generated_run memory inputs(S k))as[committed|]eqn:Run;[exists committed;reflexivity|discriminate]. }
   destruct(legal_observation_reset memory inputs k PriorLegal)as[bit Reset].
   apply(cycle_joint_step memory inputs k current observed before bit Transition Reset Before PC Joint).
Qed.
Theorem cycle_observed_write_data_assertion memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_assert_m0_5_local(top_environment observed).
Proof.
 intros Observe Legal.
 destruct(cycle_joint_observed_invariant memory inputs k observed Observe Legal)as[v[View[PC[Data Rest]]]].
 exact(proj2(proj2(proj2(proj2 Data)))).
Qed.
