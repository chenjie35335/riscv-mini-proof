Require Import CoreSocModel JointBoundaryInitialization JointBoundaryRunStep FormalObservationCommit FormalFetchType.
From Coq Require Import Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma joint_legal_trace_prefix memory inputs k j :
 generated_legal_trace memory inputs k -> (j <= k)%coq_nat -> generated_legal_trace memory inputs j.
Proof.
 intros [Initial Legal] Bound. split; [exact Initial|].
 intros i Within. apply Legal. lia.
Qed.
Local Opaque generated_modules generated_top.
Theorem joint_boundary_induction memory inputs :
 (forall initial, generated_run memory inputs 0 = Some initial -> joint_boundary_concrete initial) ->
 forall k states, generated_run memory inputs k = Some states ->
 generated_legal_trace memory inputs k -> joint_boundary_concrete states.
Proof.
 intros Base k. induction k as [|k IH]; intros states Run Legal.
 - exact (Base states Run).
 - pose proof Run as Expanded. rewrite generated_run_successor in Expanded.
   destruct (generated_run memory inputs k) as [committed|] eqn:Previous; [|discriminate Expanded].
   destruct (generated_successful_commit memory inputs k states Run) as [observed [Observe Commit]].
   destruct (fetch9220_run_type memory inputs k committed Previous) as [old [value [Old Rest]]].
   assert (PriorLegal : generated_legal_trace memory inputs k).
   { exact (joint_legal_trace_prefix memory inputs (S k) k Legal (Nat.le_succ_diag_r k)). }
   eapply (joint_boundary_run_step memory inputs k committed old observed states Previous Old Observe Run PriorLegal).
   apply IH; try assumption; reflexivity.
Qed.
Print Assumptions joint_boundary_induction.
