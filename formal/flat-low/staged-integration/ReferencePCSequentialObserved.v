Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ReferencePCSequentialFullHistory ReferencePCSequentialValues.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
(* This is an actual combinational-history witness, not a fixed-point assumption.
   Deriving it from final observations of 6507/6780 requires their stability proofs. *)
Definition reference_pc_sequential_control_window invalid env : Prop :=
 exists history : nat -> VM.t hvalue,
 history 9259%nat = env /\
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) /\
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) /\
 VM.find 6507 (history 9250%nat) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 6780 (history 9250%nat) = Some (Gval (Fuint 1) [::false]) /\
 VM.find 6780 (history 9255%nat) = Some (Gval (Fuint 1) [::false]).
Theorem reference_pc_sequential_observed_window memory inputs k observed next pc :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 reference_pc_sequential_control_window (formal_invalid_policy (generated_observation_input inputs k) nil) (top_environment observed) ->
 size pc = 32%nat ->
 VM.find 7331 (top_environment observed) = Some (Gval (Fuint 32) pc) ->
 VM.find 1395 (top_environment observed) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7331 (top_environment next) = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros Observe Legal Next [history [Last [Steps [Resets [Redirect [Exception0 Exception5]]]]]] Size PC Valid.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 unfold top_environment. rewrite After.
 rewrite <- Top in Step. rewrite <- Last in Step.
 apply (reference_pc_sequential_full_history (formal_invalid_policy (generated_observation_input inputs k) nil) history after pc Steps Resets Size).
 - rewrite Last. exact PC.
 - rewrite Last. exact Valid.
 - exact Redirect.
 - exact Exception0.
 - exact Exception5.
 - exact Step.
Qed.
