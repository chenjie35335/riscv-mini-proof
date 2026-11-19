Require Import CoreSocModel StagedIterationCount FormalLocalHistory ExternalReset FormalResetPreparation FormalTopResetHold.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem observed_history memory inputs k states :
 generated_observe memory inputs k = Some states -> generated_legal_trace memory inputs k ->
 exists bit history,
 history 9259%nat = top_environment states /\
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step
   (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history (S i))) /\
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])).
Proof.
 intros Observe Legal.
 destruct (legal_observation_reset memory inputs k Legal) as [bit External].
 unfold generated_observe, generated_observe_cycle in Observe.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run; [|discriminate Observe].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Prepare; [|discriminate Observe].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Observe.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 initial states Observe)
 as [history [First [Last Steps]]].
 destruct (top_reset_prepared (Some committed) _ initial _ External Prepare) as [env [Env Reset]].
 assert (Start : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::bit])).
 { rewrite First. unfold top_environment. rewrite Env. exact Reset. }
 exists bit, history. split; [exact Last|]. split; [exact Steps|].
 intros i. induction i as [|i IH]; intro Bound; [exact Start|].
 eapply (top_reset_iteration (formal_invalid_policy (generated_observation_input inputs k) nil) (history i) (history i) (history (S i)) bit); [apply IH; lia|apply Steps; lia].
Qed.
Print Assumptions observed_history.
