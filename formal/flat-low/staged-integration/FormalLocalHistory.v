Require Import CoreSocModel StagedFlatCircuitIteration ComparisonNodes.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Definition formal_flat_local_step invalid before after :=
 formal_value_iter invalid ComparisonNodes.flat_memories before false before ComparisonNodes.flat_statements = Some after.
Definition top_environment states :=
 match SVM.find nil states with Some env => env | None => VM.empty hvalue end.
Lemma circuit_step_local inputs before after :
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top before false = Some after ->
 formal_flat_local_step (formal_invalid_policy inputs nil) (top_environment before) (top_environment after).
Proof.
 intro Step. destruct (flat_iteration_projection (formal_invalid_policy inputs) before false after Step)
 as [old [next [Old [Next State]]]].
 unfold top_environment. rewrite Old State. exact Next.
Qed.
Lemma circuit_iteration_history inputs n initial result :
 circuit_formal_iterations generated_modules generated_top inputs n initial = Some result ->
 exists history : nat -> SVM.t (VM.t hvalue),
 history 0%nat = initial /\ history n = result /\
 forall i, (i < n)%coq_nat ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top
   (history i) false = Some (history (S i)).
Proof.
 revert initial result. induction n as [|n IH]; intros initial result Steps.
 - cbn [circuit_formal_iterations] in Steps. inversion Steps; subst result.
   exists (fun _ => initial). repeat split. intros i Bound. lia.
 - cbn [circuit_formal_iterations] in Steps.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs)
      generated_modules generated_top initial false) as [next|] eqn:Next; [|discriminate Steps].
   destruct (IH next result Steps) as [history [First [Last Step]]].
   exists (fun i => match i with O => initial | S j => history j end).
   split; [reflexivity|]. split; [exact Last|].
   intros i Bound. destruct i as [|i]; [cbn; rewrite First; exact Next|].
   apply Step. lia.
Qed.
Theorem local_iteration_history inputs n initial result :
 circuit_formal_iterations generated_modules generated_top inputs n initial = Some result ->
 exists history : nat -> VM.t hvalue,
 history 0%nat = top_environment initial /\ history n = top_environment result /\
 forall i, (i < n)%coq_nat ->
 formal_flat_local_step (formal_invalid_policy inputs nil) (history i) (history (S i)).
Proof.
 intro Steps. destruct (circuit_iteration_history inputs n initial result Steps)
 as [history [First [Last Step]]].
 exists (fun i => top_environment (history i)).
 split; [rewrite First; reflexivity|]. split; [rewrite Last; reflexivity|].
 intros i Bound. apply circuit_step_local. apply Step. exact Bound.
Qed.
Print Assumptions local_iteration_history.
