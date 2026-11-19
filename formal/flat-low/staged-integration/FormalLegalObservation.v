Require Import CoreSocModel FlatInstances.
From Coq Require Import ZArith PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Lemma flat_assumption_at_top states :
 generated_assume_m0_0_all states <->
 match SVM.find nil states with Some env => generated_assume_m0_0_local env | None => False end.
Proof.
 unfold generated_assume_m0_0_all.
 remember (find_circuit_instances generated_modules generated_top) as im eqn:E.
 pose proof flat_instances_exact as H. rewrite <- E in H.
 destruct im as [im|]; [|discriminate H].
 rewrite H. cbn [generated_assume_instances].
 clear E H im. destruct (SVM.find nil states); simpl; intuition discriminate.
Qed.
Theorem legal_observation_assumptions memory inputs k states :
 generated_legal_trace memory inputs k ->
 generated_observe memory inputs k = Some states ->
 generated_all_assumptions states.
Proof.
 intros [_ Legal] Observe.
 destruct (Legal k (Nat.le_refl k)) as [_ [observed [Observation Assumptions]]].
 rewrite Observe in Observation. inversion Observation; subst observed. exact Assumptions.
Qed.
Theorem legal_observation_local_assumption memory inputs k states env :
 generated_legal_trace memory inputs k ->
 generated_observe memory inputs k = Some states ->
 SVM.find nil states = Some env ->
 generated_assume_m0_0_local env.
Proof.
 intros Legal Observe Top.
 destruct (legal_observation_assumptions memory inputs k states Legal Observe) as [_ Assume].
 apply (proj1 (flat_assumption_at_top states)) in Assume.
 rewrite Top in Assume. exact Assume.
Qed.
Print Assumptions legal_observation_local_assumption.
