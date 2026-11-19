Require Import CoreSocModel StagedFlatCircuitIteration FormalTopResetHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition state_reset states bit := exists env,
 SVM.find nil states = Some env /\ VM.find 1 env = Some (Gval (Fuint 1) [::bit]).
Lemma reset_circuit_iteration invalid states result bit :
 state_reset states bit ->
 formal_circuit_value_iter invalid generated_modules generated_top states false = Some result ->
 state_reset result bit.
Proof.
 intros [env [Env Reset]] Step.
 destruct (flat_iteration_projection invalid states false result Step) as [old [next [Old [Next State]]]].
 rewrite Env in Old. inversion Old; subst old.
 exists next. split; [exact State|].
 eapply top_reset_iteration; [exact Reset|exact Next].
Qed.
Lemma reset_circuit_iterations inputs n states result bit :
 state_reset states bit ->
 circuit_formal_iterations generated_modules generated_top inputs n states = Some result ->
 state_reset result bit.
Proof.
 revert states result. induction n as [|n IH]; intros states result Reset Step.
 - cbn [circuit_formal_iterations] in Step. inversion Step; subst result. exact Reset.
 - cbn [circuit_formal_iterations] in Step.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs)
     generated_modules generated_top states false) as [next|] eqn:Next; [|discriminate Step].
   eapply IH; [eapply reset_circuit_iteration; [exact Reset|exact Next]|exact Step].
Qed.

Print Assumptions reset_circuit_iterations.
