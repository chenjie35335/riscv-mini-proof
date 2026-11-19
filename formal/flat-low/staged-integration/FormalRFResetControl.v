Require Import CoreSocModel StagedFlatCircuitIteration StagedIterationLemmas FormalResetTrace FormalCheckerResetConnections FormalRFResetConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Lemma rf_control_three inputs initial result bit :
 state_reset initial bit ->
 circuit_formal_iterations generated_modules generated_top inputs 3 initial = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 779 env = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros [env [Env Reset]] Steps. cbn [circuit_formal_iterations] in Steps.
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top initial false) as [s1|] eqn:A; [|discriminate Steps].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s1 false) as [s2|] eqn:B; [|discriminate Steps].
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top s2 false) as [s3|] eqn:C; [|discriminate Steps].
 inversion Steps; subst result.
 destruct (flat_iteration_projection _ initial false s1 A) as [e0 [e1 [Old0 [Step1 New1]]]].
 destruct (flat_iteration_projection _ s1 false s2 B) as [f1 [e2 [Old1 [Step2 New2]]]].
 destruct (flat_iteration_projection _ s2 false s3 C) as [f2 [e3 [Old2 [Step3 New3]]]].
 rewrite Env in Old0. inversion Old0; subst e0.
 rewrite New1 in Old1. inversion Old1; subst f1.
 rewrite New2 in Old2. inversion Old2; subst f2.
 pose proof (reset_connection_24_transfer _ env env e1 bit Reset Step1) as R24.
 pose proof (reset_connection_65_transfer _ e1 e1 e2 bit R24 Step2) as R65.
 exists e3. split; [exact New3|].
 eapply rf_reset_connection_779; [exact R65|reflexivity|exact Step3].
Qed.
Theorem rf_control_settled inputs n initial result bit :
 state_reset initial bit ->
 circuit_formal_iterations generated_modules generated_top inputs (Nat.add n 3) initial = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 779 env = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Reset Steps. rewrite formal_iterations_append in Steps.
 destruct (circuit_formal_iterations generated_modules generated_top inputs n initial) as [middle|] eqn:Prefix;
 [|discriminate Steps].
 apply (rf_control_three inputs middle result bit); [|exact Steps].
 exact (reset_circuit_iterations inputs n initial middle bit Reset Prefix).
Qed.
Corollary rf_control_9259 inputs initial result bit :
 state_reset initial bit ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some result ->
 exists env, SVM.find nil result = Some env /\ VM.find 779 env = Some (Gval (Fuint 1) [::bit]).
Proof. exact (rf_control_settled inputs 9256 initial result bit). Qed.
Print Assumptions rf_control_9259.
