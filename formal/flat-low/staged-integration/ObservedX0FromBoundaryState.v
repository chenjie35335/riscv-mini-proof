Require Import CoreSocModel FormalLocalHistory FormalObservedX0Reduction X0ZeroFromBoundaryHistory X0BoundaryHistory X0BoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem observed_x0_from_boundary_state memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) x0_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (top_environment states)) ->
 generated_assert_m0_8_all states.
Proof.
 intros Observe Legal Boundary.
 apply (observed_x0_from_implementation_zero memory inputs k states Observe Legal).
 intros bit history Last Steps Resets Enabled.
 apply (x0_zero_from_boundary_history (generated_observation_input inputs k) nil history 9259%nat).
 - intros node width Member.
   destruct (Boundary node width Member) as [bits [Size Lookup]].
   exists bits. split; [exact Size|].
   rewrite <- (x0_register_history_same (formal_invalid_policy (generated_observation_input inputs k) nil)
     history 9259%nat node width Member Steps 9259%nat ltac:(lia)).
   rewrite Last. exact Lookup.
 - intros time Within. exists bit. exact (Resets time Within).
 - exact Steps.
 - vm_compute. lia.
Qed.
Print Assumptions observed_x0_from_boundary_state.
