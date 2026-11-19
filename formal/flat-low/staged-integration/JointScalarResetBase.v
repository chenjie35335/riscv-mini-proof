Require Import CoreSocModel FormalLocalHistory JointBoundaryRegisters JointBoundaryInitialization JointScalarCycle FormalLoadInitialization ConcreteRegisterInitialization RegisterInvariants.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Opaque generated_modules generated_top.
Theorem joint_scalar_after_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top (N.of_nat 1) (Fuint 1) memory inputs = Some states ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 node <> 9220%nat -> node <> 9222%nat -> map_uint_concrete (N.of_nat node) width (top_environment states).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [symbolic|] eqn:Initial; [|discriminate].
 intro Reset.
 destruct (load9222_initial_state_concrete memory inputs symbolic Initial) as [old [Old Load]].
 destruct (joint_boundary_symbolic_initial memory inputs symbolic Initial) as [Registers Storage].
 unfold joint_registers_concrete, top_environment in Registers. rewrite Old in Registers.
 eapply (joint_scalar_cycle (force_formal_reset (N.of_nat 1) (Fuint 1) inputs) symbolic old states true Old Registers); [|exact Reset].
 unfold force_formal_reset. cbn [formal_external_inputs].
 apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Theorem joint_scalar_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 node <> 9220%nat -> node <> 9222%nat -> map_uint_concrete (N.of_nat node) width (top_environment states).
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset; [|discriminate].
 cbn [circuit_formal_run]. intro Run. inversion Run; subst states.
 exact (joint_scalar_after_reset memory (inputs 0%nat) initial Reset).
Qed.
Print Assumptions joint_scalar_run_zero.
