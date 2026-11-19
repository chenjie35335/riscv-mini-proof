Require Import CoreSocModel FormalLocalHistory JointBoundaryInitialization JointBoundaryIncludes FetchSizedCycle FormalInstructionStorageInitialization ConcreteRegisterInitialization FormalLoadInitialization FormalDataStorageInitialization RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Opaque generated_modules generated_top.
Theorem fetch_sized_after_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top (N.of_nat 1) (Fuint 1) memory inputs = Some states ->
 map_uint_concrete (N.of_nat 9220) 32 (top_environment states).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [symbolic|] eqn:Initial; [|discriminate].
 intro Reset.
 destruct (load9222_initial_state_concrete memory inputs symbolic Initial) as [old [Old Load]].
 destruct (joint_boundary_symbolic_initial memory inputs symbolic Initial) as [Registers Storage].
 unfold joint_registers_concrete, top_environment in Registers. rewrite Old in Registers.
 eapply (fetch_sized_cycle (force_formal_reset (N.of_nat 1) (Fuint 1) inputs) symbolic old states true Old).
 - intros node width Member. apply Registers. exact Member.
 - exact (symbolic_instruction_storage_concrete memory inputs symbolic Initial).
 - unfold force_formal_reset. cbn [formal_external_inputs]. apply RegisterMapFacts.find_add_eq. reflexivity.
 - exact Reset.
Qed.
Theorem fetch_sized_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states -> map_uint_concrete (N.of_nat 9220) 32 (top_environment states).
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset; [|discriminate].
 cbn [circuit_formal_run]. intro Run. inversion Run; subst states.
 exact (fetch_sized_after_reset memory (inputs 0%nat) initial Reset).
Qed.
Print Assumptions fetch_sized_run_zero.
