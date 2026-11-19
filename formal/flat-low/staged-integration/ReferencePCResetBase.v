Require Import CoreSocModel RegisterInvariants ReferencePCResetValue ReferencePCInitialization ReferencePCResetCycle ObservedArchitecturalRegisters StagedCircuitRegisterHold.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem reference_pc7331_after_formal_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\
 VM.find 7331 env = Some (Gval (Fuint 32) reference_pc_reset_bits).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init;
 [|discriminate]. intro Reset.
 destruct (reference_pc7331_initial_state_concrete memory inputs initial Init) as [old [Old [bits [Size Value]]]].
 apply (reference_pc_real_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states (Gval (Fuint 32) bits));
 try assumption; try reflexivity.
 unfold force_formal_reset. cbn [formal_external_inputs].
 apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Theorem reference_pc7331_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\
 VM.find 7331 env = Some (Gval (Fuint 32) reference_pc_reset_bits).
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat))
 as [initial|] eqn:Reset; [|discriminate].
 cbn [circuit_formal_run]. intro Run. inversion Run; subst states.
 exact (reference_pc7331_after_formal_reset memory (inputs 0%nat) initial Reset).
Qed.
Print Assumptions reference_pc7331_run_zero.
