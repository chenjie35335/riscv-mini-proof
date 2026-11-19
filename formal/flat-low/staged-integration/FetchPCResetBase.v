Require Import CoreSocModel RegisterInvariants FetchPCResetValue FormalPCRegister FetchPCResetCycle FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem fetch_pc_after_formal_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\
 VM.find 7768 env = Some (Gval (Fuint 33) fetch_pc_reset_word33).
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init;
 [|discriminate]. intro Reset.
 destruct (circuit_symbolic_pc_concrete memory inputs initial Init) as [bits [Size Value]].
 unfold top_environment in Value.
 destruct (SVM.find nil initial) as [old|] eqn:Old; [|discriminate Value].
 apply (fetch_pc_real_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states (Gval (Fuint 33) bits));
 try assumption; try reflexivity.
 unfold force_formal_reset. cbn [formal_external_inputs].
 apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Theorem fetch_pc_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\
 VM.find 7768 env = Some (Gval (Fuint 33) fetch_pc_reset_word33).
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat))
 as [initial|] eqn:Reset; [|discriminate].
 cbn [circuit_formal_run]. intro Run. inversion Run; subst states.
 exact (fetch_pc_after_formal_reset memory (inputs 0%nat) initial Reset).
Qed.
Print Assumptions fetch_pc_run_zero.
