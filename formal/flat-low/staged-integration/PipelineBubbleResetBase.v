Require Import CoreSocModel PipelineBubbleInitialization PipelineBubbleResetCommit BooleanRegisterResetCycle.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pipeline_bubbles_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\
 VM.find 7945 env = Some (Gval (Fuint 1) [::true]) /\
 VM.find 7947 env = Some (Gval (Fuint 1) [::true]).
Proof.
 intro Run.
 destruct (boolean_register_run_zero 7945 bubble7945_present (Logic.eq_refl true) (Logic.eq_refl true) bubble7945_initial_safe
 pipeline_bubble_7945_reset_commit bubble7945_initial_state_concrete memory inputs states Run)
 as [env [Env Early]].
 destruct (boolean_register_run_zero 7947 bubble7947_present (Logic.eq_refl true) (Logic.eq_refl true) bubble7947_initial_safe
 pipeline_bubble_7947_reset_commit bubble7947_initial_state_concrete memory inputs states Run)
 as [other [Other Late]].
 rewrite Env in Other. inversion Other; subst other.
 exists env. split; [exact Env|]. split; assumption.
Qed.
Print Assumptions pipeline_bubbles_run_zero.
