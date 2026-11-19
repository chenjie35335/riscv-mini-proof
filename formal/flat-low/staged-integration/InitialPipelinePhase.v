Require Import CoreSocModel InitialPipelinePCValues FetchPCResetValue ReferencePCResetValue PipelineBubbleResetBase StartupFlagResetBase.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition initial_pipeline_phase states : Prop :=
 exists env, SVM.find nil states = Some env /\
 VM.find 7768 env = Some (Gval (Fuint 33) fetch_pc_reset_word33) /\
 VM.find 7331 env = Some (Gval (Fuint 32) reference_pc_reset_bits) /\
 VM.find 7945 env = Some (Gval (Fuint 1) [::true]) /\
 VM.find 7947 env = Some (Gval (Fuint 1) [::true]) /\
 VM.find 7762 env = Some (Gval (Fuint 1) [::true]).
Theorem initial_pipeline_phase_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states -> initial_pipeline_phase states.
Proof.
 intro Run.
 destruct (initial_pipeline_pc_values_run_zero memory inputs states Run)
 as [env [Env [Fetch Reference]]].
 destruct (pipeline_bubbles_run_zero memory inputs states Run)
 as [bubbles [Bubbles [Early Late]]].
 destruct (startup_flag_run_zero memory inputs states Run)
 as [startup [Startup Started]].
 rewrite Env in Bubbles. inversion Bubbles; subst bubbles.
 rewrite Env in Startup. inversion Startup; subst startup.
 exists env. repeat split; assumption.
Qed.
Print Assumptions initial_pipeline_phase_run_zero.
