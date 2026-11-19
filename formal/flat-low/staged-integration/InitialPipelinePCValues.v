Require Import CoreSocModel FetchPCResetBase FetchPCResetValue ReferencePCResetBase ReferencePCResetValue ReferencePCResetFacts.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition initial_pipeline_pc_values states : Prop :=
 exists env, SVM.find nil states = Some env /\
 VM.find 7768 env = Some (Gval (Fuint 33) fetch_pc_reset_word33) /\
 VM.find 7331 env = Some (Gval (Fuint 32) reference_pc_reset_bits).
Theorem initial_pipeline_pc_values_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states -> initial_pipeline_pc_values states.
Proof.
 intro Run.
 destruct (fetch_pc_run_zero memory inputs states Run) as [env [Env Fetch]].
 destruct (reference_pc7331_run_zero memory inputs states Run) as [other [Other Reference]].
 rewrite Env in Other. inversion Other; subst other.
 exists env. split; [exact Env|]. split; assumption.
Qed.
Lemma initial_pipeline_pc_offset :
 to_nat reference_pc_reset_bits = (to_nat fetch_pc_reset_word33 + 4)%nat.
Proof. rewrite reference_pc_reset_unsigned fetch_pc_reset_unsigned. reflexivity. Qed.
Lemma initial_pipeline_pc_alignment :
 take 2 fetch_pc_reset_word33 = [::false;false] /\
 take 2 reference_pc_reset_bits = [::false;false].
Proof. split; reflexivity. Qed.
Print Assumptions initial_pipeline_pc_values_run_zero.
