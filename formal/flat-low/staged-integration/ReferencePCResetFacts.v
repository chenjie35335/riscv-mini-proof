Require Import CoreSocModel ReferencePCResetValue ReferencePCResetBase FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma reference_pc_reset_unsigned : to_nat reference_pc_reset_bits = 512%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma reference_pc_reset_aligned : take 2 reference_pc_reset_bits = [::false;false].
Proof. reflexivity. Qed.
Theorem reference_pc_run_zero_aligned memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists bits, size bits = 32%nat /\ take 2 bits = [::false;false] /\
 VM.find 7331 (top_environment states) = Some (Gval (Fuint 32) bits).
Proof.
 intro Run.
 destruct (reference_pc7331_run_zero memory inputs states Run) as [env [Env Value]].
 exists reference_pc_reset_bits. split; [exact reference_pc_reset_size|].
 split; [exact reference_pc_reset_aligned|].
 unfold top_environment. rewrite Env. exact Value.
Qed.
Print Assumptions reference_pc_run_zero_aligned.
