Require Import CoreSocModel ComparisonNodes ReferencePCUpdateNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_pc_reset_bits := nseq 9 false ++ [::true] ++ nseq 22 false.
Lemma reference_pc_reset_size : size reference_pc_reset_bits = 32%nat.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_pc_reset_value invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7433 result = Some (Gval (Fuint 32) reference_pc_reset_bits).
Proof.
 intro Step. eapply reference_pc_update_7433_value; [reflexivity|exact Step].
Qed.
Print Assumptions reference_pc_reset_value.
