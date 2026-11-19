Require Import CoreSocModel ComparisonNodes FormalCombStorageFrames CombStorageCertificate RegisterInvariants ScalarNodeFrames StagedFlatCircuitIteration FormalLocalHistory FormalDataStorageInitialization FormalRegisterCommitIdentity StagedRegisterHold RegisterCommitCertificate.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma data_storage_safe : comb_storage_suffix_safe flat_memories 9179 flat_statements.
Proof. apply comb_storage_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_storage_identity : register_identity_b 9179 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem data_storage_iteration invalid old current result value :
 VM.find 9179 current = Some value ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 9179 result = Some value.
Proof.
 intros Value Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old false current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 assert (Proposed : VM.find 9179 proposed = Some value).
 { exact (formal_comb_storage_suffix_preserves_value flat_statements flat_memories 9179 value invalid nil 0 old current proposed data_storage_safe Value Statements). }
 rewrite (staged_finish_false_equal flat_statements invalid nil 0 flat_memories old proposed
     (fun e => eval_hfexpr_with_memory flat_memories e old old)) in Step.
 rewrite (finish_registers_preserves_nonregister flat_statements _ old false proposed result 9179 data_storage_nonregister Step). exact Proposed.
Qed.
Local Opaque generated_modules generated_top.
Theorem circuit_data_storage_iteration invalid before after value :
 VM.find 9179 (top_environment before) = Some value ->
 formal_circuit_value_iter invalid generated_modules generated_top before false = Some after ->
 VM.find 9179 (top_environment after) = Some value.
Proof.
 intros Value Step. destruct (flat_iteration_projection invalid before false after Step)
 as [old [next [Old [LocalStep Next]]]].
 unfold top_environment in Value |- *. rewrite Old in Value. rewrite Next.
 exact (data_storage_iteration _ old old next value Value LocalStep).
Qed.
Theorem circuit_data_storage_iterations inputs n before after value :
 VM.find 9179 (top_environment before) = Some value ->
 circuit_formal_iterations generated_modules generated_top inputs n before = Some after ->
 VM.find 9179 (top_environment after) = Some value.
Proof.
 revert before after. induction n as [|n IH]; intros before after Value Steps.
 - cbn [circuit_formal_iterations] in Steps. inversion Steps; subst after. exact Value.
 - cbn [circuit_formal_iterations] in Steps.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top before false)
   as [next|] eqn:Step; [|discriminate Steps].
   apply (IH next after); [|exact Steps].
   exact (circuit_data_storage_iteration _ before next value Value Step).
Qed.
Print Assumptions circuit_data_storage_iterations.
