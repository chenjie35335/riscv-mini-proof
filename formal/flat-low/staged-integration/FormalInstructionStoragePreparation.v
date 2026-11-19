Require Import RegisterInvariants StoragePreparationFrames CoreSocModel ComparisonNodes ExternalReset StagedFlatCircuitIteration FormalLocalHistory StagedSingletonPreparation.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma instruction_storage_initial_safe : initial_storage_safe 9177 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Lemma instruction_storage_present : has_storage 9177 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma external_ports_preserve_instruction_storage initial external result :
 update_external_ports initial external top_ports = Some result ->
 VM.find 9177 result = VM.find 9177 initial.
Proof.
 intro Step.
 change (match VM.find 0 external with
 | Some clock => match VM.find 1 external with
 | Some reset => Some (VM.add 1 reset (VM.add 0 clock initial))
 | None => None end | None => None end = Some result) in Step.
 destruct (VM.find 0 external); [|discriminate Step].
 destruct (VM.find 1 external); [|discriminate Step].
 inversion Step; subst result.
 rewrite RegisterMapFacts.find_add_neq; [|discriminate].
 rewrite RegisterMapFacts.find_add_neq; [|discriminate]. reflexivity.
Qed.
Local Opaque generated_modules generated_top.
Lemma prepared_instruction_storage_copies previous old external prepared :
 SVM.find nil previous = Some old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some prepared ->
 VM.find 9177 (top_environment prepared) = VM.find 9177 old.
Proof.
 intros Old Prepare.
 destruct (singleton_prepared_property generated_modules generated_top 0 top_ports flat_statements
 previous old external prepared (fun env => VM.find 9177 env = VM.find 9177 old)
 flat_instance_map_exact flat_module_exact (Logic.eq_refl _) Old) as [result [Result Property]].
 - intros initial Init. eapply initial_storage_copies; [exact instruction_storage_initial_safe|exact instruction_storage_present|exact Init].
 - intros initial result Same Update. rewrite (external_ports_preserve_instruction_storage initial external result Update). exact Same.
 - exact Prepare.
 - unfold top_environment. rewrite Result. exact Property.
Qed.
Print Assumptions prepared_instruction_storage_copies.
