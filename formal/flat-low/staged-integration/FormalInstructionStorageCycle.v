Require Import CoreSocModel FormalLocalHistory FormalInstructionStorageHold FormalInstructionStoragePreparation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem instruction_storage_cycle inputs previous result value :
 VM.find 9177 (top_environment previous) = Some value ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 VM.find 9177 (top_environment result) = Some value.
Proof.
 intros Value Cycle. unfold top_environment in Value.
 destruct (SVM.find nil previous) as [old|] eqn:Old; [|discriminate Value].
 unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [prepared|] eqn:Prepare; [|discriminate Cycle].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count)
 as [n|]; [|discriminate Cycle].
 destruct (circuit_formal_iterations generated_modules generated_top inputs n prepared)
 as [stable|] eqn:Iterations; [|discriminate Cycle].
 apply (circuit_instruction_storage_iteration (formal_invalid_policy inputs) stable true result value); [|exact Cycle].
 apply (circuit_instruction_storage_iterations inputs n prepared stable value); [|exact Iterations].
 rewrite (prepared_instruction_storage_copies previous old _ prepared Old Prepare). exact Value.
Qed.
Theorem instruction_storage_run inputs n initial result value :
 VM.find 9177 (top_environment initial) = Some value ->
 circuit_formal_run generated_modules generated_top initial inputs n = Some result ->
 VM.find 9177 (top_environment result) = Some value.
Proof.
 revert result. induction n as [|n IH]; intros result Value Run.
 - cbn [circuit_formal_run] in Run. inversion Run; subst result. exact Value.
 - cbn [circuit_formal_run] in Run.
   destruct (circuit_formal_run generated_modules generated_top initial inputs n)
   as [previous|] eqn:Previous; [|discriminate Run].
   apply (instruction_storage_cycle (inputs n) previous result value); [|exact Run].
   apply IH; [exact Value|reflexivity].
Qed.
Print Assumptions instruction_storage_run.
