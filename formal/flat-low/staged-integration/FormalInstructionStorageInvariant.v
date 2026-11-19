Require Import CoreSocModel FormalLocalHistory FormalInstructionStorageInitialization FormalInstructionStorageCycle FormalInstructionStorageHold FormalInstructionStoragePreparation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem generated_run_instruction_storage_concrete contents inputs k states :
 generated_run contents inputs k = Some states -> instruction_storage_concrete states.
Proof.
 unfold generated_run, formal_run_after_reset. intro Run.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type contents (inputs O))
 as [initial|] eqn:Reset; [|discriminate Run].
 unfold formal_state_after_reset in Reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top contents (inputs O))
 as [symbolic|] eqn:Symbolic; [|discriminate Reset].
 destruct (symbolic_instruction_storage_concrete contents (inputs O) symbolic Symbolic) as [values [Value Concrete]].
 pose proof (instruction_storage_cycle _ symbolic initial _ Value Reset) as Initial.
 exists values. split; [|exact Concrete].
 exact (instruction_storage_run (fun n => inputs (S n)) k initial states _ Initial Run).
Qed.
Theorem observed_instruction_storage_concrete contents inputs k states :
 generated_observe contents inputs k = Some states -> instruction_storage_concrete states.
Proof.
 unfold generated_observe, generated_observe_cycle. intro Observe.
 destruct (generated_run contents inputs k) as [previous|] eqn:Run; [|discriminate Observe].
 destruct (generated_run_instruction_storage_concrete contents inputs k previous Run) as [values [Value Concrete]].
 unfold top_environment in Value.
 destruct (SVM.find nil previous) as [old|] eqn:Old; [|discriminate Value].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare; [|discriminate Observe].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count)
 as [n|]; [|discriminate Observe].
 exists values. split; [|exact Concrete].
 apply (circuit_instruction_storage_iterations (generated_observation_input inputs k) n prepared states _); [|exact Observe].
 rewrite (prepared_instruction_storage_copies previous old _ prepared Old Prepare). exact Value.
Qed.
Print Assumptions observed_instruction_storage_concrete.
