Require Import FormalDataStorageInitialization CoreSocModel FormalLoadType FormalLoadInitialization StagedObservedRegister StagedCircuitRegisterHold FormalLocalHistory FormalLoadMemoryCommit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem observed_load_type memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 exists value, VM.find 9222 (top_environment observed) = Some value /\ type_of_val value = Gtyp (Fuint 32).
Proof.
 intro Observe. pose proof Observe as Expanded.
 unfold generated_observe, generated_observe_cycle in Expanded.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run; [|discriminate Expanded].
 destruct (load9222_run_type memory inputs k committed Run) as [old [value [Old [Value Typed]]]].
 pose proof (staged_observed_register_copies memory inputs k committed old observed 9222
 (Logic.eq_refl _) (Logic.eq_refl _) load9222_initial_safe load9222_present Run Old Observe) as Hold.
 exists value. split; [|exact Typed].
 rewrite Value in Hold. unfold staged_register_lookup in Hold.
 unfold top_environment. destruct (SVM.find nil observed) as [env|]; [exact Hold|discriminate Hold].
Qed.
Theorem observed_load_commit_concrete_address memory inputs k observed committed address width :
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) = Some committed ->
 data_storage_concrete observed ->
 read_memory_port_field (top_environment observed) 9178 1 0 = Some (Gval (Fuint width) address) ->
 exists word, VM.find 9222 (top_environment committed) = Some (Gval (Fuint 32) word).
Proof.
 intros Observe Run Storage Address.
 destruct (observed_load_type memory inputs k observed Observe) as [value [Value Typed]].
 exact (observed_load_commit_concrete memory inputs k observed committed value address width Observe Run Storage Value Typed Address).
Qed.
Print Assumptions observed_load_commit_concrete_address.
