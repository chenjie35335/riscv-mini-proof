Require Import CoreSocModel FormalLocalHistory FormalDataPortPreparation FormalDataReadersInvariant StagedIterationCount.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem observed_data_readers memory inputs k states :
 generated_observe memory inputs k = Some states ->
 data_readers_typed (top_environment states) /\ data_readers_enabled (top_environment states).
Proof.
 unfold generated_observe, generated_observe_cycle. intro Observe.
 destruct (generated_run memory inputs k) as [committed|]; [|discriminate Observe].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare; [|discriminate Observe].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count.
 rewrite Count in Observe.
 apply (circuit_data_readers_iterations (generated_observation_input inputs k) 9258 prepared states); [|exact Observe].
 apply data_readers_initial_typed.
 exact (circuit_data_port_prepared (Some committed) _ prepared Prepare).
Qed.
Print Assumptions observed_data_readers.
