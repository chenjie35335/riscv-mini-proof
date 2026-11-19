Require Import CoreSocModel FormalLocalHistory StagedFlatCircuitIteration StagedIterationCount FormalInstructionPortInvariant FormalInstructionPortPreparation.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem observed_instruction_port memory inputs k states :
 generated_observe memory inputs k = Some states ->
 instruction_port_typed (top_environment states) /\
 read_memory_port_field (top_environment states) 9176 0 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 unfold generated_observe, generated_observe_cycle. intro Observe.
 destruct (generated_run memory inputs k) as [previous|]; [|discriminate Observe].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare; [|discriminate Observe].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Observe.
 destruct (flat_iterations_last (generated_observation_input inputs k) 9258 prepared states Observe)
 as [before [Earlier Last]].
 apply (circuit_instruction_port_step (formal_invalid_policy (generated_observation_input inputs k)) before false states); [|exact Last].
 apply (circuit_instruction_port_iterations (generated_observation_input inputs k) 9258 prepared before); [|exact Earlier].
 exact (circuit_instruction_port_prepared (Some previous) _ prepared Prepare).
Qed.
Print Assumptions observed_instruction_port.
