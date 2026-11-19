Require Import CoreSocModel StagedFlatCircuitIteration StagedIterationCount.
From mathcomp Require Import seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem observed_last_iteration memory inputs k states :
 generated_observe memory inputs k = Some states ->
 exists committed initial previous old next,
 generated_run memory inputs k = Some committed /\
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial /\
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous /\
 SVM.find nil previous = Some old /\
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil)
   flat_memories old false old flat_statements = Some next /\
 SVM.find nil states = Some next.
Proof.
 unfold generated_observe, generated_observe_cycle.
 destruct (generated_run memory inputs k) as [committed|] eqn:Run; [|discriminate].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k))) as [initial|] eqn:Initial; [|discriminate].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count.
 rewrite Count. intro Observe.
 destruct (flat_iterations_last (generated_observation_input inputs k) 9258 initial states Observe)
   as [previous [Prior Last]].
 destruct (flat_iteration_projection (formal_invalid_policy (generated_observation_input inputs k))
   previous false states Last) as [old [next [Old [Next State]]]].
 exists committed, initial, previous, old, next.
 repeat split; try reflexivity; assumption.
Qed.
Print Assumptions observed_last_iteration.
