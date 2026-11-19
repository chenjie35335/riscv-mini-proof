Require Import CoreSocModel.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Opaque generated_modules generated_top.
Lemma generated_run_successor memory inputs k :
 generated_run memory inputs (S k) =
 match generated_run memory inputs k with
 | Some previous => circuit_formal_cycle generated_modules generated_top (Some previous)
 (generated_observation_input inputs k)
 | None => None end.
Proof.
 unfold generated_run, formal_run_after_reset, generated_observation_input.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs O));
 reflexivity.
Qed.
Theorem observation_then_commit memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_run memory inputs (S k) =
 formal_circuit_value_iter (formal_invalid_policy (generated_observation_input inputs k))
 generated_modules generated_top observed true.
Proof.
 intro Observe. rewrite generated_run_successor.
 unfold generated_observe in Observe.
 destruct (generated_run memory inputs k) as [previous|]; [|discriminate Observe].
 unfold generated_observe_cycle in Observe. unfold circuit_formal_cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs (generated_observation_input inputs k))) as [initial|]; [|discriminate Observe].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count) as [n|];
 [|discriminate Observe].
 rewrite Observe. reflexivity.
Qed.
Print Assumptions observation_then_commit.

Theorem generated_successful_commit memory inputs k result :
 generated_run memory inputs (S k) = Some result ->
 exists observed,
 generated_observe memory inputs k = Some observed /\
 formal_circuit_value_iter (formal_invalid_policy (generated_observation_input inputs k))
 generated_modules generated_top observed true = Some result.
Proof.
 rewrite generated_run_successor.
 unfold generated_observe.
 destruct (generated_run memory inputs k) as [previous|]; [|discriminate].
 unfold generated_observe_cycle, circuit_formal_cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs (generated_observation_input inputs k))) as [initial|]; [|discriminate].
 destruct (circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count)
 as [n|]; [|discriminate].
 destruct (circuit_formal_iterations generated_modules generated_top
 (generated_observation_input inputs k) n initial) as [observed|] eqn:Observe.
 - intro Commit. exists observed. split; [reflexivity|exact Commit].
 - discriminate.
Qed.
Print Assumptions generated_successful_commit.
