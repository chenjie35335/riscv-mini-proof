Require Import FormalFetchInitialization CoreSocModel RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StagedCircuitRegisterHold StagedObservedRegister StagedIterationCount FormalFetchInitialization FormalFetchRegisterCommit ConcreteRegisterInitialization ScalarSinkTypes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition fetch9220_typed states := exists env value,
 SVM.find nil states = Some env /\ VM.find 9220 env = Some value /\ type_of_val value = Gtyp (Fuint 32).
Theorem fetch9220_cycle_type inputs previous result :
 fetch9220_typed previous ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 fetch9220_typed result.
Proof.
 intros [old [value [Previous [Old Typed]]]] Cycle.
 unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous)
 (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Steps; [|discriminate Cycle].
 pose proof (staged_prepared_register_copies previous old _ initial 9220
 (Logic.eq_refl _) (Logic.eq_refl _) fetch9220_initial_safe fetch9220_present Previous Prepare) as Init.
 rewrite Old in Init.
 pose proof (staged_iterations_hold_register inputs 9259 initial stable 9220 fetch9220_present Steps) as Hold.
 rewrite Init in Hold.
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Cycle)
 as [before [after [Before [Commit After]]]].
 unfold staged_register_lookup in Hold. rewrite Before in Hold.
 destruct (fetch_register_formal_commit_source (formal_invalid_policy inputs nil) before before after value Hold Typed Commit)
 as [source [next [Source [Adapt Value]]]].
 exists after, next. split; [exact After|]. split; [exact Value|].
 exact (adapted_uint_result_type source 32 next Adapt).
Qed.
Theorem fetch9220_run_type memory inputs k states :
 generated_run memory inputs k = Some states -> fetch9220_typed states.
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset; [|discriminate].
 assert (Base : fetch9220_typed initial).
 { unfold formal_state_after_reset in Reset.
   destruct (circuit_symbolic_initial_state generated_modules generated_top memory (inputs 0%nat)) as [symbolic|] eqn:Symbolic; [|discriminate Reset].
   destruct (fetch9220_initial_state_concrete memory (inputs 0%nat) symbolic Symbolic) as [env [Env [bits [Width Value]]]].
   eapply fetch9220_cycle_type; [|exact Reset].
   exists env, (Gval (Fuint 32) bits). split; [exact Env|]. split; [exact Value|reflexivity]. }
 revert states. induction k as [|k IH]; intros states Run.
 - cbn [circuit_formal_run] in Run. inversion Run; subst. exact Base.
 - cbn [circuit_formal_run] in Run.
   destruct (circuit_formal_run generated_modules generated_top initial (fun n => inputs (S n)) k) as [previous|] eqn:Previous; [|discriminate Run].
   apply (fetch9220_cycle_type (inputs (S k)) previous states); [apply IH; reflexivity|exact Run].
Qed.
Print Assumptions fetch9220_run_type.
