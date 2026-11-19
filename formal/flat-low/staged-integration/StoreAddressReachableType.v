Require Import ConcreteRegisterInitialization StoreAddressTypeStep StoreAddressInitialization CoreSocModel RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StagedCircuitRegisterHold StagedObservedRegister StagedIterationCount FormalSingletonSymbolic FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Lemma store_address_initial_safe : initial_register_safe 8004 flat_statements.
Proof. vm_compute;reflexivity. Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition store_address_typed states := exists env value,
 SVM.find nil states=Some env /\VM.find 8004 env=Some value /\type_of_val value=Gtyp(Fuint 32).
Theorem store_address_cycle_type inputs previous result :
 store_address_typed previous ->
 circuit_formal_cycle generated_modules generated_top(Some previous)inputs=Some result ->
 store_address_typed result.
Proof.
 intros[old[value[Previous[Old Typed]]]]Cycle.
 unfold circuit_formal_cycle in Cycle.
 destruct(circuit_initial_map_with_memory generated_modules generated_top(Some previous)
 (formal_external_inputs inputs))as[initial|]eqn:Prepare;[|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct(circuit_formal_iterations generated_modules generated_top inputs 9259 initial)as[stable|]eqn:Steps;[|discriminate Cycle].
 pose proof(staged_prepared_register_copies previous old _ initial 8004
 (Logic.eq_refl _) (Logic.eq_refl _) store_address_initial_safe store_address_register_present Previous Prepare)as Init.
 rewrite Old in Init.
 pose proof(staged_iterations_hold_register inputs 9259 initial stable 8004 store_address_register_present Steps)as Hold.
 rewrite Init in Hold.
 destruct(flat_iteration_projection (formal_invalid_policy inputs)stable true result Cycle)as[before[after[Before[Commit After]]]].
 unfold staged_register_lookup in Hold. rewrite Before in Hold.
 destruct(store_address_type_step _ before before after value Hold Typed Commit)as[next[Value TypedNext]].
 exists after,next. split;[exact After|]. split;assumption.
Qed.
Theorem store_address_initial_type memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs=Some states ->store_address_typed states.
Proof.
 intro Init.
 destruct(singleton_symbolic_property generated_modules generated_top 0 staged_top_ports flat_statements
 memory inputs states (map_uint_concrete 8004 32) flat_instance_map_exact flat_module_exact
 (store_address_symbolic_initial inputs nil) Init)as[env[Env[word[Size Value]]]].
 exists env,(Gval(Fuint 32)word). split;[exact Env|]. split;[exact Value|reflexivity].
Qed.
Theorem store_address_run_type memory inputs k states :
 generated_run memory inputs k=Some states ->store_address_typed states.
Proof.
 unfold generated_run,formal_run_after_reset.
 destruct(formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory(inputs 0%nat))as[initial|]eqn:Reset;[|discriminate].
 assert(Base:store_address_typed initial).
 { unfold formal_state_after_reset in Reset.
 destruct(circuit_symbolic_initial_state generated_modules generated_top memory(inputs 0%nat))as[symbolic|]eqn:Init;[|discriminate Reset].
 eapply store_address_cycle_type;[eapply store_address_initial_type;exact Init|exact Reset]. }
 revert states. induction k as[|k IH];intros states Run.
 - cbn[circuit_formal_run]in Run. inversion Run;subst;exact Base.
 - cbn[circuit_formal_run]in Run.
 destruct(circuit_formal_run generated_modules generated_top initial(fun n=>inputs(S n))k)as[previous|]eqn:Previous;[|discriminate Run].
 eapply store_address_cycle_type;[apply IH;reflexivity|exact Run].
Qed.
Theorem store_address_observed_type memory inputs k observed :
 generated_observe memory inputs k=Some observed ->
 exists value,VM.find 8004(top_environment observed)=Some value /\type_of_val value=Gtyp(Fuint 32).
Proof.
 intro Observe. pose proof Observe as Origin. unfold generated_observe in Origin.
 destruct(generated_run memory inputs k)as[committed|]eqn:Run;[|discriminate Origin].
 destruct(store_address_run_type memory inputs k committed Run)as[old[value[Old[Value Typed]]]].
 pose proof(staged_observed_register_copies memory inputs k committed old observed 8004
 (Logic.eq_refl _) (Logic.eq_refl _) store_address_initial_safe store_address_register_present Run Old Observe)as Copy.
 exists value. split;[|exact Typed].
 unfold staged_register_lookup in Copy. unfold top_environment.
 destruct(SVM.find nil observed)as[env|]eqn:Env.
 - rewrite Value in Copy. exact Copy.
 - rewrite Value in Copy. discriminate Copy.
Qed.
