Require Import RegisterInvariants RegisterPreparationFrames StagedFlatCircuitIteration StoreCycleState StoreDataReachableType StoreDataInitialization StoreMaskReachableType StoreMaskInitialization StoreAddressReachableType StoreAddressInitialization StagedObservedRegister StagedCircuitRegisterHold CoreSocModel FormalLocalHistory.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem store_state_observed memory inputs k committed observed lane left right instruction :
 generated_run memory inputs k=Some committed ->generated_observe memory inputs k=Some observed ->
 store_state_at(top_environment committed)lane left right instruction ->
 store_state_at(top_environment observed)lane left right instruction.
Proof.
 intros Run Observe State.
 destruct(store_data_run_type memory inputs k committed Run)as[env[value[Env[Value Typed]]]].
 assert(Top:top_environment committed=env)by(unfold top_environment;rewrite Env;reflexivity).
 assert(Copy:forall id,initial_register_safe id flat_statements ->has_register id flat_statements=true ->id!=0 ->id!=1 ->
 VM.find id(top_environment observed)=VM.find id env).
 { intros id Safe Present NotClock NotReset.
 pose proof(staged_observed_register_copies memory inputs k committed env observed id NotClock NotReset Safe Present Run Env Observe)as H.
 unfold staged_register_lookup in H. unfold top_environment.
 destruct(SVM.find nil observed)as[target|]eqn:Target;[exact H|].
 pose proof(staged_observed_register_copies memory inputs k committed env observed 7925 (Logic.eq_refl _) (Logic.eq_refl _) store_data_initial_safe store_data_register_present Run Env Observe)as D.
 unfold staged_register_lookup in D. rewrite Target Value in D. discriminate D. }
 destruct State as[Address Mask Data]. rewrite Top in Address,Mask,Data.
 constructor.
 - rewrite(Copy 8004 store_address_initial_safe store_address_register_present (Logic.eq_refl _) (Logic.eq_refl _)). exact Address.
 - rewrite(Copy 7924 store_mask_initial_safe store_mask_register_present (Logic.eq_refl _) (Logic.eq_refl _)). exact Mask.
 - rewrite(Copy 7925 store_data_initial_safe store_data_register_present (Logic.eq_refl _) (Logic.eq_refl _)). exact Data.
Qed.
