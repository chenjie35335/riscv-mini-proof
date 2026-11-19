Require Import ReferenceEventSelectedHistory ReferenceEventSpineTypes ReferenceEventSpine ReferenceEventConditions ReferenceEventObserved FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Lemma reference_event_selected_guard_member i :(i<45)%coq_nat ->List.In(reference_event_selected_guard i)reference_event_guards.
Proof. intro Bound. do 45(destruct i as[|i];[vm_compute;tauto|]);lia. Qed.
Theorem reference_event_selected_zero_observed memory inputs k observed g :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->reference_event_safe g ->
 (forall i,(i<45)%coq_nat ->reference_event_node_needed g(reference_event_spine_node i) ->
 VM.find(reference_event_selected_guard i)(top_environment observed)=Some(Gval(Fuint 1)[::g(reference_event_selected_guard i)])) ->
 VM.find 6780(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Safe Values.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite<-Last.
 apply(reference_event_selected_zero_history g _ history 9259 200 Steps Safe).
 - intros i t Bound Lower Upper Needed.
   rewrite(reference_event_guard_stable (generated_observation_input inputs k)nil history 9259 reset _ Resets Steps(reference_event_selected_guard_member i Bound)t 9259 Lower ltac:(vm_compute;lia)Upper ltac:(lia))Last.
   exact(Values i Bound Needed).
 - vm_compute;lia.
 - lia.
Qed.
Definition reference_event_observed_bit env node :=match VM.find node env with Some(Gval _ [::bit])=>bit|_=>false end.
Lemma reference_event_observed_bit_actual env node bit :
 VM.find node env=Some(Gval(Fuint 1)[::bit]) ->reference_event_observed_bit env node=bit.
Proof. intro Value;unfold reference_event_observed_bit;rewrite Value;reflexivity. Qed.
Lemma reference_event_observed_bit_lookup env node :
 (exists bit,VM.find node env=Some(Gval(Fuint 1)[::bit])) ->
 VM.find node env=Some(Gval(Fuint 1)[::reference_event_observed_bit env node]).
Proof. intros[bit Value];rewrite(reference_event_observed_bit_actual env node bit Value);exact Value. Qed.
