Require Import ReferenceEventSpine ReferenceEventSpineTypes SelectedZeroMux ReferenceRedirectSpine ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_event_disabled_zero_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 6780(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Disabled.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Guard:VM.find 1707(history 9257%nat)=Some(Gval(Fuint 1)[::false])).
 { rewrite(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9257 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(lia))Last;exact Disabled. }
 assert(Mux:exists width,VM.find 6779(history 9258%nat)=Some(Gval(Fuint width)(zeros width))).
 { eapply(selected_zero_mux reference_event_offsets reference_event_nodes 6779 _ _ _ _ (history 9257%nat)(history 9258%nat)false 1);
 [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 44%nat);vm_compute;reflexivity|intros site;exact Guard|intros site;reflexivity|apply Steps;vm_compute;lia]. }
 destruct Mux as[width Mux].
 assert(Zero:VM.find 6780(history 9259%nat)=Some(Gval(Fuint width)(zeros width))).
 { eapply(reference_redirect_ground_step reference_event_offsets reference_event_nodes 6780 (@Eref VarOrder.T(@Eid VarOrder.T 6779)));
 [exact reference_event_positions|exact reference_event_safety|apply(List.nth_error_In reference_event_nodes 45%nat);vm_compute;reflexivity|intros site;exact Mux|apply Steps;vm_compute;lia]. }
 rewrite Last in Zero.
 destruct(reference_event_spine_types_observed memory inputs k observed 45%nat Observe Legal ltac:(lia))as[value[Value Typed]].
 change(VM.find 6780(top_environment observed)=Some value)in Value.
 rewrite Zero in Value;inversion Value;subst value.
 change(Gtyp(Fuint width)=Gtyp(Fuint 1))in Typed;inversion Typed;subst width;exact Zero.
Qed.
