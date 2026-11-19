Require Import MemoryAddressOutputs MemoryAddressSemantics MemoryRequestObservedSemantics ReferenceControlStabilityHistory ReferenceEventObserved ReferenceEventSpine FormalObservedHistory ExceptionPCSourceRegisters StoreAddressInitialization FormalAssertionDischarge CoreSocModel FormalLocalHistory ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Theorem memory_store_address_assertion_observed memory inputs k observed guards rs1 immediate address :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 size rs1=32%nat ->size immediate=32%nat ->size address=32%nat ->
 VM.find 2209(top_environment observed)=Some(Gval(Fuint 32)rs1) ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 8004(top_environment observed)=Some(Gval(Fuint 32)address) ->
 (forall node,List.In node memory_address_guards ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::guards node])) ->
 memory_address_word_6963 guards rs1 immediate=address ->
 generated_assert_m0_4_local(top_environment observed).
Proof.
 intros Observe Legal RS IS AS Rs1 Imm Address Guards Agree.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Src:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)rs1)).
 { intros t Lower Upper. rewrite(reference_control_stable_2209_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) Upper ltac:(vm_compute;lia)) Last. exact Rs1. }
 assert(Immediate:forall t,(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 2552(history t)=Some(Gval(Fuint 32)immediate)).
 { intros t Lower Upper. rewrite(reference_control_stable_2552_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps t 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) Upper ltac:(vm_compute;lia)) Last. exact Imm. }
 assert(G:forall node t,List.In node memory_address_guards ->(200<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])).
 { intros node t Member Lower Upper.
 rewrite(reference_event_guard_stable (generated_observation_input inputs k) nil history 9259 reset node Resets Steps ltac:(cbn[memory_address_guards List.In]in Member;repeat destruct Member as[<-|Member];vm_compute;tauto) t 9259 Lower ltac:(vm_compute;lia) Upper ltac:(vm_compute;lia)) Last. apply Guards;exact Member. }
 assert(A:forall t,(t<=9259)%coq_nat ->VM.find 8004(history t)=Some(Gval(Fuint 32)address)).
 { intros t Upper. rewrite(flat_register_history_same _ history 9259 8004 store_address_register_present Steps t Upper).
 rewrite <-(flat_register_history_same _ history 9259 8004 store_address_register_present Steps 9259 ltac:(vm_compute;lia)),Last. exact Address. }
 destruct(memory_address_outputs_history _ history 9259 200 guards rs1 immediate address RS IS AS Steps Src Immediate G A 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia))as[Read[Write[RefRead RefWrite]]].
 rewrite Agree in RefWrite. rewrite <-Last.
 eapply(assertion_4_from_enabled_agreement _ (history 9258)(history 9258)(history 9259)(Steps 9258 ltac:(vm_compute;lia))).
 intro Enabled. exists 32,32,address,address. repeat split;try assumption;reflexivity.
Qed.
