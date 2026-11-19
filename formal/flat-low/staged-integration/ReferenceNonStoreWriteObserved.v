Require Import ReferenceWriteValidFalseHistory ReferenceRequestSpine MemoryRequestObservedSemantics ReferenceMemoryRequest StoreTypeCorrespondence
 ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_nonstore_decode_observed memory inputs k observed instruction enabled :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::enabled]) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 VM.find 1951(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 1946(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 1941(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Instruction Enabled NonStore.
 pose proof(memory_reference_decode_observed memory inputs k observed instruction enabled 5%nat Observe Legal ltac:(lia)Instruction Enabled)as D2.
 assert(T2:N.eqb 35(N.land(to_N(memory_reference_instruction instruction enabled))28799)=false).
 { destruct enabled;[|reflexivity]. apply N.eqb_neq. intro Equal.
   apply(NonStore 2%nat ltac:(lia)). unfold store_type_is_store. symmetry;exact Equal. }
 change(VM.find 1951(top_environment observed)=Some(Gval(Fuint 1)[::N.eqb 35(N.land(to_N(memory_reference_instruction instruction enabled))28799)]))in D2.
 rewrite T2 in D2.
 pose proof(memory_reference_decode_observed memory inputs k observed instruction enabled 6%nat Observe Legal ltac:(lia)Instruction Enabled)as D1.
 assert(T1:N.eqb 4131(N.land(to_N(memory_reference_instruction instruction enabled))28799)=false).
 { destruct enabled;[|reflexivity]. apply N.eqb_neq. intro Equal.
   apply(NonStore 1%nat ltac:(lia)). unfold store_type_is_store. symmetry;exact Equal. }
 change(VM.find 1946(top_environment observed)=Some(Gval(Fuint 1)[::N.eqb 4131(N.land(to_N(memory_reference_instruction instruction enabled))28799)]))in D1.
 rewrite T1 in D1.
 pose proof(memory_reference_decode_observed memory inputs k observed instruction enabled 7%nat Observe Legal ltac:(lia)Instruction Enabled)as D0.
 assert(T0:N.eqb 8227(N.land(to_N(memory_reference_instruction instruction enabled))28799)=false).
 { destruct enabled;[|reflexivity]. apply N.eqb_neq. intro Equal.
   apply(NonStore 0%nat ltac:(lia)). unfold store_type_is_store. symmetry;exact Equal. }
 change(VM.find 1941(top_environment observed)=Some(Gval(Fuint 1)[::N.eqb 8227(N.land(to_N(memory_reference_instruction instruction enabled))28799)]))in D0.
 rewrite T0 in D0.
 repeat split;assumption.
Qed.
Theorem reference_write_false_history_from_last inputs path history reset enabled :
 (forall t,(t<9259)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(t<=9259)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 VM.find 1951(history 9259%nat)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1946(history 9259%nat)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1941(history 9259%nat)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 1707(history 9259%nat)=Some(Gval(Fuint 1)[::enabled]) ->
 forall t,(210<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1523(history t)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Steps Resets SB SH SW Enabled t Lower Upper.
 assert(Guards:forall u,(200<=u)%coq_nat ->(u<=9259)%coq_nat ->
 VM.find 1951(history u)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 1946(history u)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 1941(history u)=Some(Gval(Fuint 1)[::false]) /\
 exists bit,VM.find 1707(history u)=Some(Gval(Fuint 1)[::bit])).
 { intros u Low High. repeat split.
   - rewrite(reference_control_stable_1951_history inputs path history 9259 reset Resets Steps u 9259%nat ltac:(lia) ltac:(vm_compute;lia)High ltac:(vm_compute;lia)). exact SB.
   - rewrite(reference_control_stable_1946_history inputs path history 9259 reset Resets Steps u 9259%nat ltac:(lia) ltac:(vm_compute;lia)High ltac:(vm_compute;lia)). exact SH.
   - rewrite(reference_control_stable_1941_history inputs path history 9259 reset Resets Steps u 9259%nat ltac:(lia) ltac:(vm_compute;lia)High ltac:(vm_compute;lia)). exact SW.
   - exists enabled. rewrite(reference_control_stable_1707_history inputs path history 9259 reset Resets Steps u 9259%nat ltac:(lia) ltac:(vm_compute;lia)High ltac:(vm_compute;lia)). exact Enabled.
 }
 apply(reference_request_alias_history 2%nat [::false] _ history 9259 207 ltac:(lia)ltac:(reflexivity)Steps).
 - intros u Low High. exact(reference_write_false_history _ history 9259 200 Steps Guards u Low High).
 - exact Lower.
 - exact Upper.
Qed.
Theorem reference_nonstore_write_port_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (forall lane,(lane<3)%coq_nat ->~store_type_is_store instruction lane) ->
 VM.find 1523(top_environment observed)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Observe Legal Reset Instruction NonStore.
 destruct(memory_reference_enable_known memory inputs k observed Observe Legal Reset)as[enabled Enabled].
 destruct(reference_nonstore_decode_observed memory inputs k observed instruction enabled Observe Legal Instruction Enabled NonStore)as[SB[SH SW]].
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 rewrite <-Last.
 apply(reference_write_false_history_from_last (generated_observation_input inputs k)nil history reset enabled Steps Resets);
 try(rewrite Last;assumption);vm_compute;lia.
Qed.
