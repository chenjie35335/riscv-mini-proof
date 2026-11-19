Require Import StagedRegisterHold.
Require Import StoreWidthInitialization StagedCircuitRegisterHold CoreSocModel ComparisonNodes MemoryRequestWidth ReferenceRequestSpine MemoryRequestCorrespondence LoadTypeCorrespondence FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory ReferenceControlStabilityHistory FormalAssertionDischarge ComparisonTruth.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem memory_write_width_assertion_window memory inputs k observed word guards :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->size word=6%nat ->
 VM.find 8040(top_environment observed)=Some(Gval(Fuint 6)word) ->
 (forall node,List.In node reference_request_guard_nodes ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::guards node])) ->
 word=from_N 6(reference_request_width true guards) ->
 generated_assert_m0_6_local(top_environment observed).
Proof.
 intros Observe Legal Size Mode Guards Words.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Hold:forall t,(t<=9259)%coq_nat ->VM.find 8040(history t)=VM.find 8040(history 0%nat)).
 { intros t. induction t as[|t IH];intro Bound;[reflexivity|].
   rewrite(staged_combinational_holds_registers _ flat_memories(history t)(history t)(history(S t))flat_statements 8040 store_width_register_present(Steps t ltac:(lia))).
   apply IH;lia. }
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 8040(history t)=Some(Gval(Fuint 6)word)).
 { intros t Upper. rewrite(Hold t Upper). rewrite <-(Hold 9259%nat ltac:(lia)). rewrite Last;exact Mode. }
 assert(Dut:forall t,(16<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1480(history t)=Some(Gval(Fuint 6)word)).
 { intros t Lower Upper. eapply(memory_width_alias_history true _ _ history 9259);[exact Size|exact Steps| |exact Lower|exact Upper].
 intros u Lo Hi. apply Modes;exact Hi. }
 assert(Stable:forall node i,List.In node reference_request_guard_nodes ->(200<=i)%coq_nat ->(i<=9259)%coq_nat ->VM.find node(history i)=VM.find node(history 9259%nat)).
 { intros node i Member Lower Upper. cbn [reference_request_guard_nodes List.In] in Member. repeat destruct Member as[<-|Member];try contradiction.
 - apply(reference_control_stable_1707_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1886_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1941_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1946_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1951_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1958_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1962_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1966_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_1970_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_2565_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_2649_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_2664_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_2679_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_2708_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply(reference_control_stable_2723_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps i 9259%nat);lia.
 }
 assert(AllGuards:forall node i,List.In node reference_request_guard_nodes ->(200<=i)%coq_nat ->(i<=9259)%coq_nat ->VM.find node(history i)=Some(Gval(Fuint 1)[::guards node])).
 { intros node i Member Lower Upper. rewrite(Stable node i Member Lower Upper)Last;apply Guards;exact Member. }
 assert(Ref:forall t,(214<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1525(history t)=Some(Gval(Fuint 6)(from_N 6(reference_request_width true guards)))).
 { intros t Lower Upper. eapply(reference_request_alias_history 3%nat _ _ history 9259 211);[lia|apply size_from_N|exact Steps| |exact Lower|exact Upper].
 intros u Lo Hi. exact(proj2(reference_request_spine_history true guards _ history 9259 200 Steps AllGuards u Lo Hi)). }
 rewrite<-Last. eapply(assertion_6_from_enabled_agreement _ (history 9258%nat)(history 9258%nat)(history 9259%nat));[apply Steps;vm_compute;lia|].
 intro Enabled. exists 6%nat,6%nat,word,(from_N 6(reference_request_width true guards)). split;[apply Dut;vm_compute;lia|]. split;[apply Ref;vm_compute;lia|rewrite Words;reflexivity].
Qed.
