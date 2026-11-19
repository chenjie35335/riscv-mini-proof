Require Import CoreSocModel ComparisonNodes MemoryRequestWidth ReferenceRequestSpine MemoryRequestCorrespondence LoadTypeCorrespondence FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory ReferenceControlStabilityHistory FormalAssertionDischarge ComparisonTruth.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem memory_read_width_assertion_window memory inputs k observed kind guards :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->(kind<8)%coq_nat ->
 VM.find 7755(top_environment observed)=Some(Gval(Fuint 3)(from_N 3(N.of_nat kind))) ->
 (forall node,List.In node reference_request_guard_nodes ->VM.find node(top_environment observed)=Some(Gval(Fuint 1)[::guards node])) ->
 VM.find 1476(top_environment observed)=VM.find 1521(top_environment observed) ->
 generated_assert_m0_2_local(top_environment observed).
Proof.
 intros Observe Legal Kind Mode Guards Equal.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 7755(history t)=Some(Gval(Fuint 3)(from_N 3(N.of_nat kind)))).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7755 3 load_type_register_member Steps)as Hold.
   rewrite (Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last;exact Mode. }
 assert(Dut:forall t,(16<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1476(history t)=Some(Gval(Fuint 6)(from_N 6(memory_request_width false kind)))).
 { intros t Lower Upper. eapply(memory_width_alias_history false _ _ history 9259);[apply size_from_N|exact Steps| |exact Lower|exact Upper].
 intros u Lo Hi. exact(memory_width_decoder_history false kind _ history 9259 Kind Steps Modes u Lo Hi). }
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
 assert(Ref:forall t,(214<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 1521(history t)=Some(Gval(Fuint 6)(from_N 6(reference_request_width false guards)))).
 { intros t Lower Upper. eapply(reference_request_alias_history 1%nat _ _ history 9259 211);[lia|apply size_from_N|exact Steps| |exact Lower|exact Upper].
 intros u Lo Hi. exact(proj2(reference_request_spine_history false guards _ history 9259 200 Steps AllGuards u Lo Hi)). }
 assert(Words:from_N 6(memory_request_width false kind)=from_N 6(reference_request_width false guards)).
 { rewrite<-Last in Equal. rewrite(Dut 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))(Ref 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))in Equal. exact(f_equal (fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Equal). }
 rewrite<-Last. eapply(assertion_2_from_enabled_agreement _ (history 9258%nat)(history 9258%nat)(history 9259%nat));[apply Steps;vm_compute;lia|].
 intro Enabled. exists 6%nat,6%nat,(from_N 6(memory_request_width false kind)),(from_N 6(reference_request_width false guards)). split;[apply Dut;vm_compute;lia|]. split;[apply Ref;vm_compute;lia|rewrite Words;reflexivity].
Qed.
