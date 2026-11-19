Require Import MemoryRequestWidth ReferenceMemoryRequest ReferenceRequestSpine LoadTypeCorrespondence.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
Local Open Scope N_scope.
Definition memory_load_alignment_guard lane : VarOrder.T := nth 0 [::2565;1707;2649;2664;2679] lane.
Theorem reference_request_load_selected guards lane :
 (lane < 5)%coq_nat -> guards 1707 = true ->
 (forall row, (row < 8)%coq_nat -> guards (reference_memory_guard row) = Nat.eqb row lane) ->
 guards (memory_load_alignment_guard lane) = true ->
 reference_request_valid false guards = true /\
 reference_request_width false guards = memory_load_lane_width lane /\
 reference_request_valid true guards = false /\ reference_request_width true guards = 0.
Proof.
 intros Lane Enabled Decode Align.
 unfold reference_request_valid,reference_request_width.
 rewrite Enabled.
 pose proof (Decode 0%nat ltac:(lia)) as D0.
 pose proof (Decode 1%nat ltac:(lia)) as D1.
 pose proof (Decode 2%nat ltac:(lia)) as D2.
 pose proof (Decode 3%nat ltac:(lia)) as D3.
 pose proof (Decode 4%nat ltac:(lia)) as D4.
 pose proof (Decode 5%nat ltac:(lia)) as D5.
 pose proof (Decode 6%nat ltac:(lia)) as D6.
 pose proof (Decode 7%nat ltac:(lia)) as D7.
 cbn [reference_memory_guard reference_memory_guards nth] in D0,D1,D2,D3,D4,D5,D6,D7.
 rewrite D0 D1 D2 D3 D4 D5 D6 D7.
 do 5 (destruct lane as [|lane];[cbn [memory_load_alignment_guard nth] in Align;cbn;rewrite ?Align;repeat split;reflexivity|]);lia.
Qed.
Require Import CoreSocModel ComparisonNodes ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_request_observed memory inputs k observed guards writing :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (forall node, List.In node reference_request_guard_nodes -> VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::guards node])) ->
 VM.find (if writing then 1523 else 1519) (top_environment observed) = Some (Gval (Fuint 1) [::reference_request_valid writing guards]) /\
 VM.find (if writing then 1525 else 1521) (top_environment observed) = Some (Gval (Fuint 6) (from_N 6 (reference_request_width writing guards))).
Proof.
 intros Observe Legal Guards.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Stable : forall node i, List.In node reference_request_guard_nodes -> (200 <= i)%coq_nat -> (i <= 9259)%coq_nat -> VM.find node (history i) = VM.find node (history 9259%nat)).
 { intros node i Member Lower Upper. cbn [reference_request_guard_nodes List.In] in Member.
   repeat destruct Member as [<-|Member];try contradiction.
 - apply (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1886_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1941_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1946_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1951_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1958_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1962_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1966_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_1970_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_2565_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_2649_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_2664_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_2679_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_2708_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 - apply (reference_control_stable_2723_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps i 9259%nat);lia.
 }
 assert (AllGuards : forall node i, List.In node reference_request_guard_nodes -> (200 <= i)%coq_nat -> (i <= 9259)%coq_nat -> VM.find node (history i) = Some (Gval (Fuint 1) [::guards node])).
 { intros node i Member Lower Upper. rewrite (Stable node i Member Lower Upper) Last. apply Guards;exact Member. }
 assert (Pair : forall t, (211 <= t)%coq_nat -> (t <= 9259)%coq_nat ->
 VM.find (if writing then 7113 else 7111) (history t) = Some (Gval (Fuint 1) [::reference_request_valid writing guards]) /\
 VM.find (if writing then 7114 else 7112) (history t) = Some (Gval (Fuint 6) (from_N 6 (reference_request_width writing guards)))).
 { intros t Lower Upper. exact (reference_request_spine_history writing guards _ history 9259 200 Steps AllGuards t Lower Upper). }
 rewrite <- Last. destruct writing;split.
 - eapply (reference_request_alias_history 2%nat _ _ history 9259 211);[lia|reflexivity|exact Steps| |vm_compute;lia|vm_compute;lia].
   intros i Lower Upper. exact (proj1 (Pair i Lower Upper)).
 - eapply (reference_request_alias_history 3%nat _ _ history 9259 211);[lia|apply size_from_N|exact Steps| |vm_compute;lia|vm_compute;lia].
   intros i Lower Upper. exact (proj2 (Pair i Lower Upper)).
 - eapply (reference_request_alias_history 0%nat _ _ history 9259 211);[lia|reflexivity|exact Steps| |vm_compute;lia|vm_compute;lia].
   intros i Lower Upper. exact (proj1 (Pair i Lower Upper)).
 - eapply (reference_request_alias_history 1%nat _ _ history 9259 211);[lia|apply size_from_N|exact Steps| |vm_compute;lia|vm_compute;lia].
   intros i Lower Upper. exact (proj2 (Pair i Lower Upper)).
Qed.
Theorem memory_load_request_width_correspondence memory inputs k observed instruction lane guards :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (lane < 5)%coq_nat -> VM.find 7750 (top_environment observed) = Some (Gval (Fuint 32) instruction) ->
 load_type_is_load instruction lane ->
 (forall node, List.In node reference_request_guard_nodes -> VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::guards node])) ->
 guards 1707 = true ->
 (forall row, (row < 8)%coq_nat -> guards (reference_memory_guard row) = Nat.eqb row lane) ->
 guards (memory_load_alignment_guard lane) = true ->
 VM.find 1476 (top_environment observed) = VM.find 1521 (top_environment observed) /\
 VM.find 1519 (top_environment observed) = Some (Gval (Fuint 1) [::true]) /\
 VM.find 1523 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Lane Instruction Load Guards Enabled Decode Align.
 destruct (reference_request_load_selected guards lane Lane Enabled Decode Align) as [RV [RW [WV WW]]].
 destruct (reference_request_observed memory inputs k observed guards false Observe Legal Guards) as [ReadValid ReadWidth].
 destruct (reference_request_observed memory inputs k observed guards true Observe Legal Guards) as [WriteValid WriteWidth].
 rewrite RV in ReadValid. rewrite RW in ReadWidth. rewrite WV in WriteValid.
 split;[rewrite ReadWidth;exact (memory_load_width_observed memory inputs k observed instruction lane Observe Legal Lane Instruction Load)|].
 split;assumption.
Qed.
