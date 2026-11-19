Require Import CoreSocModel ComparisonNodes ReferenceEventSpine ReferenceEventConditions ReferenceControlStabilityHistory FormalObservedHistory FormalLocalHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_event_guard_stable inputs path history limit reset node :
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 List.In node reference_event_guards ->
 forall left right, (200 <= left)%coq_nat -> (200 <= right)%coq_nat -> (left <= limit)%coq_nat -> (right <= limit)%coq_nat ->
 VM.find node (history left) = VM.find node (history right).
Proof.
 intros Resets Steps Member left right LL RL LU RU.
 cbn [reference_event_guards List.In] in Member.
 destruct Member as [<-|Member];[exact (reference_control_stable_1707_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1886_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1933_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1937_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1941_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1946_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1951_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1958_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1962_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1966_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1970_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1974_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1980_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1986_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1992_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_1998_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2004_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2010_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2357_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2565_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2634_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2649_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2664_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2679_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2708_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2723_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2736_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2748_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2750_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2751_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2806_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2825_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2830_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2847_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2850_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2867_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2872_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2889_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2892_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2909_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2912_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2929_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2949_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_2966_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 destruct Member as [<-|Member];[exact (reference_control_stable_3042_history inputs path history limit reset Resets Steps left right ltac:(lia) ltac:(lia) LU RU)|].
 contradiction.
Qed.
Theorem reference_event_value_observed memory inputs k observed guards :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (forall node, List.In node reference_event_guards -> VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::guards node])) ->
 VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::reference_event_value guards]).
Proof.
 intros Observe Legal Values.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Guards : forall node i, List.In node reference_event_guards -> (200 <= i)%coq_nat -> (i <= 9259)%coq_nat -> VM.find node (history i) = Some (Gval (Fuint 1) [::guards node])).
 { intros node i Member Lower Upper.
 rewrite (reference_event_guard_stable (generated_observation_input inputs k) nil history 9259 reset node Resets Steps Member i 9259%nat Lower ltac:(vm_compute;lia) Upper ltac:(lia)) Last.
 exact (Values node Member). }
 rewrite <- Last. exact (reference_event_spine_history guards _ history 9259 200 Steps Guards 9259 ltac:(vm_compute;lia) ltac:(lia)).
Qed.
Theorem reference_event_safe_observed memory inputs k observed guards :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (forall node, List.In node reference_event_guards -> VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::guards node])) ->
 reference_event_safe guards -> VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Values Safe.
 rewrite (reference_event_value_observed memory inputs k observed guards Observe Legal Values) (reference_event_safe_false guards Safe). reflexivity.
Qed.
(* Event output transport. *)
Require Import ReferenceEventNodes ReferenceEventConnections ReferenceEventNormalization.
Theorem reference_event_zero_history invalid s0 s1 s2 s3 s4 s5 enabled :
 formal_value_iter invalid ComparisonNodes.flat_memories s0 false s0 ComparisonNodes.flat_statements = Some s1 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s1 false s1 ComparisonNodes.flat_statements = Some s2 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s2 false s2 ComparisonNodes.flat_statements = Some s3 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s3 false s3 ComparisonNodes.flat_statements = Some s4 ->
 formal_value_iter invalid ComparisonNodes.flat_memories s4 false s4 ComparisonNodes.flat_statements = Some s5 ->
 VM.find 6780 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 s1 = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 1667 s5 = Some (Gval (Fuint 1) [::false]).
Proof.
 intros S1 S2 S3 S4 S5 Zero Enabled.
 assert (Value : VM.find 7083 s1 = Some (Gval (Fuint 1) [::false])).
 { rewrite (reference_event_equation_7083 invalid s0 s0 s1 S1).
 cbn [reference_event_expr_7083 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Zero;reflexivity. }
 pose proof (reference_event_7116_false invalid s0 s0 s1 S1) as No.
 assert (Selected : VM.find 7117 s2 = Some (Gval (Fuint 1) [::false])).
 { rewrite (reference_event_equation_7117 invalid s1 s1 s2 S2).
   cbn [reference_event_expr_7117 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Enabled Value No.
   unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Value No.
   destruct enabled;reflexivity. }
 assert (Alias : VM.find 7202 s3 = Some (Gval (Fuint 1) [::false])).
 { eapply reference_event_value_7202; [|reflexivity|exact S3].
   cbn [reference_event_expr_7202 eval_hfexpr_with_memory eval_href_with_memory]. exact Selected. }
 assert (Wire : VM.find 1857 s4 = Some (Gval (Fuint 1) [::false])).
 { eapply reference_event_connection_1857_value; [exact Alias|reflexivity|exact S4]. }
 eapply reference_event_connection_1667_value; [exact Wire|reflexivity|exact S5].
Qed.
Theorem reference_event_zero_observed memory inputs k observed enabled :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 VM.find 6780 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1707 (top_environment observed) = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find 1667 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Zero Enabled.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Source : VM.find 6780 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (reference_control_stable_6780_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9254 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(lia)) Last. exact Zero. }
 assert (Enable : VM.find 1707 (history 9255%nat) = Some (Gval (Fuint 1) [::enabled])).
 { rewrite (reference_control_stable_1707_history (generated_observation_input inputs k) nil history 9259 reset Resets Steps 9255 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(lia)) Last. exact Enabled. }
 rewrite <- Last.
 exact (reference_event_zero_history _ (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) enabled
 (Steps 9254%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia)) (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Source Enable).
Qed.
Theorem reference_event_output_safe memory inputs k observed guards :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 (forall node, List.In node reference_event_guards -> VM.find node (top_environment observed) = Some (Gval (Fuint 1) [::guards node])) ->
 reference_event_safe guards -> VM.find 1667 (top_environment observed) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Observe Legal Values Safe.
 eapply reference_event_zero_observed;[exact Observe|exact Legal| |].
 - exact (reference_event_safe_observed memory inputs k observed guards Observe Legal Values Safe).
 - apply (Values 1707). left;reflexivity.
Qed.
