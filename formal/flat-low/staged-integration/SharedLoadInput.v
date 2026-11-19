Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate FormalTypedNodeEquation FormalDeclaredWireCheck RFWritebackSelection.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition shared_load_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(3347,@Eref VarOrder.T (@Eid VarOrder.T 1712));(8079,@Eref VarOrder.T (@Eid VarOrder.T 82));(8080,@Eref VarOrder.T (@Eid VarOrder.T 8079));(8201,@Eref VarOrder.T (@Eid VarOrder.T 8080))].
Definition shared_load_offsets := [::3426%nat;5158%nat;0%nat;120%nat].
Lemma shared_load_positions : select_node_offsets shared_load_offsets flat_statements = Some shared_load_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma shared_load_safety : selected_node_safety flat_memories flat_statements shared_load_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Definition shared_load_wire_position index := nth 0%nat [::1556%nat;1601%nat;1791%nat] index.
Definition shared_load_wire_distance index := nth 0%nat [::7408%nat;6619%nat;6171%nat] index.
Definition shared_load_wire_target index := nth 0 [::1477;1522;1712] index.
Definition shared_load_wire_source index := nth 0 [::8201;1477;1522] index.
Lemma shared_load_wire_certificate index : (index < 3)%coq_nat ->
 declared_wire_check flat_memories flat_statements (shared_load_wire_position index) (shared_load_wire_distance index)
 (shared_load_wire_target index) (shared_load_wire_source index) 32 = true.
Proof. intros Bound. do 3 (destruct index as [|index]; [vm_compute;reflexivity|]). lia. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
(* Shared transport proofs. *)
Theorem shared_load_wire_step index invalid old current result word :
 (index < 3)%coq_nat -> size word = 32%nat ->
 VM.find (shared_load_wire_source index) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (shared_load_wire_target index) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Size Source Step.
 eapply (declared_wire_checked_value flat_memories flat_statements (shared_load_wire_position index) (shared_load_wire_distance index)
 (shared_load_wire_target index) (shared_load_wire_source index) 32);
 [apply shared_load_wire_certificate;exact Bound|exact Source|apply rf_load_adapt32;exact Size|exact Step].
Qed.
Theorem shared_load_node_step invalid old current result node source word :
 List.In (node,@Eref VarOrder.T (@Eid VarOrder.T source)) shared_load_nodes ->
 VM.find source old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find node result = Some (Gval (Fuint 32) word).
Proof.
 intros Member Source Step.
 destruct (selected_node_safe_position flat_memories flat_statements shared_load_offsets flat_statements shared_load_nodes _ _
 shared_load_positions shared_load_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg|exact Source|reflexivity|exact Step].
Qed.
Theorem shared_load_seven_steps invalid history word :
 size word = 32%nat -> VM.find 82 (history 0%nat) = Some (Gval (Fuint 32) word) ->
 (forall i, (i < 7)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 3347 (history 7%nat) = Some (Gval (Fuint 32) word).
Proof.
 intros Size Source Steps.
 pose proof (shared_load_node_step invalid (history 0%nat) (history 0%nat) (history 1%nat) 8079 82 word ltac:(unfold shared_load_nodes; simpl;tauto) Source (Steps 0%nat ltac:(lia))) as A.
 pose proof (shared_load_node_step invalid (history 1%nat) (history 1%nat) (history 2%nat) 8080 8079 word ltac:(unfold shared_load_nodes; simpl;tauto) A (Steps 1%nat ltac:(lia))) as B.
 pose proof (shared_load_node_step invalid (history 2%nat) (history 2%nat) (history 3%nat) 8201 8080 word ltac:(unfold shared_load_nodes; simpl;tauto) B (Steps 2%nat ltac:(lia))) as C.
 pose proof (shared_load_wire_step 0%nat invalid (history 3%nat) (history 3%nat) (history 4%nat) word ltac:(lia) Size C (Steps 3%nat ltac:(lia))) as D.
 pose proof (shared_load_wire_step 1%nat invalid (history 4%nat) (history 4%nat) (history 5%nat) word ltac:(lia) Size D (Steps 4%nat ltac:(lia))) as E.
 pose proof (shared_load_wire_step 2%nat invalid (history 5%nat) (history 5%nat) (history 6%nat) word ltac:(lia) Size E (Steps 5%nat ltac:(lia))) as F.
 exact (shared_load_node_step invalid (history 6%nat) (history 6%nat) (history 7%nat) 3347 1712 word ltac:(unfold shared_load_nodes; simpl;tauto) F (Steps 6%nat ltac:(lia))).
Qed.
Theorem shared_load_same_inputs invalid history word :
 size word = 32%nat ->
 VM.find 9222 (history 0%nat) = Some (Gval (Fuint 32) word) ->
 (forall i, (i < 9)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 82 (history 9%nat) = Some (Gval (Fuint 32) word) /\
 VM.find 3347 (history 9%nat) = Some (Gval (Fuint 32) word).
Proof.
 intros Size Initial Steps.
 pose proof (rf_load_raw_history invalid history 9%nat word Size Initial Steps) as Raw.
 split.
 - exact (Raw 7%nat ltac:(lia)).
 - exact (shared_load_seven_steps invalid (fun i => history (S (S i))) word Size (Raw 0%nat ltac:(lia))
   (fun i Bound => Steps (S (S i)) ltac:(lia))).
Qed.
Require Import RegisterInvariants FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete JointBoundaryRegisters StagedRegisterHold.
Local Opaque generated_run.
Theorem shared_load_observed_inputs memory inputs k observed :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 exists word, size word = 32%nat /\
 VM.find 82 (top_environment observed) = Some (Gval (Fuint 32) word) /\
 VM.find 3347 (top_environment observed) = Some (Gval (Fuint 32) word).
Proof.
 intros Observe Legal.
 assert (Member : List.In (9222%nat,32%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 69%nat). vm_compute. reflexivity. }
 destruct (observed_joint_register_concrete memory inputs k observed 9222%nat 32%nat Observe Legal Member) as [word [Size Value]].
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Held : forall i, (i <= 9259)%coq_nat -> VM.find 9222 (history i) = VM.find 9222 (history 0%nat)).
 { induction i as [|i IH]; intro Bound; [reflexivity|].
   rewrite (staged_combinational_holds_registers (formal_invalid_policy (generated_observation_input inputs k) nil)
    flat_memories (history i) (history i) (history (S i)) flat_statements 9222 rf_load_raw_register (Steps i ltac:(lia))).
   apply IH. lia. }
 assert (Start : VM.find 9222 (history 9250%nat) = Some (Gval (Fuint 32) word)).
 { rewrite (Held 9250%nat ltac:(vm_compute;lia)) - (Held 9259%nat ltac:(vm_compute;lia)) Last. exact Value. }
 assert (WindowBound : forall i, (i < 9)%coq_nat -> (Nat.add 9250 i < 9259)%coq_nat).
 { intros i Bound. do 9 (destruct i as [|i]; [vm_compute;lia|]). lia. }
 pose proof (shared_load_same_inputs (formal_invalid_policy (generated_observation_input inputs k) nil)
 (fun i => history (Nat.add 9250 i)) word Size Start
 (fun i Bound => Steps (Nat.add 9250 i) (WindowBound i Bound))) as Both.
 exists word. split; [exact Size|]. rewrite <- Last. exact Both.
Qed.
Theorem shared_load_observed_result memory inputs k observed low middle high b0 b1 rest raw :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 size raw = 32%nat ->
 VM.find 7755 (top_environment observed) = Some (Gval (Fuint 3) [::low;middle;high]) ->
 VM.find 7752 (top_environment observed) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 9222 (top_environment observed) = Some (Gval (Fuint 32) raw) ->
 VM.find 7904 (top_environment observed) = Some (Gval (Fsint 33) (rf_load_result low middle high raw b0 b1)).
Proof.
 intros Observe Legal Size Mode Address Raw.
 destruct (observed_history memory inputs k observed Observe Legal) as [reset [history [Last [Steps Resets]]]].
 assert (Held : forall node, has_register node flat_statements = true -> forall i, (i <= 9259)%coq_nat ->
 VM.find node (history i) = VM.find node (history 0%nat)).
 { intros node Register. induction i as [|i IH]; intro Bound; [reflexivity|].
   rewrite (staged_combinational_holds_registers (formal_invalid_policy (generated_observation_input inputs k) nil)
    flat_memories (history i) (history i) (history (S i)) flat_statements node Register (Steps i ltac:(lia))).
   apply IH. lia. }
 assert (WindowRegister : forall node, has_register node flat_statements = true ->
 VM.find node (history 9247%nat) = VM.find node (top_environment observed)).
 { intros node Register. rewrite (Held node Register 9247%nat ltac:(vm_compute;lia))
   - (Held node Register 9259%nat ltac:(vm_compute;lia)) Last. reflexivity. }
 assert (WindowBound : forall i, (i < 12)%coq_nat -> (Nat.add 9247 i < 9259)%coq_nat).
 { intros i Bound. do 12 (destruct i as [|i]; [vm_compute;lia|]). lia. }
 assert (M : VM.find 7755 (history 9247%nat) = Some (Gval (Fuint 3) [::low;middle;high])).
 { rewrite (WindowRegister 7755 rf_load_mode_register). exact Mode. }
 assert (A : VM.find 7752 (history 9247%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { rewrite (WindowRegister 7752 rf_load_address_register). exact Address. }
 assert (R : VM.find 9222 (history 9247%nat) = Some (Gval (Fuint 32) raw)).
 { rewrite (WindowRegister 9222 rf_load_raw_register). exact Raw. }
 pose proof (rf_load_from_register_history (formal_invalid_policy (generated_observation_input inputs k) nil)
 (fun i => history (Nat.add 9247 i)) low middle high b0 b1 rest raw Size M A R
 (fun i Bound => Steps (Nat.add 9247 i) (WindowBound i Bound))) as Result.
 rewrite <- Last. exact Result.
Qed.
