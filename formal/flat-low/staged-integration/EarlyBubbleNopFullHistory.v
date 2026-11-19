Require Import CoreSocModel ComparisonNodes EarlyBubbleNopAlignment EarlyBubbleNopControlKnown EarlyBubbleNopCommit FrontInstructionFetchType FrontPCSelectionNodes FormalInstructionResetConstants FormalStallHistory FormalCheckerResetConnections JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma early_bubble_front_instruction_member : List.In (7748%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 53%nat). vm_compute. reflexivity. Qed.
Theorem early_bubble_nop_full_history inputs path history result old_bubble :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7945 (history 9259%nat) = Some old_bubble -> type_of_val old_bubble = Gtyp (Fuint 1) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7945 result = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7748 result = Some (Gval (Fuint 32) instruction_nop).
Proof.
 intros Boundary Steps Resets OldBubble BubbleType Commit Bubble.
 destruct (early_bubble_nop_control_known inputs path history Boundary Steps) as [bit Source].
 assert (Kill : VM.find 7796 (history 9257%nat) = Some (Gval (Fuint 1) [::bit])).
 { rewrite <- (early_bubble_nop_control_alignment inputs path history Boundary Steps). exact Source. }
 destruct (front_instruction_fetch_type _ (history 9256%nat) (history 9256%nat) (history 9257%nat)
 (Steps 9256%nat ltac:(vm_compute;lia))) as [fetched [Fetched FetchedType]].
 destruct (joint_update_register_history_concrete _ history 9259 7748 32 early_bubble_front_instruction_member
 (Boundary 7748%nat 32%nat early_bubble_front_instruction_member) Steps 9257 ltac:(vm_compute;lia))
 as [held [HeldSize Held]].
 assert (Stall : VM.find 7765 (history 9257%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9251%nat) (history 9252%nat) (history 9253%nat)
 (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 pose proof (front_pc_advance_control (formal_invalid_policy inputs path)
 (history 9257%nat) (history 9257%nat) (history 9258%nat) Stall
 (Steps 9257%nat ltac:(vm_compute;lia))) as Advance.
 assert (Reset : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false); [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 exact (early_bubble_nop_same_commit (formal_invalid_policy inputs path)
 (history 9257%nat) (history 9258%nat) (history 9259%nat) result bit fetched (Gval (Fuint 32) held) old_bubble
 Kill Source Fetched FetchedType Held (Logic.eq_refl _) OldBubble BubbleType Advance Reset
 (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit Bubble).
Qed.
Print Assumptions early_bubble_nop_full_history.
