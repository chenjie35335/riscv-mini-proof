Require Import CoreSocModel ComparisonNodes DelayedRedirectNodes FetchPCSelectorStability EarlyControlStabilityHistory EarlyControlWireBitNormalization EarlyBubbleNopControlKnown FormalPipelineControlHistory ExceptionSourceNoTrap JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization FormalStallHistory FormalCheckerResetConnections.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem delayed_redirect_full_history inputs path history result bit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (history 9259%nat) = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7760 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Boundary Steps Resets NoTrap Source Commit.
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap) as NoException.
 assert (Member : List.In (7760%nat,1%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 65%nat). vm_compute;reflexivity. }
 destruct (joint_update_register_history_concrete _ history 9259 7760 1 Member (Boundary 7760%nat 1%nat Member) Steps 9257 ltac:(vm_compute;lia)) as [old [Size Old]].
 destruct (joint_update_register_history_concrete _ history 9259 7760 1 Member (Boundary 7760%nat 1%nat Member) Steps 9259 ltac:(vm_compute;lia)) as [old9 [Size9 Old9]].
 assert (Stall : VM.find 7765 (history 9255%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9249%nat) (history 9250%nat) (history 9251%nat) (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (Reset : VM.find 65 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9255%nat) (history 9255%nat) (history 9256%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9254%nat) (history 9254%nat) (history 9255%nat) false); [apply Resets|apply Steps];vm_compute;lia.
 - apply Steps;vm_compute;lia. }
 pose proof (pipeline_advance_after_two (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat) (history 9257%nat) false false Stall
 (NoException 9255 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) (Steps 9255 ltac:(vm_compute;lia)) (Steps 9256 ltac:(vm_compute;lia))) as Advance.
 pose proof (pipeline_flush_after_three (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false false false Stall
 (NoException 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) Reset
 (Steps 9255 ltac:(vm_compute;lia)) (Steps 9256 ltac:(vm_compute;lia)) (Steps 9257 ltac:(vm_compute;lia))) as Flush.
 destruct (fetch_pc_decode_same_history inputs path history 9259 Boundary Steps 9255 9255 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [word [Word Other]].
 destruct (early_control_wire_1360_normalized _ (history 9255%nat) (history 9255%nat) (history 9256%nat) (Steps 9255 ltac:(vm_compute;lia))) as [value [Value Normal]].
 destruct (early_bubble_normalized_concrete _ 1360 value Value Normal (early_control_concrete_1360_history inputs path history 9259 Boundary Steps 9256 ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as [branch Branch].
 assert (Value7859 : VM.find 7859 (history 9257%nat) = Some (Gval (Fuint 1) [::bit])).
 { rewrite (delayed_redirect_same_after_two (formal_invalid_policy inputs path) (history 9255%nat) (history 9256%nat) (history 9257%nat) word branch Word Branch (Steps 9255 ltac:(vm_compute;lia)) (Steps 9256 ltac:(vm_compute;lia))).
 rewrite (fetch_pc_selector_7773_same inputs path history 9259 Boundary Steps 9257 9259 ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia) ltac:(vm_compute;lia)). exact Source. }
 pose proof (delayed_redirect_select (formal_invalid_policy inputs path) (history 9257%nat) (history 9258%nat) (history 9259%nat) old bit Advance Value7859 Old Flush (Steps 9257 ltac:(vm_compute;lia)) (Steps 9258 ltac:(vm_compute;lia))) as Selected.
 exact (delayed_redirect_commit (formal_invalid_policy inputs path) (history 9259%nat) (history 9259%nat) result (Gval (Fuint 1) old9) bit Old9 (Logic.eq_refl _) Selected Commit).
Qed.
