Require Import CoreSocModel ComparisonNodes NopPCSelectHistory FormalInstructionResetConstants FetchPCSequentialExact FormalPCControlNodes FormalStallHistory FormalCheckerResetConnections FormalPCRegister ExceptionSourceNoTrap ExceptionPCSourceRegisters JointBoundaryRegisters ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma fetch_pc_nop_control_7773 invalid old current result :
 VM.find 7772 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1360 old = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7773 result = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Decode Branch Step. eapply pc_control_node_7773; [|reflexivity|exact Step].
 cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Decode Branch. reflexivity.
Qed.
Theorem fetch_pc_nop_full_history_given_branch inputs path history result pc :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7748 (history 9259%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 7768 (history 9259%nat) = Some (Gval (Fuint 33) pc) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1360 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7768 result = Some (Gval (Fuint 33) (fetch_pc_plus_four pc)).
Proof.
 intros Boundary Steps Resets Nop PC NoTrap Branch Commit.
 assert (PC0 : VM.find 7768 (history 9252%nat) = Some (Gval (Fuint 33) pc)).
 { rewrite (flat_register_history_same _ history 9259 7768 pc_register_present Steps 9252 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same _ history 9259 7768 pc_register_present Steps 9259 ltac:(vm_compute;lia)) in PC. exact PC. }
 assert (C2 : VM.find 7776 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (nop_pc_select_7776_false_history_from_final _ history 9259 Nop Steps); vm_compute;lia. }
 assert (D2 : VM.find 7772 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (nop_pc_select_7772_false_history_from_final _ history 9259 Nop Steps); vm_compute;lia. }
 pose proof (fetch_pc_nop_control_7773 _ (history 9254%nat) (history 9254%nat) (history 9255%nat) D2 Branch (Steps 9254%nat ltac:(vm_compute;lia))) as C3.
 assert (C4 : VM.find 7771 (history 9256%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (nop_pc_select_7771_false_history_from_final _ history 9259 Nop Steps); vm_compute;lia. }
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9257 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as C5.
 assert (C6 : VM.find 7765 (history 9258%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six (formal_invalid_policy inputs path) (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (Reset : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false);
 [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 apply (fetch_pc_sequential_seven_and_commit (formal_invalid_policy inputs path) (history 9252%nat) (history 9253%nat) (history 9254%nat) (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) result pc PC0 C2 C3 C4 C5 C6 Reset);
 try exact Commit; apply Steps; vm_compute;lia.
Qed.
Print Assumptions fetch_pc_nop_full_history_given_branch.
