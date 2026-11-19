Require Import CoreSocModel ComparisonNodes LateBubbleSource PipelineBubbleNormalCommit PipelineBubbleInitialization ExceptionSourceNoTrap ExceptionPCSourceRegisters JointBoundaryRegisters ConcreteRegisterInitialization FormalCheckerResetConnections.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem late_bubble_normal_history inputs path history result early old_value :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7945 (history 9259%nat) = Some (Gval (Fuint 1) [::early]) ->
 VM.find 7947 (history 9259%nat) = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7947 result = Some (Gval (Fuint 1) [::early]).
Proof.
 intros Boundary Steps Resets NoTrap Early Old Typed Commit.
 assert (E : VM.find 7945 (history 9258%nat) = Some (Gval (Fuint 1) [::early])).
 { rewrite (flat_register_history_same _ history 9259 7945 bubble7945_present Steps 9258 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same _ history 9259 7945 bubble7945_present Steps 9259 ltac:(vm_compute;lia)) in Early. exact Early. }
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9258 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as NoException.
 pose proof (late_bubble_source_value (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat)
 (history 9259%nat) early false E NoException (Steps 9258%nat ltac:(vm_compute;lia))) as Source.
 rewrite orbF in Source.
 assert (Reset : VM.find 65 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer (formal_invalid_policy inputs path) (history 9258%nat) (history 9258%nat) (history 9259%nat) false).
 - apply (reset_connection_24_transfer (formal_invalid_policy inputs path) (history 9257%nat) (history 9257%nat) (history 9258%nat) false); [apply Resets|apply Steps]; vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 exact (pipeline_bubble_7947_normal_commit (formal_invalid_policy inputs path) (history 9259%nat)
 (history 9259%nat) result old_value early Old Typed Reset Source Commit).
Qed.
Print Assumptions late_bubble_normal_history.
