Require Import FormalNextPCGroundFetchAddress FormalInstructionPortInvariant FormalInstructionPortPreparation CoreSocModel FormalLocalHistory StagedIterationCount ExternalReset FormalResetPreparation FormalTopResetHold JointUpdateBoundaryHistory JointBoundaryRegisters JointUpdateFromBoundaryHistory JointUpdateGraphPropagation JointUpdateTargets ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem observed_fetch_address_from_joint_boundary memory inputs k states :
 generated_observe memory inputs k = Some states ->
 generated_legal_trace memory inputs k ->
 (forall node width, List.In (node,width) joint_boundary_registers ->
   map_uint_concrete (N.of_nat node) width (top_environment states)) ->
 exists address, read_memory_port_field (top_environment states) (N.of_nat 9176) (N.of_nat 0) (N.of_nat 0) = Some (Gval (Fuint 16) address).
Proof.
 intros Observe Legal Boundary.
 destruct (legal_observation_reset memory inputs k Legal) as [bit External].
 unfold generated_observe, generated_observe_cycle in Observe.
 destruct (generated_run memory inputs k) as [committed|]; [|discriminate Observe].
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some committed)
 (formal_external_inputs (generated_observation_input inputs k))) as [prepared|] eqn:Prepare; [|discriminate Observe].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Observe.
 destruct (local_iteration_history (generated_observation_input inputs k) 9259 prepared states Observe)
 as [history [First [Last Steps]]].
 assert (Initial : forall node width, List.In (node,width) joint_boundary_registers ->
   map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. destruct (Boundary node width Member) as [bits [Size Lookup]].
   exists bits. split; [exact Size|].
   rewrite <- (joint_update_register_history_same _ history 9259 node width Member Steps 9259 (Nat.le_refl 9259)).
   rewrite Last. exact Lookup. }
 destruct (top_reset_prepared (Some committed) _ prepared _ External Prepare) as [env [Env Reset]].
 assert (Resets : forall i, (i <= 9259)%coq_nat ->
   VM.find (N.of_nat 1) (history i) = Some (Gval (Fuint 1) [::bit])).
 { intros i. induction i as [|i IH]; intro Bound.
   - rewrite First. unfold top_environment. rewrite Env. exact Reset.
   - eapply top_reset_iteration; [apply IH; lia|apply Steps; lia]. }
 assert (Typed : forall i, (i <= 9259)%coq_nat -> instruction_port_typed (history i)).
 { intros i. induction i as [|i IH]; intro Bound.
   - rewrite First. exact (circuit_instruction_port_prepared (Some committed) _ prepared Prepare).
   - exact (proj1 (instruction_port_iteration_typed _ (history i) false (history i) (history (S i))
       (IH ltac:(lia)) (Steps i ltac:(lia)))). }
 assert (Target : List.In 7781%nat joint_update_targets).
 { vm_compute. tauto. }
 destruct (joint_update_target_entry 7781%nat Target) as [rank [deps [Depth Member]]].
 assert (PC : joint_update_ground_at (history 9254%nat) 7781%nat).
 { eapply (joint_update_from_boundary_history (generated_observation_input inputs k) nil history 9259 Initial).
   - intros time Within. exists bit. exact (Resets time Within).
   - exact Steps.
   - vm_compute. lia.
   - exact Member.
   - apply (Nat.le_trans _ 112 _ Depth). vm_compute. lia. }
 destruct PC as [ground [pc PC]]. rewrite <- Last.
 eapply (next_pc_ground_fetch_address_after_five _ (history 9254%nat) (history 9255%nat)
 (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) ground pc PC).
 - apply Typed. exact (Nat.le_succ_diag_r 9258).
 - apply Steps. vm_compute. lia.
 - apply Steps. vm_compute. lia.
 - apply Steps. vm_compute. lia.
 - apply Steps. vm_compute. lia.
 - apply Steps. exact (Nat.le_refl 9259).
Qed.
Print Assumptions observed_fetch_address_from_joint_boundary.
