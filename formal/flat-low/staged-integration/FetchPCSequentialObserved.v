Require Import CoreSocModel ComparisonNodes FormalLocalHistory FormalObservedHistory FormalObservationCommit StagedFlatCircuitIteration FetchPCSequentialFullHistory FetchPCSequentialExact FormalInstructionResetConstants ObservedJointRegisterConcrete JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization FormalLegalObservation LegalNoTrapWindow.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem fetch_pc_sequential_observed memory inputs k observed next pc :
 generated_observe memory inputs k = Some observed ->
 generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7776 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7771 (top_environment observed) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7768 (top_environment observed) = Some (Gval (Fuint 33) pc) ->
 VM.find 7768 (top_environment next) = Some (Gval (Fuint 33) (fetch_pc_plus_four pc)).
Proof.
 intros Observe Legal Next Reset Sel2 Sel3 Sel4 PC.
 destruct (observed_history memory inputs k observed Observe Legal)
 as [bit [history [Last [Steps Resets]]]].
 assert (FalseBit : bit = false).
 { pose proof (Resets 9259%nat ltac:(vm_compute;lia)) as R. rewrite Last Reset in R.
   destruct bit; [discriminate R|reflexivity]. }
 subst bit.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member.
   destruct (observed_joint_register_concrete memory inputs k observed node width Observe Legal Member) as [bits [Size Value]].
   exists bits. split; [exact Size|].
   rewrite <- (joint_update_register_history_same _ history 9259 node width Member Steps 9259 (Nat.le_refl 9259)).
   rewrite Last. exact Value. }
 assert (LocalAssume : generated_assume_m0_0_local (history 9259%nat)).
 { rewrite Last.
   destruct (legal_observation_assumptions memory inputs k observed Legal Observe) as [_ Assume].
   apply (proj1 (flat_assumption_at_top observed)) in Assume.
   unfold top_environment. destruct (SVM.find nil observed); [exact Assume|contradiction]. }
 assert (NoTrap : VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (legal_no_trap_history_window _ history 9259 9254 Steps); try (vm_compute;lia).
   - apply Resets. vm_compute;lia.
   - exact LocalAssume. }
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment; rewrite Before; reflexivity).
 unfold top_environment. rewrite After.
 rewrite <- Top in Step. rewrite <- Last in Step.
 apply (fetch_pc_sequential_full_history (generated_observation_input inputs k) nil history after pc Boundary Steps Resets).
 - rewrite Last. exact Sel2.
 - rewrite Last. exact Sel3.
 - rewrite Last. exact Sel4.
 - rewrite Last. exact PC.
 - exact NoTrap.
 - exact Step.
Qed.
(* Audit is separated to avoid delaying downstream proof imports. *)
