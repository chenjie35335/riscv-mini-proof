Require Import CycleView CycleViewConstruction CoreSocModel ComparisonNodes ObservedJointRegisterConcrete JointBoundaryRegisters ConcreteRegisterInitialization FormalLocalHistory RFArchitecturalRelation EarlyBubbleBitReachable LoadPipelineClassification.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition cycle_remaining_fields : list(nat*nat) :=
 [::(7331%nat,32%nat);(7816%nat,32%nat);(7819%nat,32%nat);(786%nat,32%nat);(7805%nat,5%nat)].
Definition cycle_remaining_concrete env := forall node width,
 List.In(node,width)cycle_remaining_fields ->map_uint_concrete(N.of_nat node)width env.
Lemma cycle_scalar_field_partition node width : List.In(node,width)cycle_scalar_fields ->
 List.In(node,width)joint_boundary_registers \/ List.In(node,width)cycle_remaining_fields \/
 (node=7945%nat /\ width=1%nat) \/ (node=7947%nat /\ width=1%nat).
Proof. intro Member. cbn [cycle_scalar_fields] in Member.
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 55%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 67%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 56%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 right;left. apply(List.nth_error_In cycle_remaining_fields 0%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 right;left. apply(List.nth_error_In cycle_remaining_fields 1%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 right;left. apply(List.nth_error_In cycle_remaining_fields 2%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 57%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 right;left. apply(List.nth_error_In cycle_remaining_fields 3%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 right;left. apply(List.nth_error_In cycle_remaining_fields 4%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 62%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 right;right;left;split;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 right;right;right;split;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 65%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 66%nat);vm_compute;reflexivity. }
 destruct Member as [Member|Member]. { inversion Member;subst node width.
 left. apply(List.nth_error_In joint_boundary_registers 61%nat);vm_compute;reflexivity. }
 contradiction. Qed.
Theorem cycle_observed_scalar_fields memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_remaining_concrete(top_environment observed) ->cycle_scalars_concrete(top_environment observed).
Proof.
 intros Observe Legal Remaining node width Member.
 destruct(cycle_scalar_field_partition node width Member)as[Joint|[Rest|[[Node Width]|[Node Width]]]].
 - exact(observed_joint_register_concrete memory inputs k observed node width Observe Legal Joint).
 - exact(Remaining node width Rest).
 - subst node width. destruct(early_bubble_known_observation memory inputs k observed Observe Legal)as[bit Value].
   exists[::bit];split;[reflexivity|exact Value].
 - subst node width. destruct(load_pipeline_late_observed memory inputs k observed Observe Legal)as[bit[Value Nop]].
   exists[::bit];split;[reflexivity|exact Value].
Qed.
(* Remaining premises concern representation and widths only, not architectural
   correctness. They must be discharged by the actual initialization/step proofs. *)
Theorem cycle_snapshot_observed memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_architectural_registers_concrete(top_environment observed) ->
 cycle_remaining_concrete(top_environment observed) ->
 cycle_view_at(top_environment observed)(cycle_snapshot(top_environment observed)).
Proof.
 intros Observe Legal Registers Remaining. apply cycle_snapshot_at;[exact Registers|].
 exact(cycle_observed_scalar_fields memory inputs k observed Observe Legal Remaining).
Qed.
Require Import ObservedRFPortsConcrete.
Theorem cycle_snapshot_from_reference_concrete memory inputs k observed :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 rf_architectural_registers_concrete(top_environment observed) ->
 map_uint_concrete 7331 32(top_environment observed) ->
 cycle_view_at(top_environment observed)(cycle_snapshot(top_environment observed)).
Proof.
 intros Observe Legal Registers PC.
 destruct(observed_rf_ports_concrete memory inputs k observed Observe Legal)as[Left[Right[Write Destination]]].
 apply(cycle_snapshot_observed memory inputs k observed Observe Legal Registers).
 intros node width Member. cbn [cycle_remaining_fields]in Member.
 destruct Member as[Member|[Member|[Member|[Member|[Member|Member]]]]];try contradiction;
 inversion Member;subst node width;assumption.
Qed.
