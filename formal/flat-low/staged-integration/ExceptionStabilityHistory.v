Require Import CoreSocModel ComparisonNodes ExceptionNodeCongruence ExceptionWireCongruence JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization X0ConcreteOutputCertificates X0ConcreteConnectionOutputs.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma exception_member_150 : List.In (150%nat,2%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 6). vm_compute. reflexivity. Qed.
Theorem exception_concrete_150_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 150 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 150 2 exception_member_150 Steps time Upper).
 destruct (Boundary 150%nat 2%nat exception_member_150) as [bits [Size Lookup]].
 exists 2%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_150_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 150 (history t) = VM.find 150 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 150 2 exception_member_150 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 150 2 exception_member_150 Steps u UU). reflexivity.
Qed.
Lemma exception_member_7750 : List.In (7750%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 55). vm_compute. reflexivity. Qed.
Theorem exception_concrete_7750_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7750 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7750 32 exception_member_7750 Steps time Upper).
 destruct (Boundary 7750%nat 32%nat exception_member_7750) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_7750_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7750 (history t) = VM.find 7750 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7750 32 exception_member_7750 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7750 32 exception_member_7750 Steps u UU). reflexivity.
Qed.
Lemma exception_member_7752 : List.In (7752%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 57). vm_compute. reflexivity. Qed.
Theorem exception_concrete_7752_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7752 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7752 32 exception_member_7752 Steps time Upper).
 destruct (Boundary 7752%nat 32%nat exception_member_7752) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_7752_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7752 (history t) = VM.find 7752 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7752 32 exception_member_7752 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7752 32 exception_member_7752 Steps u UU). reflexivity.
Qed.
Lemma exception_member_7754 : List.In (7754%nat,2%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 59). vm_compute. reflexivity. Qed.
Theorem exception_concrete_7754_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7754 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7754 2 exception_member_7754 Steps time Upper).
 destruct (Boundary 7754%nat 2%nat exception_member_7754) as [bits [Size Lookup]].
 exists 2%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_7754_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7754 (history t) = VM.find 7754 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7754 2 exception_member_7754 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7754 2 exception_member_7754 Steps u UU). reflexivity.
Qed.
Lemma exception_member_7755 : List.In (7755%nat,3%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 60). vm_compute. reflexivity. Qed.
Theorem exception_concrete_7755_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7755 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7755 3 exception_member_7755 Steps time Upper).
 destruct (Boundary 7755%nat 3%nat exception_member_7755) as [bits [Size Lookup]].
 exists 3%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_7755_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7755 (history t) = VM.find 7755 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7755 3 exception_member_7755 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7755 3 exception_member_7755 Steps u UU). reflexivity.
Qed.
Lemma exception_member_7758 : List.In (7758%nat,3%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 63). vm_compute. reflexivity. Qed.
Theorem exception_concrete_7758_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7758 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7758 3 exception_member_7758 Steps time Upper).
 destruct (Boundary 7758%nat 3%nat exception_member_7758) as [bits [Size Lookup]].
 exists 3%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_7758_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7758 (history t) = VM.find 7758 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7758 3 exception_member_7758 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7758 3 exception_member_7758 Steps u UU). reflexivity.
Qed.
Lemma exception_member_7759 : List.In (7759%nat,1%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 64). vm_compute. reflexivity. Qed.
Theorem exception_concrete_7759_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7759 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7759 1 exception_member_7759 Steps time Upper).
 destruct (Boundary 7759%nat 1%nat exception_member_7759) as [bits [Size Lookup]].
 exists 1%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_7759_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7759 (history t) = VM.find 7759 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7759 1 exception_member_7759 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7759 1 exception_member_7759 Steps u UU). reflexivity.
Qed.
Lemma exception_member_7760 : List.In (7760%nat,1%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 65). vm_compute. reflexivity. Qed.
Theorem exception_concrete_7760_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7760 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7760 1 exception_member_7760 Steps time Upper).
 destruct (Boundary 7760%nat 1%nat exception_member_7760) as [bits [Size Lookup]].
 exists 1%nat, bits. exact Lookup.
Qed.
Theorem exception_stable_7760_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7760 (history t) = VM.find 7760 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7760 1 exception_member_7760 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7760 1 exception_member_7760 Steps u UU). reflexivity.
Qed.
Theorem exception_concrete_118_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 118 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_118 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_7758_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_118_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 118 (history t) = VM.find 118 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_118_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_7758_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_122_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 122 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_122 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_7752_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_122_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 122 (history t) = VM.find 122 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_122_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_7752_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_123_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 123 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_123 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_7750_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_123_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 123 (history t) = VM.find 123 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_123_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_7750_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_124_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 124 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_124 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_7759_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_124_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 124 (history t) = VM.find 124 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_124_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_7759_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_125_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 125 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_125 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_7754_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_125_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 125 (history t) = VM.find 125 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_125_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_7754_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_126_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 126 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_126 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_7755_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_126_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 126 (history t) = VM.find 126 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_126_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_7755_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_127_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 127 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_127 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_7760_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_127_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 127 (history t) = VM.find 127 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_127_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_7760_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_140_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 140 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_140 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_123_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_140_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 140 (history t) = VM.find 140 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_140_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_123_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_123_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_141_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 141 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_141 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_123_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_141_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 141 (history t) = VM.find 141 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_141_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_123_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_123_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_284_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 284 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_284 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_284_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 284 (history t) = VM.find 284 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_284_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_118_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_393_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 393 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_393 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_393_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 393 (history t) = VM.find 393 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_393_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_118_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_394_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 394 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_394 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_394_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 394 (history t) = VM.find 394 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_394_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_118_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_407_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 407 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_407 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_407_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 407 (history t) = VM.find 407 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_407_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_122_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_409_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 409 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_409 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_409_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 409 (history t) = VM.find 409 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_409_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_122_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_411_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 411 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_411 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_411_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 411 (history t) = VM.find 411 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_411_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_122_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_412_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 412 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_412 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_412_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 412 (history t) = VM.find 412 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_412_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_122_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_413_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 413 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_413 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_126_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_413_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 413 (history t) = VM.find 413 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_413_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_126_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_126_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_415_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 415 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_415 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_126_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_415_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 415 (history t) = VM.find 415 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_415_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_126_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_126_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_417_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 417 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_417 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_126_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_417_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 417 (history t) = VM.find 417 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_417_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_126_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_126_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_419_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 419 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_419 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_419_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 419 (history t) = VM.find 419 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_419_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_122_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_421_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 421 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_421 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_421_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 421 (history t) = VM.find 421 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_421_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_122_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_122_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_422_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 422 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_422 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_125_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_422_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 422 (history t) = VM.find 422 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_422_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_125_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_125_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_424_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 424 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_424 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_125_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_424_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 424 (history t) = VM.find 424 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_424_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_125_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_125_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_429_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 429 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_429 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_429_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 429 (history t) = VM.find 429 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_429_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_118_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_118_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_282_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 282 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_282 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_282_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 282 (history t) = VM.find 282 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_282_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_285_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 285 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_285 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_285_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 285 (history t) = VM.find 285 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_285_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_288_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 288 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_288 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_288_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 288 (history t) = VM.find 288 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_288_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_291_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 291 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_291 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_291_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 291 (history t) = VM.find 291 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_291_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_293_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 293 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_293 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_293_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 293 (history t) = VM.find 293 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_293_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_301_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 301 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_301 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_301_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 301 (history t) = VM.find 301 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_301_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_303_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 303 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_303 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_303_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 303 (history t) = VM.find 303 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_303_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_305_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 305 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_305 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_305_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 305 (history t) = VM.find 305 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_305_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_307_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 307 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_307 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_307_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 307 (history t) = VM.find 307 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_307_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_309_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 309 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_309 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_309_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 309 (history t) = VM.find 309 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_309_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_311_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 311 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_311 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_311_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 311 (history t) = VM.find 311 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_311_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_313_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 313 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_313 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_313_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 313 (history t) = VM.find 313 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_313_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_315_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 315 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_315 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_315_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 315 (history t) = VM.find 315 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_315_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_317_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 317 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_317 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_317_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 317 (history t) = VM.find 317 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_317_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_319_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 319 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_319 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_319_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 319 (history t) = VM.find 319 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_319_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_321_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 321 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_321 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_321_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 321 (history t) = VM.find 321 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_321_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_323_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 323 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_323 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_323_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 323 (history t) = VM.find 323 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_323_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_325_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 325 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_325 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_325_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 325 (history t) = VM.find 325 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_325_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_327_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 327 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_327 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_327_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 327 (history t) = VM.find 327 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_327_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_329_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 329 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_329 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_329_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 329 (history t) = VM.find 329 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_329_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_331_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 331 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_331 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_331_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 331 (history t) = VM.find 331 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_331_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_333_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 333 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_333 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_333_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 333 (history t) = VM.find 333 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_333_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_335_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 335 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_335 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_335_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 335 (history t) = VM.find 335 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_335_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_337_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 337 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_337 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_337_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 337 (history t) = VM.find 337 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_337_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_339_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 339 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_339 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_339_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 339 (history t) = VM.find 339 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_339_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_341_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 341 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_341 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_341_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 341 (history t) = VM.find 341 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_341_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_343_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 343 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_343 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_343_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 343 (history t) = VM.find 343 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_343_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_345_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 345 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_345 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_345_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 345 (history t) = VM.find 345 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_345_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_347_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 347 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_347 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_347_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 347 (history t) = VM.find 347 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_347_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_349_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 349 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_349 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_349_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 349 (history t) = VM.find 349 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_349_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_351_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 351 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_351 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_351_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 351 (history t) = VM.find 351 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_351_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_353_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 353 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_353 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_353_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 353 (history t) = VM.find 353 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_353_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_355_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 355 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_355 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_355_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 355 (history t) = VM.find 355 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_355_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_357_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 357 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_357 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_357_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 357 (history t) = VM.find 357 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_357_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_387_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 387 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_387 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_387_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 387 (history t) = VM.find 387 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_387_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_389_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 389 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_389 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_389_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 389 (history t) = VM.find 389 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_389_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_391_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 391 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_391 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_391_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 391 (history t) = VM.find 391 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_391_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_140_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_140_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_395_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 395 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_395 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_141_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_395_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 395 (history t) = VM.find 395 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_395_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_141_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_141_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_408_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 408 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_408 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_127_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_407_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_408_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 408 (history t) = VM.find 408 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_408_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_127_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_407_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_127_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_407_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_410_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 410 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_410 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_409_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_410_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 410 (history t) = VM.find 410 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_410_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_409_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_409_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_420_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 420 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_420 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_419_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_420_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 420 (history t) = VM.find 420 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_420_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_419_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_419_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_430_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 430 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_430 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_429_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_430_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 430 (history t) = VM.find 430 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_430_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_429_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_429_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_283_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 283 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_283 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_150_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_282_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_283_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 283 (history t) = VM.find 283 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_283_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_150_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_282_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_150_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_282_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_286_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 286 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_286 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_285_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_286_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 286 (history t) = VM.find 286 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_286_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_285_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_285_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_289_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 289 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_289 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_288_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_289_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 289 (history t) = VM.find 289 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_289_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_288_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_288_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_292_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 292 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_292 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_284_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_291_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_292_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 292 (history t) = VM.find 292 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_292_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_284_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_291_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_284_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_291_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_294_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 294 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_294 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_293_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_294_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 294 (history t) = VM.find 294 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_294_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_293_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_293_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_302_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 302 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_302 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_301_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_302_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 302 (history t) = VM.find 302 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_302_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_301_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_301_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_304_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 304 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_304 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_303_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_304_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 304 (history t) = VM.find 304 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_304_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_303_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_303_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_306_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 306 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_306 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_305_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_306_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 306 (history t) = VM.find 306 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_306_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_305_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_305_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_308_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 308 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_308 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_307_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_308_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 308 (history t) = VM.find 308 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_308_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_307_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_307_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_310_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 310 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_310 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_309_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_310_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 310 (history t) = VM.find 310 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_310_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_309_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_309_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_312_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 312 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_312 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_311_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_312_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 312 (history t) = VM.find 312 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_312_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_311_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_311_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_314_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 314 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_314 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_313_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_314_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 314 (history t) = VM.find 314 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_314_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_313_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_313_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_316_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 316 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_316 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_315_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_316_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 316 (history t) = VM.find 316 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_316_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_315_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_315_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_318_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 318 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_318 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_317_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_318_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 318 (history t) = VM.find 318 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_318_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_317_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_317_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_320_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 320 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_320 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_319_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_320_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 320 (history t) = VM.find 320 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_320_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_319_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_319_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_322_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 322 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_322 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_321_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_322_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 322 (history t) = VM.find 322 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_322_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_321_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_321_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_324_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 324 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_324 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_323_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_324_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 324 (history t) = VM.find 324 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_324_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_323_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_323_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_326_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 326 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_326 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_325_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_326_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 326 (history t) = VM.find 326 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_326_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_325_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_325_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_328_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 328 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_328 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_327_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_328_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 328 (history t) = VM.find 328 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_328_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_327_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_327_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_330_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 330 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_330 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_329_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_330_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 330 (history t) = VM.find 330 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_330_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_329_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_329_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_332_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 332 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_332 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_331_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_332_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 332 (history t) = VM.find 332 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_332_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_331_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_331_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_334_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 334 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_334 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_333_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_334_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 334 (history t) = VM.find 334 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_334_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_333_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_333_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_336_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 336 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_336 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_335_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_336_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 336 (history t) = VM.find 336 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_336_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_335_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_335_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_338_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 338 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_338 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_337_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_338_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 338 (history t) = VM.find 338 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_338_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_337_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_337_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_340_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 340 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_340 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_339_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_340_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 340 (history t) = VM.find 340 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_340_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_339_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_339_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_342_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 342 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_342 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_341_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_342_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 342 (history t) = VM.find 342 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_342_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_341_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_341_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_344_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 344 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_344 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_343_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_344_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 344 (history t) = VM.find 344 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_344_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_343_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_343_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_346_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 346 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_346 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_345_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_346_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 346 (history t) = VM.find 346 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_346_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_345_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_345_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_348_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 348 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_348 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_347_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_348_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 348 (history t) = VM.find 348 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_348_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_347_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_347_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_350_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 350 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_350 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_349_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_350_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 350 (history t) = VM.find 350 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_350_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_349_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_349_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_352_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 352 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_352 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_351_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_352_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 352 (history t) = VM.find 352 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_352_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_351_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_351_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_354_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 354 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_354 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_353_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_354_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 354 (history t) = VM.find 354 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_354_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_353_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_353_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_356_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 356 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_356 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_355_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_356_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 356 (history t) = VM.find 356 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_356_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_355_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_355_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_358_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 358 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_358 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_357_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_358_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 358 (history t) = VM.find 358 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_358_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_357_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_357_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_388_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 388 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_388 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_387_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_388_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 388 (history t) = VM.find 388 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_388_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_387_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_387_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_396_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 396 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_396 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_394_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_395_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_396_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 396 (history t) = VM.find 396 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_396_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_394_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_395_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_394_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_395_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_414_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 414 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_414 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_410_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_413_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_414_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 414 (history t) = VM.find 414 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_414_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_410_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_413_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_410_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_413_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_423_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 423 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_423 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_420_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_422_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_423_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 423 (history t) = VM.find 423 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_423_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_420_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_422_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_420_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_422_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_426_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 426 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_426 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_124_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_408_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_426_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 426 (history t) = VM.find 426 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_426_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_124_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_408_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_124_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_408_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_287_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 287 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_287 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_284_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_286_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_287_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 287 (history t) = VM.find 287 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_287_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_284_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_286_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_284_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_286_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_295_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 295 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_295 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_292_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_294_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_295_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 295 (history t) = VM.find 295 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_295_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_292_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_294_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_292_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_294_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_359_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 359 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_359 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_302_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_304_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_359_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 359 (history t) = VM.find 359 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_359_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_302_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_304_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_302_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_304_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_390_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 390 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_390 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_388_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_389_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_390_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 390 (history t) = VM.find 390 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_390_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_388_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_389_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_388_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_389_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_397_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 397 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_397 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_393_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_396_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_397_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 397 (history t) = VM.find 397 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_397_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_393_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_396_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_393_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_396_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_416_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 416 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_416 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_411_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_414_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_415_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_416_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 416 (history t) = VM.find 416 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_416_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_411_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_414_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_415_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_411_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_414_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_415_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_425_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 425 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_425 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_421_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_423_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_424_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_425_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 425 (history t) = VM.find 425 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_425_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_421_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_423_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_424_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_421_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_423_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_424_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_432_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 432 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_432 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_283_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_432_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 432 (history t) = VM.find 432 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_432_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_283_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_283_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_438_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 438 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_438 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_283_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_438_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 438 (history t) = VM.find 438 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_438_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_283_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_283_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_290_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 290 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_290 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_287_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_289_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_290_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 290 (history t) = VM.find 290 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_290_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_287_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_289_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_287_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_289_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_360_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 360 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_360 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_306_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_359_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_360_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 360 (history t) = VM.find 360 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_360_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_306_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_359_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_306_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_392_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 392 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_392 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_390_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_391_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_392_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 392 (history t) = VM.find 392 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_392_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_390_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_391_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_390_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_391_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_418_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 418 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_418 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_412_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_416_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_417_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_418_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 418 (history t) = VM.find 418 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_418_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_412_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_416_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_417_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_412_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_416_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_417_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_439_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 439 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_439 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_284_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_438_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_439_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 439 (history t) = VM.find 439 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_439_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_284_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_438_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_284_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_438_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_361_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 361 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_361 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_308_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_360_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_361_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (7 <= t)%coq_nat -> (7 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 361 (history t) = VM.find 361 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_361_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_308_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_360_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_308_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_360_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_427_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 427 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_427 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_418_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_426_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_427_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (7 <= t)%coq_nat -> (7 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 427 (history t) = VM.find 427 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_427_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_418_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_426_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_418_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_426_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_436_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 436 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_436 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_392_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_397_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_436_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (7 <= t)%coq_nat -> (7 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 436 (history t) = VM.find 436 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_436_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_392_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_397_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_392_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_397_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_362_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 362 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_362 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_310_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_361_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_362_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (8 <= t)%coq_nat -> (8 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 362 (history t) = VM.find 362 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_362_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_310_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_361_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_310_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_361_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_428_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 428 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_428 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_425_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_427_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_428_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (8 <= t)%coq_nat -> (8 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 428 (history t) = VM.find 428 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_428_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_425_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_427_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_425_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_427_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_363_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 363 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_363 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_312_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_362_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_363_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (9 <= t)%coq_nat -> (9 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 363 (history t) = VM.find 363 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_363_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_312_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_362_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_312_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_362_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_364_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 364 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_364 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_314_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_363_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_364_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (10 <= t)%coq_nat -> (10 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 364 (history t) = VM.find 364 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_364_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_314_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_363_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_314_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_363_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_365_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 365 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_365 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_316_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_364_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_365_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (11 <= t)%coq_nat -> (11 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 365 (history t) = VM.find 365 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_365_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_316_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_364_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_316_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_364_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_366_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 366 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_366 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_318_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_365_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_366_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (12 <= t)%coq_nat -> (12 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 366 (history t) = VM.find 366 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_366_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_318_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_365_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_318_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_365_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_367_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 367 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_367 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_320_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_366_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_367_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (13 <= t)%coq_nat -> (13 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 367 (history t) = VM.find 367 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_367_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_320_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_366_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_320_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_366_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_368_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 368 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_368 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_322_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_367_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_368_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (14 <= t)%coq_nat -> (14 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 368 (history t) = VM.find 368 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_368_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_322_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_367_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_322_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_367_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_369_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 369 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_369 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_324_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_368_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_369_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (15 <= t)%coq_nat -> (15 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 369 (history t) = VM.find 369 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_369_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_324_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_368_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_324_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_368_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_370_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 370 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_370 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_326_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_369_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_370_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (16 <= t)%coq_nat -> (16 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 370 (history t) = VM.find 370 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_370_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_326_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_369_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_326_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_369_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_371_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 371 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_371 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_328_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_370_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_371_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (17 <= t)%coq_nat -> (17 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 371 (history t) = VM.find 371 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_371_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_328_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_370_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_328_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_370_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_372_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 372 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_372 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_330_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_371_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_372_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (18 <= t)%coq_nat -> (18 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 372 (history t) = VM.find 372 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_372_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_330_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_371_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_330_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_371_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_373_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 373 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_373 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_332_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_372_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_373_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (19 <= t)%coq_nat -> (19 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 373 (history t) = VM.find 373 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_373_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_332_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_372_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_332_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_372_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_374_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 374 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_374 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_334_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_373_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_374_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (20 <= t)%coq_nat -> (20 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 374 (history t) = VM.find 374 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_374_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_334_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_373_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_334_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_373_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_375_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 375 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_375 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_336_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_374_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_375_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (21 <= t)%coq_nat -> (21 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 375 (history t) = VM.find 375 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_375_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_336_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_374_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_336_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_374_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_376_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 376 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_376 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_338_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_375_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_376_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (22 <= t)%coq_nat -> (22 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 376 (history t) = VM.find 376 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_376_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_338_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_375_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_338_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_375_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_377_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 377 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_377 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_340_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_376_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_377_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (23 <= t)%coq_nat -> (23 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 377 (history t) = VM.find 377 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_377_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_340_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_376_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_340_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_376_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_378_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 378 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_378 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_342_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_377_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_378_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (24 <= t)%coq_nat -> (24 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 378 (history t) = VM.find 378 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_378_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_342_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_377_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_342_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_377_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_379_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 379 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_379 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_344_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_378_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_379_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (25 <= t)%coq_nat -> (25 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 379 (history t) = VM.find 379 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_379_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_344_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_378_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_344_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_378_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_380_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 380 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_380 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_346_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_379_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_380_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (26 <= t)%coq_nat -> (26 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 380 (history t) = VM.find 380 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_380_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_346_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_379_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_346_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_379_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_381_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 381 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_381 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_348_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_380_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_381_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (27 <= t)%coq_nat -> (27 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 381 (history t) = VM.find 381 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_381_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_348_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_380_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_348_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_380_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_382_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 382 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_382 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_350_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_381_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_382_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (28 <= t)%coq_nat -> (28 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 382 (history t) = VM.find 382 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_382_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_350_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_381_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_350_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_381_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_383_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 383 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_383 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_352_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_382_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_383_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (29 <= t)%coq_nat -> (29 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 383 (history t) = VM.find 383 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_383_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_352_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_382_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_352_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_382_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_384_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 384 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_384 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_354_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_383_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_384_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (30 <= t)%coq_nat -> (30 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 384 (history t) = VM.find 384 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_384_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_354_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_383_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_354_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_383_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_385_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 385 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_385 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_356_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_384_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_385_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (31 <= t)%coq_nat -> (31 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 385 (history t) = VM.find 385 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_385_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_356_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_384_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_356_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_384_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_386_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 386 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_386 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_358_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_385_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_386_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (32 <= t)%coq_nat -> (32 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 386 (history t) = VM.find 386 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_386_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_358_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_385_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_358_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_385_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_431_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 431 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_431 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_386_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_431_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (33 <= t)%coq_nat -> (33 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 431 (history t) = VM.find 431 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_431_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_386_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_386_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_433_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 433 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_433 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_431_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_432_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_433_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (34 <= t)%coq_nat -> (34 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 433 (history t) = VM.find 433 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_433_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_431_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_432_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_431_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_432_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_434_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 434 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_434 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_430_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_433_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_434_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (35 <= t)%coq_nat -> (35 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 434 (history t) = VM.find 434 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_434_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_430_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_433_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_430_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_433_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_435_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 435 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_435 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_428_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_434_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_435_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (36 <= t)%coq_nat -> (36 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 435 (history t) = VM.find 435 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_435_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_428_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_434_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_428_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_434_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_437_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 437 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_437 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_435_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_436_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_437_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (37 <= t)%coq_nat -> (37 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 437 (history t) = VM.find 437 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_437_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_435_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_436_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_435_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_436_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_440_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 440 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_440 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_437_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_439_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_440_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (38 <= t)%coq_nat -> (38 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 440 (history t) = VM.find 440 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_440_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_437_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_439_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_437_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_439_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_441_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 441 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_441 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_290_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_440_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_441_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (39 <= t)%coq_nat -> (39 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 441 (history t) = VM.find 441 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_441_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_290_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_440_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_290_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_440_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_442_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 442 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_node_output_442 inputs path (history time) (history time) (history (S time))).
 - apply (exception_concrete_295_history inputs path history limit Boundary Steps time); lia.
 - apply (exception_concrete_441_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_442_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 442 (history t) = VM.find 442 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_node_442_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_concrete_295_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_concrete_441_history inputs path history limit Boundary Steps t); lia.
 - apply (exception_stable_295_history inputs path history limit Boundary Steps t u); lia.
 - apply (exception_stable_441_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem exception_concrete_128_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 128 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (x0_connection_output_128 (formal_invalid_policy inputs path) (history time) (history time) (history (S time))).
 - apply (exception_concrete_442_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem exception_stable_128_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (41 <= t)%coq_nat -> (41 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 128 (history t) = VM.find 128 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (exception_wire_128_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (exception_stable_442_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Print Assumptions exception_stable_128_history.
