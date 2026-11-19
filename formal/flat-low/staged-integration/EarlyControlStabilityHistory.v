Require Import CoreSocModel ComparisonNodes EarlyControlDataCongruence EarlyControlJointCongruence EarlyControlWireCongruence JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization JointUpdateOutputCertificates DataAddressExpressionCertificates DataAddressUIntCertificates DataAddressPositionCertificate DataAddressSafetyCertificate X0ConcreteOutputCertificates X0ConcreteExpressionCertificates X0UIntExpressionCertificates SelectedUIntNodeCongruence SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma early_control_data_uint_output node expression inputs path old result :
 List.In (node,expression) data_address_expected_nodes ->
 (forall site value,
  eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories expression old old = Some value ->
  exists width bits, value = Gval (Fuint width) bits) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false old flat_statements = Some result ->
 exists width bits, VM.find node result = Some (Gval (Fuint width) bits).
Proof.
 intros Member Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes node expression data_address_actual_node_expressions data_address_actual_nodes_safe Member)
 as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node expression (formal_invalid_policy inputs path)
 flat_memories old false old result Position Step) as [value Eval]. rewrite add0n in Eval.
 destruct (Typed _ value Eval) as [width [bits Eq]]. subst value.
 exists width,bits.
 exact (formal_combinational_known_node count flat_statements tail node expression width (Gval (Fuint width) bits)
 (formal_invalid_policy inputs path) flat_memories old old result Position Safe Nonreg Eval (Logic.eq_refl _) Step).
Qed.
Lemma early_control_node_7805_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7750 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7750 left = VM.find 7750 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7805 next_left = VM.find 7805 next_right.
Proof.
 intros Concrete Equal L R.
 apply (x0_selected_uint_node_congruent 7805 x0_concrete_expr_7805 (formal_invalid_policy inputs path) left right next_left next_right).
 - apply (List.nth_error_In X0ConcretePositionCertificate.x0_expected_nodes 152%nat). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_7805 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Equal. reflexivity.
 - intros site value Eval. destruct (x0_uint_result_7805 _ site flat_memories left value Concrete Eval) as [width [bits Eq]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
Lemma early_control_member_851 : List.In (851%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 21%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_851_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 851 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 851 32 early_control_member_851 Steps time Upper).
 destruct (Boundary 851%nat 32%nat early_control_member_851) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_851_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 851 (history t) = VM.find 851 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 851 32 early_control_member_851 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 851 32 early_control_member_851 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_852 : List.In (852%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 22%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_852_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 852 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 852 32 early_control_member_852 Steps time Upper).
 destruct (Boundary 852%nat 32%nat early_control_member_852) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_852_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 852 (history t) = VM.find 852 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 852 32 early_control_member_852 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 852 32 early_control_member_852 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_853 : List.In (853%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 23%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_853_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 853 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 853 32 early_control_member_853 Steps time Upper).
 destruct (Boundary 853%nat 32%nat early_control_member_853) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_853_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 853 (history t) = VM.find 853 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 853 32 early_control_member_853 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 853 32 early_control_member_853 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_854 : List.In (854%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 24%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_854_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 854 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 854 32 early_control_member_854 Steps time Upper).
 destruct (Boundary 854%nat 32%nat early_control_member_854) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_854_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 854 (history t) = VM.find 854 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 854 32 early_control_member_854 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 854 32 early_control_member_854 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_855 : List.In (855%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 25%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_855_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 855 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 855 32 early_control_member_855 Steps time Upper).
 destruct (Boundary 855%nat 32%nat early_control_member_855) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_855_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 855 (history t) = VM.find 855 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 855 32 early_control_member_855 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 855 32 early_control_member_855 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_856 : List.In (856%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 26%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_856_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 856 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 856 32 early_control_member_856 Steps time Upper).
 destruct (Boundary 856%nat 32%nat early_control_member_856) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_856_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 856 (history t) = VM.find 856 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 856 32 early_control_member_856 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 856 32 early_control_member_856 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_857 : List.In (857%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 27%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_857_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 857 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 857 32 early_control_member_857 Steps time Upper).
 destruct (Boundary 857%nat 32%nat early_control_member_857) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_857_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 857 (history t) = VM.find 857 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 857 32 early_control_member_857 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 857 32 early_control_member_857 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_858 : List.In (858%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 28%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_858_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 858 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 858 32 early_control_member_858 Steps time Upper).
 destruct (Boundary 858%nat 32%nat early_control_member_858) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_858_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 858 (history t) = VM.find 858 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 858 32 early_control_member_858 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 858 32 early_control_member_858 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_859 : List.In (859%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 29%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_859_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 859 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 859 32 early_control_member_859 Steps time Upper).
 destruct (Boundary 859%nat 32%nat early_control_member_859) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_859_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 859 (history t) = VM.find 859 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 859 32 early_control_member_859 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 859 32 early_control_member_859 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_860 : List.In (860%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 30%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_860_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 860 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 860 32 early_control_member_860 Steps time Upper).
 destruct (Boundary 860%nat 32%nat early_control_member_860) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_860_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 860 (history t) = VM.find 860 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 860 32 early_control_member_860 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 860 32 early_control_member_860 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_861 : List.In (861%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 31%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_861_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 861 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 861 32 early_control_member_861 Steps time Upper).
 destruct (Boundary 861%nat 32%nat early_control_member_861) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_861_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 861 (history t) = VM.find 861 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 861 32 early_control_member_861 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 861 32 early_control_member_861 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_862 : List.In (862%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 32%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_862_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 862 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 862 32 early_control_member_862 Steps time Upper).
 destruct (Boundary 862%nat 32%nat early_control_member_862) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_862_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 862 (history t) = VM.find 862 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 862 32 early_control_member_862 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 862 32 early_control_member_862 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_863 : List.In (863%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 33%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_863_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 863 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 863 32 early_control_member_863 Steps time Upper).
 destruct (Boundary 863%nat 32%nat early_control_member_863) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_863_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 863 (history t) = VM.find 863 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 863 32 early_control_member_863 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 863 32 early_control_member_863 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_864 : List.In (864%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 34%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_864_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 864 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 864 32 early_control_member_864 Steps time Upper).
 destruct (Boundary 864%nat 32%nat early_control_member_864) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_864_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 864 (history t) = VM.find 864 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 864 32 early_control_member_864 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 864 32 early_control_member_864 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_865 : List.In (865%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 35%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_865_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 865 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 865 32 early_control_member_865 Steps time Upper).
 destruct (Boundary 865%nat 32%nat early_control_member_865) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_865_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 865 (history t) = VM.find 865 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 865 32 early_control_member_865 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 865 32 early_control_member_865 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_866 : List.In (866%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 36%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_866_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 866 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 866 32 early_control_member_866 Steps time Upper).
 destruct (Boundary 866%nat 32%nat early_control_member_866) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_866_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 866 (history t) = VM.find 866 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 866 32 early_control_member_866 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 866 32 early_control_member_866 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_867 : List.In (867%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 37%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_867_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 867 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 867 32 early_control_member_867 Steps time Upper).
 destruct (Boundary 867%nat 32%nat early_control_member_867) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_867_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 867 (history t) = VM.find 867 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 867 32 early_control_member_867 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 867 32 early_control_member_867 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_868 : List.In (868%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 38%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_868_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 868 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 868 32 early_control_member_868 Steps time Upper).
 destruct (Boundary 868%nat 32%nat early_control_member_868) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_868_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 868 (history t) = VM.find 868 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 868 32 early_control_member_868 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 868 32 early_control_member_868 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_869 : List.In (869%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 39%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_869_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 869 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 869 32 early_control_member_869 Steps time Upper).
 destruct (Boundary 869%nat 32%nat early_control_member_869) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_869_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 869 (history t) = VM.find 869 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 869 32 early_control_member_869 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 869 32 early_control_member_869 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_870 : List.In (870%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 40%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_870_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 870 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 870 32 early_control_member_870 Steps time Upper).
 destruct (Boundary 870%nat 32%nat early_control_member_870) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_870_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 870 (history t) = VM.find 870 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 870 32 early_control_member_870 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 870 32 early_control_member_870 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_871 : List.In (871%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 41%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_871_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 871 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 871 32 early_control_member_871 Steps time Upper).
 destruct (Boundary 871%nat 32%nat early_control_member_871) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_871_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 871 (history t) = VM.find 871 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 871 32 early_control_member_871 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 871 32 early_control_member_871 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_872 : List.In (872%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 42%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_872_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 872 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 872 32 early_control_member_872 Steps time Upper).
 destruct (Boundary 872%nat 32%nat early_control_member_872) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_872_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 872 (history t) = VM.find 872 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 872 32 early_control_member_872 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 872 32 early_control_member_872 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_873 : List.In (873%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 43%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_873_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 873 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 873 32 early_control_member_873 Steps time Upper).
 destruct (Boundary 873%nat 32%nat early_control_member_873) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_873_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 873 (history t) = VM.find 873 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 873 32 early_control_member_873 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 873 32 early_control_member_873 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_874 : List.In (874%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 44%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_874_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 874 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 874 32 early_control_member_874 Steps time Upper).
 destruct (Boundary 874%nat 32%nat early_control_member_874) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_874_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 874 (history t) = VM.find 874 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 874 32 early_control_member_874 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 874 32 early_control_member_874 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_875 : List.In (875%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 45%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_875_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 875 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 875 32 early_control_member_875 Steps time Upper).
 destruct (Boundary 875%nat 32%nat early_control_member_875) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_875_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 875 (history t) = VM.find 875 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 875 32 early_control_member_875 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 875 32 early_control_member_875 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_876 : List.In (876%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 46%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_876_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 876 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 876 32 early_control_member_876 Steps time Upper).
 destruct (Boundary 876%nat 32%nat early_control_member_876) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_876_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 876 (history t) = VM.find 876 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 876 32 early_control_member_876 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 876 32 early_control_member_876 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_877 : List.In (877%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 47%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_877_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 877 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 877 32 early_control_member_877 Steps time Upper).
 destruct (Boundary 877%nat 32%nat early_control_member_877) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_877_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 877 (history t) = VM.find 877 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 877 32 early_control_member_877 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 877 32 early_control_member_877 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_878 : List.In (878%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 48%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_878_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 878 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 878 32 early_control_member_878 Steps time Upper).
 destruct (Boundary 878%nat 32%nat early_control_member_878) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_878_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 878 (history t) = VM.find 878 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 878 32 early_control_member_878 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 878 32 early_control_member_878 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_879 : List.In (879%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 49%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_879_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 879 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 879 32 early_control_member_879 Steps time Upper).
 destruct (Boundary 879%nat 32%nat early_control_member_879) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_879_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 879 (history t) = VM.find 879 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 879 32 early_control_member_879 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 879 32 early_control_member_879 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_880 : List.In (880%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 50%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_880_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 880 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 880 32 early_control_member_880 Steps time Upper).
 destruct (Boundary 880%nat 32%nat early_control_member_880) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_880_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 880 (history t) = VM.find 880 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 880 32 early_control_member_880 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 880 32 early_control_member_880 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_881 : List.In (881%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 51%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_881_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 881 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 881 32 early_control_member_881 Steps time Upper).
 destruct (Boundary 881%nat 32%nat early_control_member_881) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_881_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 881 (history t) = VM.find 881 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 881 32 early_control_member_881 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 881 32 early_control_member_881 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_882 : List.In (882%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 52%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_882_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 882 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 882 32 early_control_member_882 Steps time Upper).
 destruct (Boundary 882%nat 32%nat early_control_member_882) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_882_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 882 (history t) = VM.find 882 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 882 32 early_control_member_882 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 882 32 early_control_member_882 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_7748 : List.In (7748%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 53%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_7748_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7748 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7748 32 early_control_member_7748 Steps time Upper).
 destruct (Boundary 7748%nat 32%nat early_control_member_7748) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_7748_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7748 (history t) = VM.find 7748 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7748 32 early_control_member_7748 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7748 32 early_control_member_7748 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_7750 : List.In (7750%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 55%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_7750_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7750 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7750 32 early_control_member_7750 Steps time Upper).
 destruct (Boundary 7750%nat 32%nat early_control_member_7750) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_7750_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7750 (history t) = VM.find 7750 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7750 32 early_control_member_7750 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7750 32 early_control_member_7750 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_7752 : List.In (7752%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 57%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_7752_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7752 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7752 32 early_control_member_7752 Steps time Upper).
 destruct (Boundary 7752%nat 32%nat early_control_member_7752) as [bits [Size Lookup]].
 exists 32%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_7752_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7752 (history t) = VM.find 7752 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7752 32 early_control_member_7752 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7752 32 early_control_member_7752 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_7756 : List.In (7756%nat,2%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 61%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_7756_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7756 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7756 2 early_control_member_7756 Steps time Upper).
 destruct (Boundary 7756%nat 2%nat early_control_member_7756) as [bits [Size Lookup]].
 exists 2%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_7756_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7756 (history t) = VM.find 7756 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7756 2 early_control_member_7756 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7756 2 early_control_member_7756 Steps u UU). reflexivity.
Qed.
Lemma early_control_member_7757 : List.In (7757%nat,1%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 62%nat). vm_compute. reflexivity. Qed.
Theorem early_control_concrete_7757_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (0 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7757 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 rewrite (joint_update_register_history_same _ history limit 7757 1 early_control_member_7757 Steps time Upper).
 destruct (Boundary 7757%nat 1%nat early_control_member_7757) as [bits [Size Lookup]].
 exists 1%nat, bits. exact Lookup.
Qed.
Theorem early_control_stable_7757_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (0 <= t)%coq_nat -> (0 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7757 (history t) = VM.find 7757 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 rewrite (joint_update_register_history_same _ history limit 7757 1 early_control_member_7757 Steps t UT).
 rewrite (joint_update_register_history_same _ history limit 7757 1 early_control_member_7757 Steps u UU). reflexivity.
Qed.
Theorem early_control_concrete_83_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 83 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_83_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_7748_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 32%nat, bits. exact Value.
Qed.
Theorem early_control_stable_83_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 83 (history t) = VM.find 83 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_83_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_7748_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7803_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7803 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7748 : exists width bits, VM.find 7748 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7748_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7803 address_expr_7803 inputs path (history time) (history (S time)) early_control_data_member_7803).
 - intros site value Eval. exact (address_uint_result_7803 inputs path site flat_memories (history time) value H7748 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7803_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7803 (history t) = VM.find 7803 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7803_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7748_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7748_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7804_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7804 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7748 : exists width bits, VM.find 7748 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7748_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7804 address_expr_7804 inputs path (history time) (history (S time)) early_control_data_member_7804).
 - intros site value Eval. exact (address_uint_result_7804 inputs path site flat_memories (history time) value H7748 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7804_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7804 (history t) = VM.find 7804 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7804_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7748_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7748_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7805_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7805 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7750 : exists width bits, VM.find 7750 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7750_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7805 address_expr_7805 inputs path (history time) (history (S time)) early_control_data_member_7805).
 - intros site value Eval. exact (address_uint_result_7805 inputs path site flat_memories (history time) value H7750 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7805_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7805 (history t) = VM.find 7805 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7805_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7750_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7750_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7814_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7814 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7756 : exists width bits, VM.find 7756 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7756_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7814 address_expr_7814 inputs path (history time) (history (S time)) early_control_data_member_7814).
 - intros site value Eval. exact (address_uint_result_7814 inputs path site flat_memories (history time) value H7756 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7814_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7814 (history t) = VM.find 7814 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7814_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7756_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7756_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7817_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7817 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7756 : exists width bits, VM.find 7756 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7756_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7817 address_expr_7817 inputs path (history time) (history (S time)) early_control_data_member_7817).
 - intros site value Eval. exact (address_uint_result_7817 inputs path site flat_memories (history time) value H7756 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7817_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (1 <= t)%coq_nat -> (1 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7817 (history t) = VM.find 7817 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7817_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7756_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7756_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_780_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_780_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_7803_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 5%nat, bits. exact Value.
Qed.
Theorem early_control_stable_780_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 780 (history t) = VM.find 780 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_780_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_7803_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_781_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_781_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_7804_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 5%nat, bits. exact Value.
Qed.
Theorem early_control_stable_781_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 781 (history t) = VM.find 781 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_781_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_7804_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7806_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7806 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7803 : exists width bits, VM.find 7803 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7803_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7806 address_expr_7806 inputs path (history time) (history (S time)) early_control_data_member_7806).
 - intros site value Eval. exact (address_uint_result_7806 inputs path site flat_memories (history time) value H7803 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7806_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7806 (history t) = VM.find 7806 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7806_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7803_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7803_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7808_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7808 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7803 : exists width bits, VM.find 7803 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7803_history inputs path history limit Boundary Steps time); lia. }
 assert (H7805 : exists width bits, VM.find 7805 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7805_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7808 address_expr_7808 inputs path (history time) (history (S time)) early_control_data_member_7808).
 - intros site value Eval. exact (address_uint_result_7808 inputs path site flat_memories (history time) value H7803 H7805 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7808_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7808 (history t) = VM.find 7808 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7808_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7803_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7805_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7803_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7805_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7810_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7810 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7804 : exists width bits, VM.find 7804 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7804_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7810 address_expr_7810 inputs path (history time) (history (S time)) early_control_data_member_7810).
 - intros site value Eval. exact (address_uint_result_7810 inputs path site flat_memories (history time) value H7804 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7810_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7810 (history t) = VM.find 7810 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7810_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7804_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7804_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7812_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7812 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7804 : exists width bits, VM.find 7804 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7804_history inputs path history limit Boundary Steps time); lia. }
 assert (H7805 : exists width bits, VM.find 7805 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7805_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7812 address_expr_7812 inputs path (history time) (history (S time)) early_control_data_member_7812).
 - intros site value Eval. exact (address_uint_result_7812 inputs path site flat_memories (history time) value H7804 H7805 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7812_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7812 (history t) = VM.find 7812 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7812_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7804_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7805_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7804_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7805_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8249_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_8249_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_83_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 32%nat, bits. exact Value.
Qed.
Theorem early_control_stable_8249_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (2 <= t)%coq_nat -> (2 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8249 (history t) = VM.find 8249 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_8249_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_83_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_883_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 883 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 883 address_expr_883 inputs path (history time) (history (S time)) early_control_data_member_883).
 - intros site value Eval. exact (address_uint_result_883 inputs path site flat_memories (history time) value H780 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_883_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 883 (history t) = VM.find 883 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_883_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_884_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 884 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H851 : exists width bits, VM.find 851 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_851_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 884 address_expr_884 inputs path (history time) (history (S time)) early_control_data_member_884).
 - intros site value Eval. exact (address_uint_result_884 inputs path site flat_memories (history time) value H780 H851 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_884_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 884 (history t) = VM.find 884 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_884_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_851_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_851_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_918_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 918 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 918 address_expr_918 inputs path (history time) (history (S time)) early_control_data_member_918).
 - intros site value Eval. exact (address_uint_result_918 inputs path site flat_memories (history time) value H781 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_918_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 918 (history t) = VM.find 918 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_918_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_919_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 919 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H851 : exists width bits, VM.find 851 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_851_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 919 address_expr_919 inputs path (history time) (history (S time)) early_control_data_member_919).
 - intros site value Eval. exact (address_uint_result_919 inputs path site flat_memories (history time) value H781 H851 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_919_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 919 (history t) = VM.find 919 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_919_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_851_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_851_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7807_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7807 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7757 : exists width bits, VM.find 7757 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7757_history inputs path history limit Boundary Steps time); lia. }
 assert (H7806 : exists width bits, VM.find 7806 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7806_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7807 address_expr_7807 inputs path (history time) (history (S time)) early_control_data_member_7807).
 - intros site value Eval. exact (address_uint_result_7807 inputs path site flat_memories (history time) value H7757 H7806 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7807_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7807 (history t) = VM.find 7807 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7807_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7757_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7806_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7757_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7806_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7811_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7811 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7757 : exists width bits, VM.find 7757 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7757_history inputs path history limit Boundary Steps time); lia. }
 assert (H7810 : exists width bits, VM.find 7810 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7810_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7811 address_expr_7811 inputs path (history time) (history (S time)) early_control_data_member_7811).
 - intros site value Eval. exact (address_uint_result_7811 inputs path site flat_memories (history time) value H7757 H7810 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7811_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7811 (history t) = VM.find 7811 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7811_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7757_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7810_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7757_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7810_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8263_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8263 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8263 address_expr_8263 inputs path (history time) (history (S time)) early_control_data_member_8263).
 - intros site value Eval. exact (address_uint_result_8263 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8263_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8263 (history t) = VM.find 8263 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8263_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8265_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8265 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8265 address_expr_8265 inputs path (history time) (history (S time)) early_control_data_member_8265).
 - intros site value Eval. exact (address_uint_result_8265 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8265_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8265 (history t) = VM.find 8265 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8265_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8267_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8267 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8267 address_expr_8267 inputs path (history time) (history (S time)) early_control_data_member_8267).
 - intros site value Eval. exact (address_uint_result_8267 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8267_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8267 (history t) = VM.find 8267 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8267_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8269_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8269 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8269 address_expr_8269 inputs path (history time) (history (S time)) early_control_data_member_8269).
 - intros site value Eval. exact (address_uint_result_8269 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8269_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8269 (history t) = VM.find 8269 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8269_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8271_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8271 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8271 address_expr_8271 inputs path (history time) (history (S time)) early_control_data_member_8271).
 - intros site value Eval. exact (address_uint_result_8271 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8271_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8271 (history t) = VM.find 8271 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8271_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8273_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8273 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8273 address_expr_8273 inputs path (history time) (history (S time)) early_control_data_member_8273).
 - intros site value Eval. exact (address_uint_result_8273 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8273_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8273 (history t) = VM.find 8273 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8273_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8275_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8275 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8275 address_expr_8275 inputs path (history time) (history (S time)) early_control_data_member_8275).
 - intros site value Eval. exact (address_uint_result_8275 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8275_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8275 (history t) = VM.find 8275 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8275_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8277_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8277 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8277 address_expr_8277 inputs path (history time) (history (S time)) early_control_data_member_8277).
 - intros site value Eval. exact (address_uint_result_8277 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8277_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8277 (history t) = VM.find 8277 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8277_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8279_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8279 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8279 address_expr_8279 inputs path (history time) (history (S time)) early_control_data_member_8279).
 - intros site value Eval. exact (address_uint_result_8279 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8279_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8279 (history t) = VM.find 8279 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8279_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8281_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8281 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8281 address_expr_8281 inputs path (history time) (history (S time)) early_control_data_member_8281).
 - intros site value Eval. exact (address_uint_result_8281 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8281_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8281 (history t) = VM.find 8281 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8281_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8283_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8283 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8283 address_expr_8283 inputs path (history time) (history (S time)) early_control_data_member_8283).
 - intros site value Eval. exact (address_uint_result_8283 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8283_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8283 (history t) = VM.find 8283 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8283_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8285_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8285 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8285 address_expr_8285 inputs path (history time) (history (S time)) early_control_data_member_8285).
 - intros site value Eval. exact (address_uint_result_8285 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8285_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8285 (history t) = VM.find 8285 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8285_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8287_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8287 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8287 address_expr_8287 inputs path (history time) (history (S time)) early_control_data_member_8287).
 - intros site value Eval. exact (address_uint_result_8287 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8287_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8287 (history t) = VM.find 8287 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8287_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8289_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8289 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8289 address_expr_8289 inputs path (history time) (history (S time)) early_control_data_member_8289).
 - intros site value Eval. exact (address_uint_result_8289 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8289_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8289 (history t) = VM.find 8289 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8289_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8291_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8291 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8291 address_expr_8291 inputs path (history time) (history (S time)) early_control_data_member_8291).
 - intros site value Eval. exact (address_uint_result_8291 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8291_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8291 (history t) = VM.find 8291 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8291_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8293_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8293 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8293 address_expr_8293 inputs path (history time) (history (S time)) early_control_data_member_8293).
 - intros site value Eval. exact (address_uint_result_8293 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8293_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8293 (history t) = VM.find 8293 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8293_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8295_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8295 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8295 address_expr_8295 inputs path (history time) (history (S time)) early_control_data_member_8295).
 - intros site value Eval. exact (address_uint_result_8295 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8295_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8295 (history t) = VM.find 8295 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8295_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8297_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8297 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8297 address_expr_8297 inputs path (history time) (history (S time)) early_control_data_member_8297).
 - intros site value Eval. exact (address_uint_result_8297 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8297_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8297 (history t) = VM.find 8297 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8297_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8299_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8299 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8299 address_expr_8299 inputs path (history time) (history (S time)) early_control_data_member_8299).
 - intros site value Eval. exact (address_uint_result_8299 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8299_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8299 (history t) = VM.find 8299 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8299_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8301_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8301 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8301 address_expr_8301 inputs path (history time) (history (S time)) early_control_data_member_8301).
 - intros site value Eval. exact (address_uint_result_8301 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8301_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8301 (history t) = VM.find 8301 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8301_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8303_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8303 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8303 address_expr_8303 inputs path (history time) (history (S time)) early_control_data_member_8303).
 - intros site value Eval. exact (address_uint_result_8303 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8303_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8303 (history t) = VM.find 8303 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8303_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8305_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8305 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8305 address_expr_8305 inputs path (history time) (history (S time)) early_control_data_member_8305).
 - intros site value Eval. exact (address_uint_result_8305 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8305_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8305 (history t) = VM.find 8305 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8305_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8307_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8307 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8307 address_expr_8307 inputs path (history time) (history (S time)) early_control_data_member_8307).
 - intros site value Eval. exact (address_uint_result_8307 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8307_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8307 (history t) = VM.find 8307 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8307_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8309_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8309 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8309 address_expr_8309 inputs path (history time) (history (S time)) early_control_data_member_8309).
 - intros site value Eval. exact (address_uint_result_8309 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8309_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8309 (history t) = VM.find 8309 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8309_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8311_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8311 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8311 address_expr_8311 inputs path (history time) (history (S time)) early_control_data_member_8311).
 - intros site value Eval. exact (address_uint_result_8311 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8311_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8311 (history t) = VM.find 8311 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8311_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8313_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8313 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8313 address_expr_8313 inputs path (history time) (history (S time)) early_control_data_member_8313).
 - intros site value Eval. exact (address_uint_result_8313 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8313_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8313 (history t) = VM.find 8313 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8313_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8315_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8315 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8315 address_expr_8315 inputs path (history time) (history (S time)) early_control_data_member_8315).
 - intros site value Eval. exact (address_uint_result_8315 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8315_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8315 (history t) = VM.find 8315 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8315_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8317_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8317 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8317 address_expr_8317 inputs path (history time) (history (S time)) early_control_data_member_8317).
 - intros site value Eval. exact (address_uint_result_8317 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8317_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8317 (history t) = VM.find 8317 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8317_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8319_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8319 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8319 address_expr_8319 inputs path (history time) (history (S time)) early_control_data_member_8319).
 - intros site value Eval. exact (address_uint_result_8319 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8319_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8319 (history t) = VM.find 8319 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8319_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8321_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8321 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8321 address_expr_8321 inputs path (history time) (history (S time)) early_control_data_member_8321).
 - intros site value Eval. exact (address_uint_result_8321 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8321_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8321 (history t) = VM.find 8321 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8321_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8323_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8323 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8323 address_expr_8323 inputs path (history time) (history (S time)) early_control_data_member_8323).
 - intros site value Eval. exact (address_uint_result_8323 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8323_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8323 (history t) = VM.find 8323 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8323_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8325_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8325 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8325 address_expr_8325 inputs path (history time) (history (S time)) early_control_data_member_8325).
 - intros site value Eval. exact (address_uint_result_8325 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8325_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8325 (history t) = VM.find 8325 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8325_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8327_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8327 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8327 address_expr_8327 inputs path (history time) (history (S time)) early_control_data_member_8327).
 - intros site value Eval. exact (address_uint_result_8327 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8327_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8327 (history t) = VM.find 8327 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8327_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8329_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8329 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8329 address_expr_8329 inputs path (history time) (history (S time)) early_control_data_member_8329).
 - intros site value Eval. exact (address_uint_result_8329 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8329_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8329 (history t) = VM.find 8329 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8329_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8331_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8331 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8331 address_expr_8331 inputs path (history time) (history (S time)) early_control_data_member_8331).
 - intros site value Eval. exact (address_uint_result_8331 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8331_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8331 (history t) = VM.find 8331 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8331_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8333_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8333 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8333 address_expr_8333 inputs path (history time) (history (S time)) early_control_data_member_8333).
 - intros site value Eval. exact (address_uint_result_8333 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8333_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8333 (history t) = VM.find 8333 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8333_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8335_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8335 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8335 address_expr_8335 inputs path (history time) (history (S time)) early_control_data_member_8335).
 - intros site value Eval. exact (address_uint_result_8335 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8335_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8335 (history t) = VM.find 8335 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8335_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8337_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8337 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8337 address_expr_8337 inputs path (history time) (history (S time)) early_control_data_member_8337).
 - intros site value Eval. exact (address_uint_result_8337 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8337_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8337 (history t) = VM.find 8337 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8337_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8339_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8339 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8339 address_expr_8339 inputs path (history time) (history (S time)) early_control_data_member_8339).
 - intros site value Eval. exact (address_uint_result_8339 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8339_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8339 (history t) = VM.find 8339 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8339_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8341_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8341 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8341 address_expr_8341 inputs path (history time) (history (S time)) early_control_data_member_8341).
 - intros site value Eval. exact (address_uint_result_8341 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8341_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8341 (history t) = VM.find 8341 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8341_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8343_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8343 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8343 address_expr_8343 inputs path (history time) (history (S time)) early_control_data_member_8343).
 - intros site value Eval. exact (address_uint_result_8343 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8343_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8343 (history t) = VM.find 8343 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8343_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8345_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8345 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8345 address_expr_8345 inputs path (history time) (history (S time)) early_control_data_member_8345).
 - intros site value Eval. exact (address_uint_result_8345 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8345_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8345 (history t) = VM.find 8345 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8345_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8347_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8347 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8347 address_expr_8347 inputs path (history time) (history (S time)) early_control_data_member_8347).
 - intros site value Eval. exact (address_uint_result_8347 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8347_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8347 (history t) = VM.find 8347 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8347_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8349_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8349 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8349 address_expr_8349 inputs path (history time) (history (S time)) early_control_data_member_8349).
 - intros site value Eval. exact (address_uint_result_8349 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8349_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8349 (history t) = VM.find 8349 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8349_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8351_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8351 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8351 address_expr_8351 inputs path (history time) (history (S time)) early_control_data_member_8351).
 - intros site value Eval. exact (address_uint_result_8351 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8351_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8351 (history t) = VM.find 8351 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8351_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8353_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8353 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8353 address_expr_8353 inputs path (history time) (history (S time)) early_control_data_member_8353).
 - intros site value Eval. exact (address_uint_result_8353 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8353_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8353 (history t) = VM.find 8353 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8353_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8355_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8355 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8355 address_expr_8355 inputs path (history time) (history (S time)) early_control_data_member_8355).
 - intros site value Eval. exact (address_uint_result_8355 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8355_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8355 (history t) = VM.find 8355 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8355_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8357_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8357 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8357 address_expr_8357 inputs path (history time) (history (S time)) early_control_data_member_8357).
 - intros site value Eval. exact (address_uint_result_8357 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8357_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8357 (history t) = VM.find 8357 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8357_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8359_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8359 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8249 : exists width bits, VM.find 8249 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8249_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8359 address_expr_8359 inputs path (history time) (history (S time)) early_control_data_member_8359).
 - intros site value Eval. exact (address_uint_result_8359 inputs path site flat_memories (history time) value H8249 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8359_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (3 <= t)%coq_nat -> (3 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8359 (history t) = VM.find 8359 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8359_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8249_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8249_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_885_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 885 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H852 : exists width bits, VM.find 852 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_852_history inputs path history limit Boundary Steps time); lia. }
 assert (H884 : exists width bits, VM.find 884 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_884_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 885 address_expr_885 inputs path (history time) (history (S time)) early_control_data_member_885).
 - intros site value Eval. exact (address_uint_result_885 inputs path site flat_memories (history time) value H780 H852 H884 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_885_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 885 (history t) = VM.find 885 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_885_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_852_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_884_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_852_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_884_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_920_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 920 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H852 : exists width bits, VM.find 852 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_852_history inputs path history limit Boundary Steps time); lia. }
 assert (H919 : exists width bits, VM.find 919 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_919_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 920 address_expr_920 inputs path (history time) (history (S time)) early_control_data_member_920).
 - intros site value Eval. exact (address_uint_result_920 inputs path site flat_memories (history time) value H781 H852 H919 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_920_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 920 (history t) = VM.find 920 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_920_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_852_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_919_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_852_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_919_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7809_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7809 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7807 : exists width bits, VM.find 7807 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7807_history inputs path history limit Boundary Steps time); lia. }
 assert (H7808 : exists width bits, VM.find 7808 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7808_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7809 address_expr_7809 inputs path (history time) (history (S time)) early_control_data_member_7809).
 - intros site value Eval. exact (address_uint_result_7809 inputs path site flat_memories (history time) value H7807 H7808 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7809_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7809 (history t) = VM.find 7809 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7809_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7807_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7808_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7807_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7808_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7813_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7813 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7811 : exists width bits, VM.find 7811 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7811_history inputs path history limit Boundary Steps time); lia. }
 assert (H7812 : exists width bits, VM.find 7812 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7812_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7813 address_expr_7813 inputs path (history time) (history (S time)) early_control_data_member_7813).
 - intros site value Eval. exact (address_uint_result_7813 inputs path site flat_memories (history time) value H7811 H7812 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7813_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7813 (history t) = VM.find 7813 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7813_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7811_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7812_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7811_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7812_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8264_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8264 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8263 : exists width bits, VM.find 8263 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8263_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8264 address_expr_8264 inputs path (history time) (history (S time)) early_control_data_member_8264).
 - intros site value Eval. exact (address_uint_result_8264 inputs path site flat_memories (history time) value H8263 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8264_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8264 (history t) = VM.find 8264 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8264_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8263_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8263_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8266_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8266 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8265 : exists width bits, VM.find 8265 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8265_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8266 address_expr_8266 inputs path (history time) (history (S time)) early_control_data_member_8266).
 - intros site value Eval. exact (address_uint_result_8266 inputs path site flat_memories (history time) value H8265 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8266_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8266 (history t) = VM.find 8266 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8266_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8265_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8265_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8268_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8268 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8267 : exists width bits, VM.find 8267 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8267_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8268 address_expr_8268 inputs path (history time) (history (S time)) early_control_data_member_8268).
 - intros site value Eval. exact (address_uint_result_8268 inputs path site flat_memories (history time) value H8267 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8268_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8268 (history t) = VM.find 8268 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8268_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8267_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8267_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8270_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8270 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8269 : exists width bits, VM.find 8269 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8269_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8270 address_expr_8270 inputs path (history time) (history (S time)) early_control_data_member_8270).
 - intros site value Eval. exact (address_uint_result_8270 inputs path site flat_memories (history time) value H8269 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8270_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8270 (history t) = VM.find 8270 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8270_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8269_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8269_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8272_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8272 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8271 : exists width bits, VM.find 8271 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8271_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8272 address_expr_8272 inputs path (history time) (history (S time)) early_control_data_member_8272).
 - intros site value Eval. exact (address_uint_result_8272 inputs path site flat_memories (history time) value H8271 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8272_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8272 (history t) = VM.find 8272 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8272_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8271_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8271_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8274_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8274 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8273 : exists width bits, VM.find 8273 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8273_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8274 address_expr_8274 inputs path (history time) (history (S time)) early_control_data_member_8274).
 - intros site value Eval. exact (address_uint_result_8274 inputs path site flat_memories (history time) value H8273 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8274_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8274 (history t) = VM.find 8274 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8274_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8273_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8273_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8276_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8276 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8275 : exists width bits, VM.find 8275 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8275_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8276 address_expr_8276 inputs path (history time) (history (S time)) early_control_data_member_8276).
 - intros site value Eval. exact (address_uint_result_8276 inputs path site flat_memories (history time) value H8275 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8276_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8276 (history t) = VM.find 8276 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8276_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8275_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8275_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8278_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8278 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8277 : exists width bits, VM.find 8277 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8277_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8278 address_expr_8278 inputs path (history time) (history (S time)) early_control_data_member_8278).
 - intros site value Eval. exact (address_uint_result_8278 inputs path site flat_memories (history time) value H8277 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8278_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8278 (history t) = VM.find 8278 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8278_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8277_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8277_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8280_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8280 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8279 : exists width bits, VM.find 8279 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8279_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8280 address_expr_8280 inputs path (history time) (history (S time)) early_control_data_member_8280).
 - intros site value Eval. exact (address_uint_result_8280 inputs path site flat_memories (history time) value H8279 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8280_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8280 (history t) = VM.find 8280 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8280_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8279_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8279_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8282_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8282 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8281 : exists width bits, VM.find 8281 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8281_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8282 address_expr_8282 inputs path (history time) (history (S time)) early_control_data_member_8282).
 - intros site value Eval. exact (address_uint_result_8282 inputs path site flat_memories (history time) value H8281 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8282_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8282 (history t) = VM.find 8282 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8282_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8281_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8281_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8284_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8284 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8283 : exists width bits, VM.find 8283 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8283_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8284 address_expr_8284 inputs path (history time) (history (S time)) early_control_data_member_8284).
 - intros site value Eval. exact (address_uint_result_8284 inputs path site flat_memories (history time) value H8283 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8284_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8284 (history t) = VM.find 8284 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8284_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8283_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8283_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8286_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8286 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8285 : exists width bits, VM.find 8285 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8285_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8286 address_expr_8286 inputs path (history time) (history (S time)) early_control_data_member_8286).
 - intros site value Eval. exact (address_uint_result_8286 inputs path site flat_memories (history time) value H8285 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8286_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8286 (history t) = VM.find 8286 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8286_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8285_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8285_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8288_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8288 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8287 : exists width bits, VM.find 8287 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8287_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8288 address_expr_8288 inputs path (history time) (history (S time)) early_control_data_member_8288).
 - intros site value Eval. exact (address_uint_result_8288 inputs path site flat_memories (history time) value H8287 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8288_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8288 (history t) = VM.find 8288 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8288_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8287_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8287_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8290_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8290 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8289 : exists width bits, VM.find 8289 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8289_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8290 address_expr_8290 inputs path (history time) (history (S time)) early_control_data_member_8290).
 - intros site value Eval. exact (address_uint_result_8290 inputs path site flat_memories (history time) value H8289 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8290_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8290 (history t) = VM.find 8290 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8290_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8289_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8289_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8292_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8292 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8291 : exists width bits, VM.find 8291 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8291_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8292 address_expr_8292 inputs path (history time) (history (S time)) early_control_data_member_8292).
 - intros site value Eval. exact (address_uint_result_8292 inputs path site flat_memories (history time) value H8291 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8292_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8292 (history t) = VM.find 8292 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8292_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8291_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8291_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8294_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8294 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8293 : exists width bits, VM.find 8293 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8293_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8294 address_expr_8294 inputs path (history time) (history (S time)) early_control_data_member_8294).
 - intros site value Eval. exact (address_uint_result_8294 inputs path site flat_memories (history time) value H8293 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8294_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8294 (history t) = VM.find 8294 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8294_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8293_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8293_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8296_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8296 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8295 : exists width bits, VM.find 8295 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8295_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8296 address_expr_8296 inputs path (history time) (history (S time)) early_control_data_member_8296).
 - intros site value Eval. exact (address_uint_result_8296 inputs path site flat_memories (history time) value H8295 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8296_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8296 (history t) = VM.find 8296 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8296_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8295_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8295_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8298_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8298 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8297 : exists width bits, VM.find 8297 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8297_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8298 address_expr_8298 inputs path (history time) (history (S time)) early_control_data_member_8298).
 - intros site value Eval. exact (address_uint_result_8298 inputs path site flat_memories (history time) value H8297 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8298_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8298 (history t) = VM.find 8298 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8298_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8297_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8297_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8300_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8300 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8299 : exists width bits, VM.find 8299 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8299_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8300 address_expr_8300 inputs path (history time) (history (S time)) early_control_data_member_8300).
 - intros site value Eval. exact (address_uint_result_8300 inputs path site flat_memories (history time) value H8299 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8300_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8300 (history t) = VM.find 8300 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8300_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8299_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8299_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8302_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8302 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8301 : exists width bits, VM.find 8301 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8301_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8302 address_expr_8302 inputs path (history time) (history (S time)) early_control_data_member_8302).
 - intros site value Eval. exact (address_uint_result_8302 inputs path site flat_memories (history time) value H8301 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8302_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8302 (history t) = VM.find 8302 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8302_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8301_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8301_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8304_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8304 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8303 : exists width bits, VM.find 8303 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8303_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8304 address_expr_8304 inputs path (history time) (history (S time)) early_control_data_member_8304).
 - intros site value Eval. exact (address_uint_result_8304 inputs path site flat_memories (history time) value H8303 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8304_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8304 (history t) = VM.find 8304 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8304_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8303_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8303_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8306_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8306 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8305 : exists width bits, VM.find 8305 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8305_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8306 address_expr_8306 inputs path (history time) (history (S time)) early_control_data_member_8306).
 - intros site value Eval. exact (address_uint_result_8306 inputs path site flat_memories (history time) value H8305 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8306_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8306 (history t) = VM.find 8306 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8306_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8305_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8305_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8308_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8308 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8307 : exists width bits, VM.find 8307 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8307_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8308 address_expr_8308 inputs path (history time) (history (S time)) early_control_data_member_8308).
 - intros site value Eval. exact (address_uint_result_8308 inputs path site flat_memories (history time) value H8307 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8308_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8308 (history t) = VM.find 8308 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8308_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8307_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8307_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8310_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8310 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8309 : exists width bits, VM.find 8309 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8309_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8310 address_expr_8310 inputs path (history time) (history (S time)) early_control_data_member_8310).
 - intros site value Eval. exact (address_uint_result_8310 inputs path site flat_memories (history time) value H8309 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8310_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8310 (history t) = VM.find 8310 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8310_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8309_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8309_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8312_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8312 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8311 : exists width bits, VM.find 8311 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8311_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8312 address_expr_8312 inputs path (history time) (history (S time)) early_control_data_member_8312).
 - intros site value Eval. exact (address_uint_result_8312 inputs path site flat_memories (history time) value H8311 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8312_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8312 (history t) = VM.find 8312 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8312_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8311_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8311_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8314_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8314 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8313 : exists width bits, VM.find 8313 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8313_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8314 address_expr_8314 inputs path (history time) (history (S time)) early_control_data_member_8314).
 - intros site value Eval. exact (address_uint_result_8314 inputs path site flat_memories (history time) value H8313 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8314_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8314 (history t) = VM.find 8314 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8314_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8313_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8313_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8316_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8316 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8315 : exists width bits, VM.find 8315 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8315_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8316 address_expr_8316 inputs path (history time) (history (S time)) early_control_data_member_8316).
 - intros site value Eval. exact (address_uint_result_8316 inputs path site flat_memories (history time) value H8315 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8316_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8316 (history t) = VM.find 8316 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8316_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8315_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8315_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8318_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8318 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8317 : exists width bits, VM.find 8317 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8317_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8318 address_expr_8318 inputs path (history time) (history (S time)) early_control_data_member_8318).
 - intros site value Eval. exact (address_uint_result_8318 inputs path site flat_memories (history time) value H8317 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8318_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8318 (history t) = VM.find 8318 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8318_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8317_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8317_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8320_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8320 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8319 : exists width bits, VM.find 8319 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8319_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8320 address_expr_8320 inputs path (history time) (history (S time)) early_control_data_member_8320).
 - intros site value Eval. exact (address_uint_result_8320 inputs path site flat_memories (history time) value H8319 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8320_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8320 (history t) = VM.find 8320 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8320_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8319_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8319_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8322_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8322 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8321 : exists width bits, VM.find 8321 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8321_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8322 address_expr_8322 inputs path (history time) (history (S time)) early_control_data_member_8322).
 - intros site value Eval. exact (address_uint_result_8322 inputs path site flat_memories (history time) value H8321 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8322_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8322 (history t) = VM.find 8322 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8322_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8321_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8321_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8324_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8324 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8323 : exists width bits, VM.find 8323 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8323_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8324 address_expr_8324 inputs path (history time) (history (S time)) early_control_data_member_8324).
 - intros site value Eval. exact (address_uint_result_8324 inputs path site flat_memories (history time) value H8323 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8324_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8324 (history t) = VM.find 8324 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8324_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8323_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8323_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8326_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8326 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8325 : exists width bits, VM.find 8325 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8325_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8326 address_expr_8326 inputs path (history time) (history (S time)) early_control_data_member_8326).
 - intros site value Eval. exact (address_uint_result_8326 inputs path site flat_memories (history time) value H8325 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8326_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8326 (history t) = VM.find 8326 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8326_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8325_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8325_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8328_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8328 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8327 : exists width bits, VM.find 8327 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8327_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8328 address_expr_8328 inputs path (history time) (history (S time)) early_control_data_member_8328).
 - intros site value Eval. exact (address_uint_result_8328 inputs path site flat_memories (history time) value H8327 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8328_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8328 (history t) = VM.find 8328 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8328_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8327_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8327_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8330_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8330 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8329 : exists width bits, VM.find 8329 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8329_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8330 address_expr_8330 inputs path (history time) (history (S time)) early_control_data_member_8330).
 - intros site value Eval. exact (address_uint_result_8330 inputs path site flat_memories (history time) value H8329 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8330_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8330 (history t) = VM.find 8330 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8330_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8329_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8329_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8332_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8332 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8331 : exists width bits, VM.find 8331 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8331_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8332 address_expr_8332 inputs path (history time) (history (S time)) early_control_data_member_8332).
 - intros site value Eval. exact (address_uint_result_8332 inputs path site flat_memories (history time) value H8331 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8332_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8332 (history t) = VM.find 8332 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8332_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8331_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8331_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8334_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8334 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8333 : exists width bits, VM.find 8333 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8333_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8334 address_expr_8334 inputs path (history time) (history (S time)) early_control_data_member_8334).
 - intros site value Eval. exact (address_uint_result_8334 inputs path site flat_memories (history time) value H8333 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8334_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8334 (history t) = VM.find 8334 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8334_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8333_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8333_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8336_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8336 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8335 : exists width bits, VM.find 8335 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8335_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8336 address_expr_8336 inputs path (history time) (history (S time)) early_control_data_member_8336).
 - intros site value Eval. exact (address_uint_result_8336 inputs path site flat_memories (history time) value H8335 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8336_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8336 (history t) = VM.find 8336 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8336_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8335_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8335_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8338_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8338 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8337 : exists width bits, VM.find 8337 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8337_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8338 address_expr_8338 inputs path (history time) (history (S time)) early_control_data_member_8338).
 - intros site value Eval. exact (address_uint_result_8338 inputs path site flat_memories (history time) value H8337 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8338_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8338 (history t) = VM.find 8338 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8338_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8337_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8337_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8340_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8340 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8339 : exists width bits, VM.find 8339 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8339_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8340 address_expr_8340 inputs path (history time) (history (S time)) early_control_data_member_8340).
 - intros site value Eval. exact (address_uint_result_8340 inputs path site flat_memories (history time) value H8339 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8340_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8340 (history t) = VM.find 8340 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8340_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8339_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8339_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8342_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8342 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8341 : exists width bits, VM.find 8341 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8341_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8342 address_expr_8342 inputs path (history time) (history (S time)) early_control_data_member_8342).
 - intros site value Eval. exact (address_uint_result_8342 inputs path site flat_memories (history time) value H8341 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8342_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8342 (history t) = VM.find 8342 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8342_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8341_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8341_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8344_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8344 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8343 : exists width bits, VM.find 8343 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8343_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8344 address_expr_8344 inputs path (history time) (history (S time)) early_control_data_member_8344).
 - intros site value Eval. exact (address_uint_result_8344 inputs path site flat_memories (history time) value H8343 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8344_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8344 (history t) = VM.find 8344 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8344_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8343_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8343_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8346_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8346 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8345 : exists width bits, VM.find 8345 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8345_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8346 address_expr_8346 inputs path (history time) (history (S time)) early_control_data_member_8346).
 - intros site value Eval. exact (address_uint_result_8346 inputs path site flat_memories (history time) value H8345 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8346_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8346 (history t) = VM.find 8346 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8346_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8345_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8345_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8348_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8348 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8347 : exists width bits, VM.find 8347 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8347_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8348 address_expr_8348 inputs path (history time) (history (S time)) early_control_data_member_8348).
 - intros site value Eval. exact (address_uint_result_8348 inputs path site flat_memories (history time) value H8347 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8348_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8348 (history t) = VM.find 8348 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8348_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8347_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8347_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8350_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8350 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8349 : exists width bits, VM.find 8349 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8349_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8350 address_expr_8350 inputs path (history time) (history (S time)) early_control_data_member_8350).
 - intros site value Eval. exact (address_uint_result_8350 inputs path site flat_memories (history time) value H8349 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8350_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8350 (history t) = VM.find 8350 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8350_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8349_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8349_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8352_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8352 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8351 : exists width bits, VM.find 8351 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8351_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8352 address_expr_8352 inputs path (history time) (history (S time)) early_control_data_member_8352).
 - intros site value Eval. exact (address_uint_result_8352 inputs path site flat_memories (history time) value H8351 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8352_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8352 (history t) = VM.find 8352 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8352_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8351_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8351_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8354_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8354 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8353 : exists width bits, VM.find 8353 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8353_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8354 address_expr_8354 inputs path (history time) (history (S time)) early_control_data_member_8354).
 - intros site value Eval. exact (address_uint_result_8354 inputs path site flat_memories (history time) value H8353 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8354_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8354 (history t) = VM.find 8354 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8354_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8353_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8353_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8356_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8356 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8355 : exists width bits, VM.find 8355 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8355_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8356 address_expr_8356 inputs path (history time) (history (S time)) early_control_data_member_8356).
 - intros site value Eval. exact (address_uint_result_8356 inputs path site flat_memories (history time) value H8355 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8356_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8356 (history t) = VM.find 8356 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8356_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8355_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8355_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8358_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8358 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8357 : exists width bits, VM.find 8357 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8357_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8358 address_expr_8358 inputs path (history time) (history (S time)) early_control_data_member_8358).
 - intros site value Eval. exact (address_uint_result_8358 inputs path site flat_memories (history time) value H8357 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8358_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8358 (history t) = VM.find 8358 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8358_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8357_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8357_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8360_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8360 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H8359 : exists width bits, VM.find 8359 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_8359_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 8360 address_expr_8360 inputs path (history time) (history (S time)) early_control_data_member_8360).
 - intros site value Eval. exact (address_uint_result_8360 inputs path site flat_memories (history time) value H8359 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8360_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (4 <= t)%coq_nat -> (4 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8360 (history t) = VM.find 8360 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8360_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8359_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_886_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 886 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H853 : exists width bits, VM.find 853 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_853_history inputs path history limit Boundary Steps time); lia. }
 assert (H885 : exists width bits, VM.find 885 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_885_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 886 address_expr_886 inputs path (history time) (history (S time)) early_control_data_member_886).
 - intros site value Eval. exact (address_uint_result_886 inputs path site flat_memories (history time) value H780 H853 H885 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_886_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 886 (history t) = VM.find 886 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_886_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_853_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_885_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_853_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_885_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_921_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 921 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H853 : exists width bits, VM.find 853 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_853_history inputs path history limit Boundary Steps time); lia. }
 assert (H920 : exists width bits, VM.find 920 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_920_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 921 address_expr_921 inputs path (history time) (history (S time)) early_control_data_member_921).
 - intros site value Eval. exact (address_uint_result_921 inputs path site flat_memories (history time) value H781 H853 H920 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_921_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 921 (history t) = VM.find 921 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_921_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_853_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_920_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_853_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_920_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7815_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7815 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7809 : exists width bits, VM.find 7809 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7809_history inputs path history limit Boundary Steps time); lia. }
 assert (H7814 : exists width bits, VM.find 7814 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7814_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7815 address_expr_7815 inputs path (history time) (history (S time)) early_control_data_member_7815).
 - intros site value Eval. exact (address_uint_result_7815 inputs path site flat_memories (history time) value H7809 H7814 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7815_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7815 (history t) = VM.find 7815 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7815_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7809_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7814_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7809_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7814_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7818_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7818 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H7813 : exists width bits, VM.find 7813 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7813_history inputs path history limit Boundary Steps time); lia. }
 assert (H7817 : exists width bits, VM.find 7817 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7817_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7818 address_expr_7818 inputs path (history time) (history (S time)) early_control_data_member_7818).
 - intros site value Eval. exact (address_uint_result_7818 inputs path site flat_memories (history time) value H7813 H7817 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7818_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7818 (history t) = VM.find 7818 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7818_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_7813_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7817_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_7813_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7817_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8606_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8606 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8606 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8360_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8606_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8606 (history t) = VM.find 8606 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8606_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8360_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_8360_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8655_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8655 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8655 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8360_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8655_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (5 <= t)%coq_nat -> (5 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8655 (history t) = VM.find 8655 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8655_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8360_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_8360_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_887_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 887 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H854 : exists width bits, VM.find 854 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_854_history inputs path history limit Boundary Steps time); lia. }
 assert (H886 : exists width bits, VM.find 886 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_886_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 887 address_expr_887 inputs path (history time) (history (S time)) early_control_data_member_887).
 - intros site value Eval. exact (address_uint_result_887 inputs path site flat_memories (history time) value H780 H854 H886 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_887_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 887 (history t) = VM.find 887 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_887_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_854_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_886_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_854_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_886_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_922_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 922 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H854 : exists width bits, VM.find 854 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_854_history inputs path history limit Boundary Steps time); lia. }
 assert (H921 : exists width bits, VM.find 921 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_921_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 922 address_expr_922 inputs path (history time) (history (S time)) early_control_data_member_922).
 - intros site value Eval. exact (address_uint_result_922 inputs path site flat_memories (history time) value H781 H854 H921 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_922_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 922 (history t) = VM.find 922 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_922_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_854_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_921_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_854_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_921_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8607_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8607 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8607 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8358_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8606_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8607_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8607 (history t) = VM.find 8607 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8607_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8358_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8606_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8358_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8606_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8656_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8656 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8656 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8358_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8655_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8656_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (6 <= t)%coq_nat -> (6 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8656 (history t) = VM.find 8656 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8656_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8358_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8655_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8358_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8655_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_888_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 888 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H855 : exists width bits, VM.find 855 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_855_history inputs path history limit Boundary Steps time); lia. }
 assert (H887 : exists width bits, VM.find 887 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_887_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 888 address_expr_888 inputs path (history time) (history (S time)) early_control_data_member_888).
 - intros site value Eval. exact (address_uint_result_888 inputs path site flat_memories (history time) value H780 H855 H887 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_888_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (7 <= t)%coq_nat -> (7 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 888 (history t) = VM.find 888 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_888_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_855_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_887_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_855_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_887_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_923_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 923 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H855 : exists width bits, VM.find 855 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_855_history inputs path history limit Boundary Steps time); lia. }
 assert (H922 : exists width bits, VM.find 922 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_922_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 923 address_expr_923 inputs path (history time) (history (S time)) early_control_data_member_923).
 - intros site value Eval. exact (address_uint_result_923 inputs path site flat_memories (history time) value H781 H855 H922 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_923_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (7 <= t)%coq_nat -> (7 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 923 (history t) = VM.find 923 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_923_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_855_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_922_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_855_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_922_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8608_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8608 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8608 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8356_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8607_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8608_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (7 <= t)%coq_nat -> (7 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8608 (history t) = VM.find 8608 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8608_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8356_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8607_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8356_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8607_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8657_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8657 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8657 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8356_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8656_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8657_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (7 <= t)%coq_nat -> (7 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8657 (history t) = VM.find 8657 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8657_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8356_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8656_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8356_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8656_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_889_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 889 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H856 : exists width bits, VM.find 856 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_856_history inputs path history limit Boundary Steps time); lia. }
 assert (H888 : exists width bits, VM.find 888 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_888_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 889 address_expr_889 inputs path (history time) (history (S time)) early_control_data_member_889).
 - intros site value Eval. exact (address_uint_result_889 inputs path site flat_memories (history time) value H780 H856 H888 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_889_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (8 <= t)%coq_nat -> (8 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 889 (history t) = VM.find 889 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_889_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_856_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_888_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_856_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_888_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_924_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 924 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H856 : exists width bits, VM.find 856 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_856_history inputs path history limit Boundary Steps time); lia. }
 assert (H923 : exists width bits, VM.find 923 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_923_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 924 address_expr_924 inputs path (history time) (history (S time)) early_control_data_member_924).
 - intros site value Eval. exact (address_uint_result_924 inputs path site flat_memories (history time) value H781 H856 H923 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_924_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (8 <= t)%coq_nat -> (8 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 924 (history t) = VM.find 924 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_924_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_856_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_923_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_856_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_923_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8609_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8609 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8609 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8354_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8608_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8609_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (8 <= t)%coq_nat -> (8 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8609 (history t) = VM.find 8609 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8609_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8354_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8608_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8354_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8608_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8658_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8658 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8658 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8354_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8657_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8658_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (8 <= t)%coq_nat -> (8 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8658 (history t) = VM.find 8658 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8658_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8354_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8657_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8354_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8657_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_890_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 890 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H857 : exists width bits, VM.find 857 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_857_history inputs path history limit Boundary Steps time); lia. }
 assert (H889 : exists width bits, VM.find 889 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_889_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 890 address_expr_890 inputs path (history time) (history (S time)) early_control_data_member_890).
 - intros site value Eval. exact (address_uint_result_890 inputs path site flat_memories (history time) value H780 H857 H889 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_890_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (9 <= t)%coq_nat -> (9 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 890 (history t) = VM.find 890 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_890_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_857_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_889_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_857_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_889_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_925_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 925 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H857 : exists width bits, VM.find 857 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_857_history inputs path history limit Boundary Steps time); lia. }
 assert (H924 : exists width bits, VM.find 924 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_924_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 925 address_expr_925 inputs path (history time) (history (S time)) early_control_data_member_925).
 - intros site value Eval. exact (address_uint_result_925 inputs path site flat_memories (history time) value H781 H857 H924 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_925_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (9 <= t)%coq_nat -> (9 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 925 (history t) = VM.find 925 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_925_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_857_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_924_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_857_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_924_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8610_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8610 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8610 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8352_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8609_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8610_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (9 <= t)%coq_nat -> (9 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8610 (history t) = VM.find 8610 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8610_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8352_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8609_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8352_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8609_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8659_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8659 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8659 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8352_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8658_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8659_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (9 <= t)%coq_nat -> (9 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8659 (history t) = VM.find 8659 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8659_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8352_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8658_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8352_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8658_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_891_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 891 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H858 : exists width bits, VM.find 858 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_858_history inputs path history limit Boundary Steps time); lia. }
 assert (H890 : exists width bits, VM.find 890 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_890_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 891 address_expr_891 inputs path (history time) (history (S time)) early_control_data_member_891).
 - intros site value Eval. exact (address_uint_result_891 inputs path site flat_memories (history time) value H780 H858 H890 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_891_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (10 <= t)%coq_nat -> (10 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 891 (history t) = VM.find 891 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_891_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_858_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_890_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_858_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_890_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_926_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 926 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H858 : exists width bits, VM.find 858 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_858_history inputs path history limit Boundary Steps time); lia. }
 assert (H925 : exists width bits, VM.find 925 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_925_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 926 address_expr_926 inputs path (history time) (history (S time)) early_control_data_member_926).
 - intros site value Eval. exact (address_uint_result_926 inputs path site flat_memories (history time) value H781 H858 H925 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_926_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (10 <= t)%coq_nat -> (10 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 926 (history t) = VM.find 926 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_926_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_858_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_925_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_858_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_925_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8611_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8611 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8611 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8350_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8610_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8611_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (10 <= t)%coq_nat -> (10 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8611 (history t) = VM.find 8611 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8611_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8350_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8610_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8350_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8610_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8660_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8660 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8660 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8350_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8659_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8660_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (10 <= t)%coq_nat -> (10 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8660 (history t) = VM.find 8660 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8660_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8350_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8659_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8350_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8659_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_892_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 892 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H859 : exists width bits, VM.find 859 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_859_history inputs path history limit Boundary Steps time); lia. }
 assert (H891 : exists width bits, VM.find 891 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_891_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 892 address_expr_892 inputs path (history time) (history (S time)) early_control_data_member_892).
 - intros site value Eval. exact (address_uint_result_892 inputs path site flat_memories (history time) value H780 H859 H891 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_892_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (11 <= t)%coq_nat -> (11 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 892 (history t) = VM.find 892 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_892_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_859_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_891_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_859_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_891_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_927_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 927 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H859 : exists width bits, VM.find 859 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_859_history inputs path history limit Boundary Steps time); lia. }
 assert (H926 : exists width bits, VM.find 926 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_926_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 927 address_expr_927 inputs path (history time) (history (S time)) early_control_data_member_927).
 - intros site value Eval. exact (address_uint_result_927 inputs path site flat_memories (history time) value H781 H859 H926 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_927_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (11 <= t)%coq_nat -> (11 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 927 (history t) = VM.find 927 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_927_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_859_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_926_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_859_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_926_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8612_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8612 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8612 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8348_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8611_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8612_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (11 <= t)%coq_nat -> (11 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8612 (history t) = VM.find 8612 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8612_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8348_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8611_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8348_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8611_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8661_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8661 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8661 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8348_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8660_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8661_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (11 <= t)%coq_nat -> (11 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8661 (history t) = VM.find 8661 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8661_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8348_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8660_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8348_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8660_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_893_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 893 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H860 : exists width bits, VM.find 860 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_860_history inputs path history limit Boundary Steps time); lia. }
 assert (H892 : exists width bits, VM.find 892 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_892_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 893 address_expr_893 inputs path (history time) (history (S time)) early_control_data_member_893).
 - intros site value Eval. exact (address_uint_result_893 inputs path site flat_memories (history time) value H780 H860 H892 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_893_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (12 <= t)%coq_nat -> (12 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 893 (history t) = VM.find 893 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_893_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_860_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_892_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_860_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_892_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_928_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 928 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H860 : exists width bits, VM.find 860 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_860_history inputs path history limit Boundary Steps time); lia. }
 assert (H927 : exists width bits, VM.find 927 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_927_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 928 address_expr_928 inputs path (history time) (history (S time)) early_control_data_member_928).
 - intros site value Eval. exact (address_uint_result_928 inputs path site flat_memories (history time) value H781 H860 H927 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_928_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (12 <= t)%coq_nat -> (12 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 928 (history t) = VM.find 928 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_928_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_860_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_927_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_860_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_927_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8613_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8613 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8613 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8346_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8612_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8613_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (12 <= t)%coq_nat -> (12 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8613 (history t) = VM.find 8613 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8613_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8346_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8612_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8346_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8612_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8662_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8662 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8662 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8346_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8661_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8662_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (12 <= t)%coq_nat -> (12 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8662 (history t) = VM.find 8662 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8662_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8346_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8661_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8346_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8661_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_894_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 894 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H861 : exists width bits, VM.find 861 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_861_history inputs path history limit Boundary Steps time); lia. }
 assert (H893 : exists width bits, VM.find 893 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_893_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 894 address_expr_894 inputs path (history time) (history (S time)) early_control_data_member_894).
 - intros site value Eval. exact (address_uint_result_894 inputs path site flat_memories (history time) value H780 H861 H893 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_894_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (13 <= t)%coq_nat -> (13 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 894 (history t) = VM.find 894 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_894_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_861_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_893_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_861_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_893_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_929_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 929 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H861 : exists width bits, VM.find 861 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_861_history inputs path history limit Boundary Steps time); lia. }
 assert (H928 : exists width bits, VM.find 928 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_928_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 929 address_expr_929 inputs path (history time) (history (S time)) early_control_data_member_929).
 - intros site value Eval. exact (address_uint_result_929 inputs path site flat_memories (history time) value H781 H861 H928 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_929_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (13 <= t)%coq_nat -> (13 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 929 (history t) = VM.find 929 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_929_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_861_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_928_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_861_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_928_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8614_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8614 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8614 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8344_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8613_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8614_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (13 <= t)%coq_nat -> (13 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8614 (history t) = VM.find 8614 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8614_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8344_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8613_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8344_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8613_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8663_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8663 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8663 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8344_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8662_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8663_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (13 <= t)%coq_nat -> (13 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8663 (history t) = VM.find 8663 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8663_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8344_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8662_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8344_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8662_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_895_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 895 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H862 : exists width bits, VM.find 862 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_862_history inputs path history limit Boundary Steps time); lia. }
 assert (H894 : exists width bits, VM.find 894 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_894_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 895 address_expr_895 inputs path (history time) (history (S time)) early_control_data_member_895).
 - intros site value Eval. exact (address_uint_result_895 inputs path site flat_memories (history time) value H780 H862 H894 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_895_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (14 <= t)%coq_nat -> (14 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 895 (history t) = VM.find 895 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_895_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_862_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_894_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_862_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_894_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_930_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 930 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H862 : exists width bits, VM.find 862 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_862_history inputs path history limit Boundary Steps time); lia. }
 assert (H929 : exists width bits, VM.find 929 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_929_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 930 address_expr_930 inputs path (history time) (history (S time)) early_control_data_member_930).
 - intros site value Eval. exact (address_uint_result_930 inputs path site flat_memories (history time) value H781 H862 H929 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_930_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (14 <= t)%coq_nat -> (14 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 930 (history t) = VM.find 930 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_930_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_862_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_929_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_862_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_929_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8615_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8615 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8615 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8342_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8614_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8615_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (14 <= t)%coq_nat -> (14 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8615 (history t) = VM.find 8615 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8615_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8342_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8614_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8342_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8614_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8664_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8664 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8664 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8342_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8663_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8664_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (14 <= t)%coq_nat -> (14 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8664 (history t) = VM.find 8664 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8664_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8342_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8663_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8342_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8663_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_896_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 896 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H863 : exists width bits, VM.find 863 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_863_history inputs path history limit Boundary Steps time); lia. }
 assert (H895 : exists width bits, VM.find 895 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_895_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 896 address_expr_896 inputs path (history time) (history (S time)) early_control_data_member_896).
 - intros site value Eval. exact (address_uint_result_896 inputs path site flat_memories (history time) value H780 H863 H895 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_896_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (15 <= t)%coq_nat -> (15 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 896 (history t) = VM.find 896 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_896_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_863_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_895_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_863_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_895_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_931_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 931 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H863 : exists width bits, VM.find 863 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_863_history inputs path history limit Boundary Steps time); lia. }
 assert (H930 : exists width bits, VM.find 930 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_930_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 931 address_expr_931 inputs path (history time) (history (S time)) early_control_data_member_931).
 - intros site value Eval. exact (address_uint_result_931 inputs path site flat_memories (history time) value H781 H863 H930 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_931_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (15 <= t)%coq_nat -> (15 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 931 (history t) = VM.find 931 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_931_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_863_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_930_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_863_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_930_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8616_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8616 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8616 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8340_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8615_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8616_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (15 <= t)%coq_nat -> (15 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8616 (history t) = VM.find 8616 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8616_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8340_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8615_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8340_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8615_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8665_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8665 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8665 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8340_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8664_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8665_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (15 <= t)%coq_nat -> (15 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8665 (history t) = VM.find 8665 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8665_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8340_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8664_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8340_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8664_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_897_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 897 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H864 : exists width bits, VM.find 864 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_864_history inputs path history limit Boundary Steps time); lia. }
 assert (H896 : exists width bits, VM.find 896 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_896_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 897 address_expr_897 inputs path (history time) (history (S time)) early_control_data_member_897).
 - intros site value Eval. exact (address_uint_result_897 inputs path site flat_memories (history time) value H780 H864 H896 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_897_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (16 <= t)%coq_nat -> (16 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 897 (history t) = VM.find 897 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_897_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_864_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_896_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_864_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_896_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_932_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 932 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H864 : exists width bits, VM.find 864 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_864_history inputs path history limit Boundary Steps time); lia. }
 assert (H931 : exists width bits, VM.find 931 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_931_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 932 address_expr_932 inputs path (history time) (history (S time)) early_control_data_member_932).
 - intros site value Eval. exact (address_uint_result_932 inputs path site flat_memories (history time) value H781 H864 H931 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_932_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (16 <= t)%coq_nat -> (16 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 932 (history t) = VM.find 932 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_932_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_864_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_931_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_864_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_931_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8617_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8617 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8617 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8338_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8616_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8617_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (16 <= t)%coq_nat -> (16 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8617 (history t) = VM.find 8617 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8617_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8338_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8616_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8338_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8616_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8666_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8666 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8666 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8338_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8665_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8666_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (16 <= t)%coq_nat -> (16 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8666 (history t) = VM.find 8666 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8666_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8338_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8665_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8338_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8665_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_898_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 898 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H865 : exists width bits, VM.find 865 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_865_history inputs path history limit Boundary Steps time); lia. }
 assert (H897 : exists width bits, VM.find 897 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_897_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 898 address_expr_898 inputs path (history time) (history (S time)) early_control_data_member_898).
 - intros site value Eval. exact (address_uint_result_898 inputs path site flat_memories (history time) value H780 H865 H897 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_898_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (17 <= t)%coq_nat -> (17 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 898 (history t) = VM.find 898 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_898_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_865_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_897_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_865_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_897_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_933_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 933 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H865 : exists width bits, VM.find 865 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_865_history inputs path history limit Boundary Steps time); lia. }
 assert (H932 : exists width bits, VM.find 932 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_932_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 933 address_expr_933 inputs path (history time) (history (S time)) early_control_data_member_933).
 - intros site value Eval. exact (address_uint_result_933 inputs path site flat_memories (history time) value H781 H865 H932 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_933_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (17 <= t)%coq_nat -> (17 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 933 (history t) = VM.find 933 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_933_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_865_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_932_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_865_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_932_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8618_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8618 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8618 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8336_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8617_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8618_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (17 <= t)%coq_nat -> (17 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8618 (history t) = VM.find 8618 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8618_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8336_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8617_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8336_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8617_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8667_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8667 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8667 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8336_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8666_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8667_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (17 <= t)%coq_nat -> (17 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8667 (history t) = VM.find 8667 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8667_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8336_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8666_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8336_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8666_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_899_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 899 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H866 : exists width bits, VM.find 866 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_866_history inputs path history limit Boundary Steps time); lia. }
 assert (H898 : exists width bits, VM.find 898 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_898_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 899 address_expr_899 inputs path (history time) (history (S time)) early_control_data_member_899).
 - intros site value Eval. exact (address_uint_result_899 inputs path site flat_memories (history time) value H780 H866 H898 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_899_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (18 <= t)%coq_nat -> (18 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 899 (history t) = VM.find 899 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_899_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_866_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_898_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_866_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_898_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_934_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 934 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H866 : exists width bits, VM.find 866 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_866_history inputs path history limit Boundary Steps time); lia. }
 assert (H933 : exists width bits, VM.find 933 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_933_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 934 address_expr_934 inputs path (history time) (history (S time)) early_control_data_member_934).
 - intros site value Eval. exact (address_uint_result_934 inputs path site flat_memories (history time) value H781 H866 H933 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_934_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (18 <= t)%coq_nat -> (18 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 934 (history t) = VM.find 934 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_934_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_866_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_933_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_866_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_933_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8619_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8619 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8619 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8334_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8618_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8619_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (18 <= t)%coq_nat -> (18 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8619 (history t) = VM.find 8619 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8619_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8334_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8618_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8334_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8618_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8668_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8668 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8668 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8334_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8667_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8668_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (18 <= t)%coq_nat -> (18 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8668 (history t) = VM.find 8668 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8668_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8334_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8667_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8334_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8667_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_900_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 900 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H867 : exists width bits, VM.find 867 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_867_history inputs path history limit Boundary Steps time); lia. }
 assert (H899 : exists width bits, VM.find 899 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_899_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 900 address_expr_900 inputs path (history time) (history (S time)) early_control_data_member_900).
 - intros site value Eval. exact (address_uint_result_900 inputs path site flat_memories (history time) value H780 H867 H899 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_900_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (19 <= t)%coq_nat -> (19 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 900 (history t) = VM.find 900 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_900_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_867_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_899_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_867_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_899_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_935_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 935 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H867 : exists width bits, VM.find 867 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_867_history inputs path history limit Boundary Steps time); lia. }
 assert (H934 : exists width bits, VM.find 934 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_934_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 935 address_expr_935 inputs path (history time) (history (S time)) early_control_data_member_935).
 - intros site value Eval. exact (address_uint_result_935 inputs path site flat_memories (history time) value H781 H867 H934 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_935_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (19 <= t)%coq_nat -> (19 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 935 (history t) = VM.find 935 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_935_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_867_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_934_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_867_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_934_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8620_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8620 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8620 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8332_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8619_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8620_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (19 <= t)%coq_nat -> (19 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8620 (history t) = VM.find 8620 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8620_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8332_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8619_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8332_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8619_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8669_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8669 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8669 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8332_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8668_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8669_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (19 <= t)%coq_nat -> (19 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8669 (history t) = VM.find 8669 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8669_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8332_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8668_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8332_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8668_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_901_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 901 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H868 : exists width bits, VM.find 868 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_868_history inputs path history limit Boundary Steps time); lia. }
 assert (H900 : exists width bits, VM.find 900 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_900_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 901 address_expr_901 inputs path (history time) (history (S time)) early_control_data_member_901).
 - intros site value Eval. exact (address_uint_result_901 inputs path site flat_memories (history time) value H780 H868 H900 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_901_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (20 <= t)%coq_nat -> (20 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 901 (history t) = VM.find 901 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_901_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_868_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_900_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_868_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_900_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_936_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 936 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H868 : exists width bits, VM.find 868 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_868_history inputs path history limit Boundary Steps time); lia. }
 assert (H935 : exists width bits, VM.find 935 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_935_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 936 address_expr_936 inputs path (history time) (history (S time)) early_control_data_member_936).
 - intros site value Eval. exact (address_uint_result_936 inputs path site flat_memories (history time) value H781 H868 H935 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_936_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (20 <= t)%coq_nat -> (20 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 936 (history t) = VM.find 936 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_936_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_868_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_935_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_868_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_935_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8621_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8621 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8621 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8330_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8620_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8621_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (20 <= t)%coq_nat -> (20 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8621 (history t) = VM.find 8621 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8621_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8330_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8620_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8330_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8620_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8670_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8670 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8670 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8330_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8669_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8670_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (20 <= t)%coq_nat -> (20 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8670 (history t) = VM.find 8670 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8670_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8330_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8669_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8330_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8669_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_902_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 902 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H869 : exists width bits, VM.find 869 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_869_history inputs path history limit Boundary Steps time); lia. }
 assert (H901 : exists width bits, VM.find 901 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_901_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 902 address_expr_902 inputs path (history time) (history (S time)) early_control_data_member_902).
 - intros site value Eval. exact (address_uint_result_902 inputs path site flat_memories (history time) value H780 H869 H901 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_902_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (21 <= t)%coq_nat -> (21 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 902 (history t) = VM.find 902 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_902_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_869_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_901_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_869_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_901_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_937_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 937 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H869 : exists width bits, VM.find 869 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_869_history inputs path history limit Boundary Steps time); lia. }
 assert (H936 : exists width bits, VM.find 936 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_936_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 937 address_expr_937 inputs path (history time) (history (S time)) early_control_data_member_937).
 - intros site value Eval. exact (address_uint_result_937 inputs path site flat_memories (history time) value H781 H869 H936 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_937_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (21 <= t)%coq_nat -> (21 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 937 (history t) = VM.find 937 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_937_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_869_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_936_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_869_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_936_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8622_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8622 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8622 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8328_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8621_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8622_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (21 <= t)%coq_nat -> (21 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8622 (history t) = VM.find 8622 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8622_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8328_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8621_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8328_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8621_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8671_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8671 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8671 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8328_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8670_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8671_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (21 <= t)%coq_nat -> (21 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8671 (history t) = VM.find 8671 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8671_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8328_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8670_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8328_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8670_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_903_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 903 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H870 : exists width bits, VM.find 870 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_870_history inputs path history limit Boundary Steps time); lia. }
 assert (H902 : exists width bits, VM.find 902 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_902_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 903 address_expr_903 inputs path (history time) (history (S time)) early_control_data_member_903).
 - intros site value Eval. exact (address_uint_result_903 inputs path site flat_memories (history time) value H780 H870 H902 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_903_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (22 <= t)%coq_nat -> (22 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 903 (history t) = VM.find 903 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_903_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_870_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_902_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_870_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_902_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_938_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 938 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H870 : exists width bits, VM.find 870 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_870_history inputs path history limit Boundary Steps time); lia. }
 assert (H937 : exists width bits, VM.find 937 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_937_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 938 address_expr_938 inputs path (history time) (history (S time)) early_control_data_member_938).
 - intros site value Eval. exact (address_uint_result_938 inputs path site flat_memories (history time) value H781 H870 H937 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_938_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (22 <= t)%coq_nat -> (22 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 938 (history t) = VM.find 938 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_938_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_870_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_937_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_870_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_937_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8623_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8623 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8623 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8326_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8622_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8623_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (22 <= t)%coq_nat -> (22 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8623 (history t) = VM.find 8623 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8623_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8326_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8622_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8326_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8622_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8672_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8672 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8672 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8326_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8671_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8672_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (22 <= t)%coq_nat -> (22 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8672 (history t) = VM.find 8672 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8672_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8326_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8671_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8326_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8671_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_904_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 904 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H871 : exists width bits, VM.find 871 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_871_history inputs path history limit Boundary Steps time); lia. }
 assert (H903 : exists width bits, VM.find 903 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_903_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 904 address_expr_904 inputs path (history time) (history (S time)) early_control_data_member_904).
 - intros site value Eval. exact (address_uint_result_904 inputs path site flat_memories (history time) value H780 H871 H903 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_904_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (23 <= t)%coq_nat -> (23 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 904 (history t) = VM.find 904 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_904_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_871_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_903_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_871_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_903_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_939_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 939 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H871 : exists width bits, VM.find 871 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_871_history inputs path history limit Boundary Steps time); lia. }
 assert (H938 : exists width bits, VM.find 938 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_938_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 939 address_expr_939 inputs path (history time) (history (S time)) early_control_data_member_939).
 - intros site value Eval. exact (address_uint_result_939 inputs path site flat_memories (history time) value H781 H871 H938 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_939_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (23 <= t)%coq_nat -> (23 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 939 (history t) = VM.find 939 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_939_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_871_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_938_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_871_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_938_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8624_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8624 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8624 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8324_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8623_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8624_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (23 <= t)%coq_nat -> (23 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8624 (history t) = VM.find 8624 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8624_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8324_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8623_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8324_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8623_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8673_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8673 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8673 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8324_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8672_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8673_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (23 <= t)%coq_nat -> (23 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8673 (history t) = VM.find 8673 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8673_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8324_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8672_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8324_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8672_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_905_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 905 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H872 : exists width bits, VM.find 872 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_872_history inputs path history limit Boundary Steps time); lia. }
 assert (H904 : exists width bits, VM.find 904 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_904_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 905 address_expr_905 inputs path (history time) (history (S time)) early_control_data_member_905).
 - intros site value Eval. exact (address_uint_result_905 inputs path site flat_memories (history time) value H780 H872 H904 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_905_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (24 <= t)%coq_nat -> (24 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 905 (history t) = VM.find 905 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_905_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_872_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_904_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_872_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_904_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_940_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 940 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H872 : exists width bits, VM.find 872 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_872_history inputs path history limit Boundary Steps time); lia. }
 assert (H939 : exists width bits, VM.find 939 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_939_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 940 address_expr_940 inputs path (history time) (history (S time)) early_control_data_member_940).
 - intros site value Eval. exact (address_uint_result_940 inputs path site flat_memories (history time) value H781 H872 H939 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_940_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (24 <= t)%coq_nat -> (24 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 940 (history t) = VM.find 940 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_940_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_872_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_939_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_872_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_939_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8625_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8625 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8625 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8322_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8624_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8625_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (24 <= t)%coq_nat -> (24 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8625 (history t) = VM.find 8625 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8625_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8322_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8624_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8322_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8624_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8674_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8674 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8674 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8322_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8673_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8674_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (24 <= t)%coq_nat -> (24 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8674 (history t) = VM.find 8674 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8674_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8322_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8673_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8322_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8673_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_906_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 906 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H873 : exists width bits, VM.find 873 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_873_history inputs path history limit Boundary Steps time); lia. }
 assert (H905 : exists width bits, VM.find 905 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_905_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 906 address_expr_906 inputs path (history time) (history (S time)) early_control_data_member_906).
 - intros site value Eval. exact (address_uint_result_906 inputs path site flat_memories (history time) value H780 H873 H905 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_906_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (25 <= t)%coq_nat -> (25 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 906 (history t) = VM.find 906 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_906_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_873_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_905_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_873_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_905_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_941_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 941 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H873 : exists width bits, VM.find 873 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_873_history inputs path history limit Boundary Steps time); lia. }
 assert (H940 : exists width bits, VM.find 940 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_940_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 941 address_expr_941 inputs path (history time) (history (S time)) early_control_data_member_941).
 - intros site value Eval. exact (address_uint_result_941 inputs path site flat_memories (history time) value H781 H873 H940 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_941_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (25 <= t)%coq_nat -> (25 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 941 (history t) = VM.find 941 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_941_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_873_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_940_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_873_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_940_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8626_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8626 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8626 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8320_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8625_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8626_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (25 <= t)%coq_nat -> (25 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8626 (history t) = VM.find 8626 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8626_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8320_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8625_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8320_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8625_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8675_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8675 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8675 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8320_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8674_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8675_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (25 <= t)%coq_nat -> (25 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8675 (history t) = VM.find 8675 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8675_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8320_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8674_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8320_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8674_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_907_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 907 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H874 : exists width bits, VM.find 874 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_874_history inputs path history limit Boundary Steps time); lia. }
 assert (H906 : exists width bits, VM.find 906 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_906_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 907 address_expr_907 inputs path (history time) (history (S time)) early_control_data_member_907).
 - intros site value Eval. exact (address_uint_result_907 inputs path site flat_memories (history time) value H780 H874 H906 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_907_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (26 <= t)%coq_nat -> (26 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 907 (history t) = VM.find 907 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_907_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_874_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_906_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_874_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_906_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_942_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 942 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H874 : exists width bits, VM.find 874 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_874_history inputs path history limit Boundary Steps time); lia. }
 assert (H941 : exists width bits, VM.find 941 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_941_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 942 address_expr_942 inputs path (history time) (history (S time)) early_control_data_member_942).
 - intros site value Eval. exact (address_uint_result_942 inputs path site flat_memories (history time) value H781 H874 H941 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_942_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (26 <= t)%coq_nat -> (26 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 942 (history t) = VM.find 942 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_942_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_874_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_941_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_874_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_941_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8627_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8627 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8627 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8318_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8626_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8627_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (26 <= t)%coq_nat -> (26 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8627 (history t) = VM.find 8627 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8627_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8318_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8626_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8318_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8626_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8676_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8676 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8676 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8318_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8675_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8676_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (26 <= t)%coq_nat -> (26 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8676 (history t) = VM.find 8676 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8676_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8318_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8675_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8318_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8675_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_908_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 908 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H875 : exists width bits, VM.find 875 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_875_history inputs path history limit Boundary Steps time); lia. }
 assert (H907 : exists width bits, VM.find 907 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_907_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 908 address_expr_908 inputs path (history time) (history (S time)) early_control_data_member_908).
 - intros site value Eval. exact (address_uint_result_908 inputs path site flat_memories (history time) value H780 H875 H907 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_908_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (27 <= t)%coq_nat -> (27 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 908 (history t) = VM.find 908 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_908_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_875_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_907_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_875_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_907_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_943_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 943 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H875 : exists width bits, VM.find 875 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_875_history inputs path history limit Boundary Steps time); lia. }
 assert (H942 : exists width bits, VM.find 942 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_942_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 943 address_expr_943 inputs path (history time) (history (S time)) early_control_data_member_943).
 - intros site value Eval. exact (address_uint_result_943 inputs path site flat_memories (history time) value H781 H875 H942 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_943_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (27 <= t)%coq_nat -> (27 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 943 (history t) = VM.find 943 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_943_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_875_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_942_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_875_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_942_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8628_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8628 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8628 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8316_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8627_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8628_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (27 <= t)%coq_nat -> (27 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8628 (history t) = VM.find 8628 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8628_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8316_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8627_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8316_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8627_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8677_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8677 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8677 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8316_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8676_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8677_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (27 <= t)%coq_nat -> (27 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8677 (history t) = VM.find 8677 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8677_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8316_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8676_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8316_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8676_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_909_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 909 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H876 : exists width bits, VM.find 876 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_876_history inputs path history limit Boundary Steps time); lia. }
 assert (H908 : exists width bits, VM.find 908 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_908_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 909 address_expr_909 inputs path (history time) (history (S time)) early_control_data_member_909).
 - intros site value Eval. exact (address_uint_result_909 inputs path site flat_memories (history time) value H780 H876 H908 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_909_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (28 <= t)%coq_nat -> (28 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 909 (history t) = VM.find 909 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_909_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_876_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_908_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_876_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_908_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_944_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 944 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H876 : exists width bits, VM.find 876 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_876_history inputs path history limit Boundary Steps time); lia. }
 assert (H943 : exists width bits, VM.find 943 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_943_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 944 address_expr_944 inputs path (history time) (history (S time)) early_control_data_member_944).
 - intros site value Eval. exact (address_uint_result_944 inputs path site flat_memories (history time) value H781 H876 H943 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_944_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (28 <= t)%coq_nat -> (28 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 944 (history t) = VM.find 944 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_944_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_876_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_943_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_876_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_943_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8629_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8629 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8629 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8314_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8628_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8629_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (28 <= t)%coq_nat -> (28 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8629 (history t) = VM.find 8629 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8629_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8314_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8628_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8314_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8628_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8678_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8678 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8678 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8314_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8677_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8678_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (28 <= t)%coq_nat -> (28 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8678 (history t) = VM.find 8678 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8678_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8314_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8677_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8314_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8677_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_910_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 910 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H877 : exists width bits, VM.find 877 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_877_history inputs path history limit Boundary Steps time); lia. }
 assert (H909 : exists width bits, VM.find 909 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_909_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 910 address_expr_910 inputs path (history time) (history (S time)) early_control_data_member_910).
 - intros site value Eval. exact (address_uint_result_910 inputs path site flat_memories (history time) value H780 H877 H909 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_910_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (29 <= t)%coq_nat -> (29 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 910 (history t) = VM.find 910 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_910_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_877_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_909_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_877_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_909_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_945_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 945 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H877 : exists width bits, VM.find 877 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_877_history inputs path history limit Boundary Steps time); lia. }
 assert (H944 : exists width bits, VM.find 944 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_944_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 945 address_expr_945 inputs path (history time) (history (S time)) early_control_data_member_945).
 - intros site value Eval. exact (address_uint_result_945 inputs path site flat_memories (history time) value H781 H877 H944 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_945_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (29 <= t)%coq_nat -> (29 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 945 (history t) = VM.find 945 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_945_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_877_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_944_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_877_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_944_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8630_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8630 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8630 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8312_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8629_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8630_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (29 <= t)%coq_nat -> (29 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8630 (history t) = VM.find 8630 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8630_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8312_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8629_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8312_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8629_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8679_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8679 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8679 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8312_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8678_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8679_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (29 <= t)%coq_nat -> (29 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8679 (history t) = VM.find 8679 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8679_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8312_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8678_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8312_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8678_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_911_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 911 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H878 : exists width bits, VM.find 878 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_878_history inputs path history limit Boundary Steps time); lia. }
 assert (H910 : exists width bits, VM.find 910 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_910_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 911 address_expr_911 inputs path (history time) (history (S time)) early_control_data_member_911).
 - intros site value Eval. exact (address_uint_result_911 inputs path site flat_memories (history time) value H780 H878 H910 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_911_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (30 <= t)%coq_nat -> (30 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 911 (history t) = VM.find 911 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_911_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_878_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_910_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_878_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_910_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_946_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 946 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H878 : exists width bits, VM.find 878 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_878_history inputs path history limit Boundary Steps time); lia. }
 assert (H945 : exists width bits, VM.find 945 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_945_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 946 address_expr_946 inputs path (history time) (history (S time)) early_control_data_member_946).
 - intros site value Eval. exact (address_uint_result_946 inputs path site flat_memories (history time) value H781 H878 H945 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_946_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (30 <= t)%coq_nat -> (30 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 946 (history t) = VM.find 946 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_946_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_878_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_945_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_878_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_945_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8631_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8631 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8631 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8310_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8630_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8631_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (30 <= t)%coq_nat -> (30 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8631 (history t) = VM.find 8631 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8631_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8310_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8630_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8310_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8630_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8680_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8680 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8680 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8310_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8679_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8680_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (30 <= t)%coq_nat -> (30 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8680 (history t) = VM.find 8680 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8680_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8310_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8679_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8310_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8679_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_912_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 912 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H879 : exists width bits, VM.find 879 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_879_history inputs path history limit Boundary Steps time); lia. }
 assert (H911 : exists width bits, VM.find 911 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_911_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 912 address_expr_912 inputs path (history time) (history (S time)) early_control_data_member_912).
 - intros site value Eval. exact (address_uint_result_912 inputs path site flat_memories (history time) value H780 H879 H911 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_912_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (31 <= t)%coq_nat -> (31 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 912 (history t) = VM.find 912 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_912_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_879_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_911_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_879_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_911_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_947_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 947 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H879 : exists width bits, VM.find 879 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_879_history inputs path history limit Boundary Steps time); lia. }
 assert (H946 : exists width bits, VM.find 946 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_946_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 947 address_expr_947 inputs path (history time) (history (S time)) early_control_data_member_947).
 - intros site value Eval. exact (address_uint_result_947 inputs path site flat_memories (history time) value H781 H879 H946 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_947_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (31 <= t)%coq_nat -> (31 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 947 (history t) = VM.find 947 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_947_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_879_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_946_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_879_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_946_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8632_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8632 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8632 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8308_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8631_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8632_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (31 <= t)%coq_nat -> (31 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8632 (history t) = VM.find 8632 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8632_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8308_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8631_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8308_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8631_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8681_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8681 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8681 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8308_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8680_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8681_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (31 <= t)%coq_nat -> (31 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8681 (history t) = VM.find 8681 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8681_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8308_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8680_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8308_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8680_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_913_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 913 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H880 : exists width bits, VM.find 880 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_880_history inputs path history limit Boundary Steps time); lia. }
 assert (H912 : exists width bits, VM.find 912 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_912_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 913 address_expr_913 inputs path (history time) (history (S time)) early_control_data_member_913).
 - intros site value Eval. exact (address_uint_result_913 inputs path site flat_memories (history time) value H780 H880 H912 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_913_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (32 <= t)%coq_nat -> (32 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 913 (history t) = VM.find 913 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_913_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_880_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_912_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_880_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_912_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_948_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 948 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H880 : exists width bits, VM.find 880 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_880_history inputs path history limit Boundary Steps time); lia. }
 assert (H947 : exists width bits, VM.find 947 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_947_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 948 address_expr_948 inputs path (history time) (history (S time)) early_control_data_member_948).
 - intros site value Eval. exact (address_uint_result_948 inputs path site flat_memories (history time) value H781 H880 H947 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_948_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (32 <= t)%coq_nat -> (32 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 948 (history t) = VM.find 948 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_948_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_880_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_947_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_880_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_947_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8633_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8633 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8633 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8306_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8632_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8633_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (32 <= t)%coq_nat -> (32 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8633 (history t) = VM.find 8633 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8633_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8306_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8632_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8306_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8632_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8682_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8682 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8682 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8306_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8681_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8682_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (32 <= t)%coq_nat -> (32 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8682 (history t) = VM.find 8682 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8682_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8306_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8681_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8306_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8681_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_914_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 914 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H881 : exists width bits, VM.find 881 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_881_history inputs path history limit Boundary Steps time); lia. }
 assert (H913 : exists width bits, VM.find 913 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_913_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 914 address_expr_914 inputs path (history time) (history (S time)) early_control_data_member_914).
 - intros site value Eval. exact (address_uint_result_914 inputs path site flat_memories (history time) value H780 H881 H913 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_914_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (33 <= t)%coq_nat -> (33 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 914 (history t) = VM.find 914 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_914_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_881_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_913_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_881_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_913_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_949_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 949 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H881 : exists width bits, VM.find 881 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_881_history inputs path history limit Boundary Steps time); lia. }
 assert (H948 : exists width bits, VM.find 948 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_948_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 949 address_expr_949 inputs path (history time) (history (S time)) early_control_data_member_949).
 - intros site value Eval. exact (address_uint_result_949 inputs path site flat_memories (history time) value H781 H881 H948 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_949_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (33 <= t)%coq_nat -> (33 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 949 (history t) = VM.find 949 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_949_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_881_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_948_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_881_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_948_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8634_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8634 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8634 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8304_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8633_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8634_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (33 <= t)%coq_nat -> (33 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8634 (history t) = VM.find 8634 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8634_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8304_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8633_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8304_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8633_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8683_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8683 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8683 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8304_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8682_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8683_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (33 <= t)%coq_nat -> (33 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8683 (history t) = VM.find 8683 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8683_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8304_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8682_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8304_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8682_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_915_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 915 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H780 : exists width bits, VM.find 780 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_780_history inputs path history limit Boundary Steps time); lia. }
 assert (H882 : exists width bits, VM.find 882 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_882_history inputs path history limit Boundary Steps time); lia. }
 assert (H914 : exists width bits, VM.find 914 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_914_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 915 address_expr_915 inputs path (history time) (history (S time)) early_control_data_member_915).
 - intros site value Eval. exact (address_uint_result_915 inputs path site flat_memories (history time) value H780 H882 H914 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_915_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (34 <= t)%coq_nat -> (34 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 915 (history t) = VM.find 915 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_915_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_780_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_882_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_914_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_780_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_882_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_914_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_950_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 950 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H781 : exists width bits, VM.find 781 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_781_history inputs path history limit Boundary Steps time); lia. }
 assert (H882 : exists width bits, VM.find 882 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_882_history inputs path history limit Boundary Steps time); lia. }
 assert (H949 : exists width bits, VM.find 949 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_949_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 950 address_expr_950 inputs path (history time) (history (S time)) early_control_data_member_950).
 - intros site value Eval. exact (address_uint_result_950 inputs path site flat_memories (history time) value H781 H882 H949 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_950_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (34 <= t)%coq_nat -> (34 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 950 (history t) = VM.find 950 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_950_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_781_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_882_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_949_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_781_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_882_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_949_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8635_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8635 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8635 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8302_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8634_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8635_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (34 <= t)%coq_nat -> (34 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8635 (history t) = VM.find 8635 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8635_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8302_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8634_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8302_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8634_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8684_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8684 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8684 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8302_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8683_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8684_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (34 <= t)%coq_nat -> (34 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8684 (history t) = VM.find 8684 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8684_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8302_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8683_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8302_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8683_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_916_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 916 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H915 : exists width bits, VM.find 915 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_915_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 916 address_expr_916 inputs path (history time) (history (S time)) early_control_data_member_916).
 - intros site value Eval. exact (address_uint_result_916 inputs path site flat_memories (history time) value H915 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_916_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (35 <= t)%coq_nat -> (35 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 916 (history t) = VM.find 916 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_916_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_915_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_915_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_951_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 951 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H950 : exists width bits, VM.find 950 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_950_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 951 address_expr_951 inputs path (history time) (history (S time)) early_control_data_member_951).
 - intros site value Eval. exact (address_uint_result_951 inputs path site flat_memories (history time) value H950 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_951_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (35 <= t)%coq_nat -> (35 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 951 (history t) = VM.find 951 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_951_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_950_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_950_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8636_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8636 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8636 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8300_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8635_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8636_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (35 <= t)%coq_nat -> (35 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8636 (history t) = VM.find 8636 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8636_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8300_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8635_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8300_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8635_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8685_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8685 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8685 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8300_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8684_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8685_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (35 <= t)%coq_nat -> (35 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8685 (history t) = VM.find 8685 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8685_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8300_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8684_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8300_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8684_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_917_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 917 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H883 : exists width bits, VM.find 883 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_883_history inputs path history limit Boundary Steps time); lia. }
 assert (H916 : exists width bits, VM.find 916 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_916_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 917 address_expr_917 inputs path (history time) (history (S time)) early_control_data_member_917).
 - intros site value Eval. exact (address_uint_result_917 inputs path site flat_memories (history time) value H883 H916 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_917_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (36 <= t)%coq_nat -> (36 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 917 (history t) = VM.find 917 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_917_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_883_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_916_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_883_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_916_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_952_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 952 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H918 : exists width bits, VM.find 918 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_918_history inputs path history limit Boundary Steps time); lia. }
 assert (H951 : exists width bits, VM.find 951 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_951_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 952 address_expr_952 inputs path (history time) (history (S time)) early_control_data_member_952).
 - intros site value Eval. exact (address_uint_result_952 inputs path site flat_memories (history time) value H918 H951 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_952_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (36 <= t)%coq_nat -> (36 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 952 (history t) = VM.find 952 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_952_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_918_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_951_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_918_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_951_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8637_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8637 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8637 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8298_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8636_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8637_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (36 <= t)%coq_nat -> (36 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8637 (history t) = VM.find 8637 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8637_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8298_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8636_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8298_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8636_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8686_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8686 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8686 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8298_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8685_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8686_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (36 <= t)%coq_nat -> (36 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8686 (history t) = VM.find 8686 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8686_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8298_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8685_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8298_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8685_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_782_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 782 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_782_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_917_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 32%nat, bits. exact Value.
Qed.
Theorem early_control_stable_782_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (37 <= t)%coq_nat -> (37 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 782 (history t) = VM.find 782 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_782_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_917_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_783_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 783 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_783_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_952_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 32%nat, bits. exact Value.
Qed.
Theorem early_control_stable_783_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (37 <= t)%coq_nat -> (37 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 783 (history t) = VM.find 783 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_783_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_952_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8638_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8638 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8638 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8296_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8637_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8638_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (37 <= t)%coq_nat -> (37 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8638 (history t) = VM.find 8638 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8638_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8296_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8637_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8296_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8637_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8687_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8687 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8687 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8296_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8686_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8687_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (37 <= t)%coq_nat -> (37 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8687 (history t) = VM.find 8687 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8687_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8296_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8686_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8296_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8686_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7816_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7816 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H782 : exists width bits, VM.find 782 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_782_history inputs path history limit Boundary Steps time); lia. }
 assert (H7752 : exists width bits, VM.find 7752 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7752_history inputs path history limit Boundary Steps time); lia. }
 assert (H7815 : exists width bits, VM.find 7815 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7815_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7816 address_expr_7816 inputs path (history time) (history (S time)) early_control_data_member_7816).
 - intros site value Eval. exact (address_uint_result_7816 inputs path site flat_memories (history time) value H782 H7752 H7815 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7816_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (38 <= t)%coq_nat -> (38 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7816 (history t) = VM.find 7816 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7816_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_782_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7752_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7815_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_782_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7752_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7815_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_7819_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 7819 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 assert (H783 : exists width bits, VM.find 783 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_783_history inputs path history limit Boundary Steps time); lia. }
 assert (H7752 : exists width bits, VM.find 7752 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7752_history inputs path history limit Boundary Steps time); lia. }
 assert (H7818 : exists width bits, VM.find 7818 (history time) = Some (Gval (Fuint width) bits)).
 { apply (early_control_concrete_7818_history inputs path history limit Boundary Steps time); lia. }
 apply (early_control_data_uint_output 7819 address_expr_7819 inputs path (history time) (history (S time)) early_control_data_member_7819).
 - intros site value Eval. exact (address_uint_result_7819 inputs path site flat_memories (history time) value H783 H7752 H7818 Eval).
 - apply Steps. lia.
Qed.
Theorem early_control_stable_7819_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (38 <= t)%coq_nat -> (38 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7819 (history t) = VM.find 7819 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_7819_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_783_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7752_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_7818_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_783_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7752_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_7818_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8639_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8639 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8639 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8294_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8638_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8639_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (38 <= t)%coq_nat -> (38 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8639 (history t) = VM.find 8639 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8639_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8294_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8638_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8294_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8638_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8688_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8688 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8688 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8294_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8687_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8688_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (38 <= t)%coq_nat -> (38 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8688 (history t) = VM.find 8688 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8688_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8294_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8687_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8294_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8687_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1357_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 1357 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_1357_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_7816_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 32%nat, bits. exact Value.
Qed.
Theorem early_control_stable_1357_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (39 <= t)%coq_nat -> (39 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1357 (history t) = VM.find 1357 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_1357_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_7816_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1358_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 1358 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_1358_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_7819_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 32%nat, bits. exact Value.
Qed.
Theorem early_control_stable_1358_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (39 <= t)%coq_nat -> (39 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1358 (history t) = VM.find 1358 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_1358_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_7819_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8640_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8640 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8640 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8292_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8639_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8640_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (39 <= t)%coq_nat -> (39 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8640 (history t) = VM.find 8640 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8640_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8292_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8639_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8292_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8639_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8689_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8689 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8689 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8292_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8688_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8689_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (39 <= t)%coq_nat -> (39 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8689 (history t) = VM.find 8689 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8689_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8292_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8688_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8292_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8688_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1361_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1361 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1361 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1357_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - destruct (early_control_concrete_1358_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1361_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1361 (history t) = VM.find 1361 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1361_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1357_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - destruct (early_control_concrete_1358_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1357_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1358_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1365_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1365 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1365 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1357_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1365_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1365 (history t) = VM.find 1365 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1365_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1357_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1357_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1366_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1366 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1366 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1358_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1366_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1366 (history t) = VM.find 1366 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1366_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1358_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1358_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1369_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1369 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1369 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1357_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1369_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1369 (history t) = VM.find 1369 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1369_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1357_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1357_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1372_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1372 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1372 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1358_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1372_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1372 (history t) = VM.find 1372 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1372_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1358_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1358_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8641_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8641 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8641 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8290_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8640_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8641_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8641 (history t) = VM.find 8641 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8641_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8290_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8640_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8290_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8640_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8690_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8690 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8690 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8290_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8689_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8690_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (40 <= t)%coq_nat -> (40 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8690 (history t) = VM.find 8690 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8690_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8290_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8689_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8290_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8689_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1362_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1362 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1362 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1361_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1362_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (41 <= t)%coq_nat -> (41 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1362 (history t) = VM.find 1362 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1362_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1361_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1361_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1367_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1367 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1367 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1365_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1366_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1367_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (41 <= t)%coq_nat -> (41 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1367 (history t) = VM.find 1367 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1367_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1365_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1366_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1365_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1366_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8642_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8642 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8642 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8288_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8641_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8642_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (41 <= t)%coq_nat -> (41 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8642 (history t) = VM.find 8642 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8642_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8288_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8641_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8288_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8641_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8691_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8691 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8691 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8288_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8690_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8691_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (41 <= t)%coq_nat -> (41 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8691 (history t) = VM.find 8691 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8691_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8288_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8690_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8288_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8690_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1363_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1363 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1363 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1362_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1363_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (42 <= t)%coq_nat -> (42 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1363 (history t) = VM.find 1363 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1363_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1362_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1362_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1368_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1368 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1368 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1362_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1368_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (42 <= t)%coq_nat -> (42 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1368 (history t) = VM.find 1368 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1368_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1362_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1362_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1371_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1371 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1371 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1362_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1371_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (42 <= t)%coq_nat -> (42 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1371 (history t) = VM.find 1371 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1371_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1362_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1362_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8643_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8643 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8643 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8286_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8642_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8643_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (42 <= t)%coq_nat -> (42 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8643 (history t) = VM.find 8643 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8643_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8286_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8642_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8286_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8642_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8692_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8692 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8692 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8286_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8691_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8692_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (42 <= t)%coq_nat -> (42 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8692 (history t) = VM.find 8692 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8692_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8286_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8691_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8286_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8691_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1364_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1364 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1364 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1363_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1364_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (43 <= t)%coq_nat -> (43 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1364 (history t) = VM.find 1364 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1364_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1363_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1363_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1370_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1370 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1370 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1367_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1368_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1369_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1370_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (43 <= t)%coq_nat -> (43 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1370 (history t) = VM.find 1370 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1370_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1367_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1368_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1369_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1367_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1368_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1369_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1373_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1373 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1373 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1367_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1371_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1372_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1373_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (43 <= t)%coq_nat -> (43 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1373 (history t) = VM.find 1373 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1373_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1367_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1371_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1372_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1367_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1371_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1372_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8644_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8644 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8644 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8284_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8643_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8644_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (43 <= t)%coq_nat -> (43 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8644 (history t) = VM.find 8644 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8644_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8284_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8643_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8284_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8643_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8693_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8693 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8693 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8284_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8692_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8693_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (43 <= t)%coq_nat -> (43 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8693 (history t) = VM.find 8693 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8693_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8284_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8692_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8284_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8692_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1374_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1374 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1374 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1370_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1374_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (44 <= t)%coq_nat -> (44 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1374 (history t) = VM.find 1374 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1374_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1370_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1370_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1375_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1375 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1375 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1373_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1375_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (44 <= t)%coq_nat -> (44 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1375 (history t) = VM.find 1375 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1375_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1373_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1373_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8645_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8645 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8645 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8282_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8644_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8645_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (44 <= t)%coq_nat -> (44 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8645 (history t) = VM.find 8645 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8645_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8282_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8644_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8282_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8644_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8694_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8694 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8694 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8282_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8693_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8694_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (44 <= t)%coq_nat -> (44 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8694 (history t) = VM.find 8694 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8694_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8282_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8693_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8282_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8693_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8646_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (45 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8646 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8646 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8280_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8645_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8646_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (45 <= t)%coq_nat -> (45 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8646 (history t) = VM.find 8646 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8646_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8280_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8645_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8280_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8645_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8695_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (45 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8695 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8695 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8280_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8694_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8695_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (45 <= t)%coq_nat -> (45 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8695 (history t) = VM.find 8695 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8695_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8280_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8694_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8280_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8694_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8647_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (46 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8647 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8647 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8278_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8646_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8647_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (46 <= t)%coq_nat -> (46 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8647 (history t) = VM.find 8647 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8647_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8278_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8646_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8278_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8646_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8696_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (46 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8696 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8696 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8278_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8695_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8696_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (46 <= t)%coq_nat -> (46 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8696 (history t) = VM.find 8696 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8696_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8278_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8695_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8278_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8695_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8648_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (47 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8648 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8648 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8276_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8647_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8648_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (47 <= t)%coq_nat -> (47 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8648 (history t) = VM.find 8648 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8648_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8276_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8647_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8276_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8647_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8697_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (47 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8697 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8697 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8276_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8696_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8697_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (47 <= t)%coq_nat -> (47 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8697 (history t) = VM.find 8697 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8697_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8276_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8696_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8276_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8696_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8649_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (48 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8649 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8649 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8274_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8648_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8649_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (48 <= t)%coq_nat -> (48 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8649 (history t) = VM.find 8649 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8649_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8274_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8648_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8274_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8648_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8698_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (48 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8698 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8698 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8274_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8697_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8698_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (48 <= t)%coq_nat -> (48 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8698 (history t) = VM.find 8698 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8698_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8274_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8697_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8274_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8697_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8650_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (49 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8650 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8650 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8272_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8649_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8650_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (49 <= t)%coq_nat -> (49 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8650 (history t) = VM.find 8650 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8650_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8272_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8649_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8272_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8649_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8699_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (49 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8699 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8699 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8272_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8698_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8699_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (49 <= t)%coq_nat -> (49 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8699 (history t) = VM.find 8699 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8699_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8272_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8698_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8272_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8698_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8651_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (50 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8651 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8651 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8270_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8650_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8651_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (50 <= t)%coq_nat -> (50 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8651 (history t) = VM.find 8651 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8651_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8270_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8650_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8270_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8650_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8700_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (50 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8700 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8700 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8270_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8699_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8700_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (50 <= t)%coq_nat -> (50 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8700 (history t) = VM.find 8700 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8700_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8270_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8699_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8270_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8699_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8652_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (51 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8652 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8652 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8268_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8651_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8652_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (51 <= t)%coq_nat -> (51 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8652 (history t) = VM.find 8652 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8652_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8268_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8651_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8268_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8651_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8701_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (51 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8701 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8701 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8268_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8700_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8701_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (51 <= t)%coq_nat -> (51 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8701 (history t) = VM.find 8701 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8701_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8268_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8700_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8268_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8700_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8653_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (52 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8653 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8653 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8266_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8652_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8653_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (52 <= t)%coq_nat -> (52 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8653 (history t) = VM.find 8653 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8653_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8266_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8652_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8266_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8652_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8702_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (52 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8702 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8702 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8266_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8701_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8702_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (52 <= t)%coq_nat -> (52 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8702 (history t) = VM.find 8702 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8702_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8266_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8701_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8266_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8701_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8654_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (53 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8654 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8654 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8264_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8653_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8654_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (53 <= t)%coq_nat -> (53 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8654 (history t) = VM.find 8654 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8654_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8264_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8653_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8264_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8653_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8703_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (53 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8703 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8703 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_8264_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8702_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8703_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (53 <= t)%coq_nat -> (53 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8703 (history t) = VM.find 8703 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8703_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_8264_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_concrete_8702_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8264_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_8702_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8256_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (54 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8256 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_8256_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - apply (early_control_concrete_8654_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
 - exists 3%nat, bits. exact Value.
Qed.
Theorem early_control_stable_8256_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (54 <= t)%coq_nat -> (54 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8256 (history t) = VM.find 8256 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_8256_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_8654_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8998_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (54 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 8998 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_8998 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_8703_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_8998_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (54 <= t)%coq_nat -> (54 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8998 (history t) = VM.find 8998 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_8998_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_8703_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_8703_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_90_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 90 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_90_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_8256_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 3%nat, bits. exact Value.
Qed.
Theorem early_control_stable_90_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (55 <= t)%coq_nat -> (55 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 90 (history t) = VM.find 90 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_90_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_8256_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_8251_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 8251 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_8251_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - apply (early_control_concrete_8998_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
 - exists 1%nat, bits. exact Value.
Qed.
Theorem early_control_stable_8251_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (55 <= t)%coq_nat -> (55 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 8251 (history t) = VM.find 8251 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_8251_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_8998_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_85_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 85 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_85_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_8251_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 1%nat, bits. exact Value.
Qed.
Theorem early_control_stable_85_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (56 <= t)%coq_nat -> (56 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 85 (history t) = VM.find 85 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_85_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_8251_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1359_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 1359 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_1359_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - destruct (early_control_concrete_90_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
 - exists 3%nat, bits. exact Value.
Qed.
Theorem early_control_stable_1359_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (56 <= t)%coq_nat -> (56 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1359 (history t) = VM.find 1359 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_1359_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_90_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1376_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1376 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1376 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1376_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (57 <= t)%coq_nat -> (57 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1376 (history t) = VM.find 1376 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1376_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1378_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1378 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1378 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1378_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (57 <= t)%coq_nat -> (57 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1378 (history t) = VM.find 1378 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1378_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1381_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1381 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1381 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1381_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (57 <= t)%coq_nat -> (57 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1381 (history t) = VM.find 1381 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1381_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1384_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1384 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1384 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1384_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (57 <= t)%coq_nat -> (57 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1384 (history t) = VM.find 1384 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1384_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1387_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1387 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1387 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1387_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (57 <= t)%coq_nat -> (57 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1387 (history t) = VM.find 1387 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1387_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1390_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1390 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1390 inputs path (history time) (history time) (history (S time))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps time ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1390_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (57 <= t)%coq_nat -> (57 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1390 (history t) = VM.find 1390 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1390_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - destruct (early_control_concrete_1359_history inputs path history limit Boundary Steps t ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.
 - apply (early_control_stable_1359_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1377_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1377 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1377 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1364_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1376_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1377_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (58 <= t)%coq_nat -> (58 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1377 (history t) = VM.find 1377 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1377_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1364_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1376_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1364_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1376_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1379_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1379 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1379 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1363_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1378_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1379_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (58 <= t)%coq_nat -> (58 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1379 (history t) = VM.find 1379 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1379_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1363_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1378_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1363_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1378_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1382_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1382 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1382 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1370_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1381_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1382_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (58 <= t)%coq_nat -> (58 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1382 (history t) = VM.find 1382 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1382_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1370_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1381_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1370_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1381_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1385_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1385 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1385 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1374_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1384_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1385_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (58 <= t)%coq_nat -> (58 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1385 (history t) = VM.find 1385 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1385_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1374_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1384_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1374_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1384_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1388_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1388 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1388 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1373_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1387_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1388_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (58 <= t)%coq_nat -> (58 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1388 (history t) = VM.find 1388 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1388_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1373_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1387_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1373_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1387_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1391_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1391 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1391 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1375_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1390_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1391_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (58 <= t)%coq_nat -> (58 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1391 (history t) = VM.find 1391 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1391_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1375_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1390_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1375_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1390_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1380_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (59 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1380 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1380 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1377_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1379_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1380_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (59 <= t)%coq_nat -> (59 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1380 (history t) = VM.find 1380 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1380_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1377_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1379_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1377_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1379_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1383_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (60 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1383 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1383 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1380_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1382_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1383_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (60 <= t)%coq_nat -> (60 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1383 (history t) = VM.find 1383 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1383_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1380_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1382_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1380_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1382_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1386_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (61 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1386 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1386 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1383_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1385_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1386_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (61 <= t)%coq_nat -> (61 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1386 (history t) = VM.find 1386 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1386_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1383_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1385_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1383_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1385_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1389_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (62 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1389 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1389 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1386_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1388_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1389_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (62 <= t)%coq_nat -> (62 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1389 (history t) = VM.find 1389 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1389_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1386_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1388_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1386_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1388_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1392_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (63 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists ground bits, VM.find 1392 (history time) = Some (Gval ground bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (joint_update_node_output_1392 inputs path (history time) (history time) (history (S time))).
 - apply (early_control_concrete_1389_history inputs path history limit Boundary Steps time); lia.
 - apply (early_control_concrete_1391_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem early_control_stable_1392_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (63 <= t)%coq_nat -> (63 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1392 (history t) = VM.find 1392 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_node_1392_congruent inputs path (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_concrete_1389_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_concrete_1391_history inputs path history limit Boundary Steps t); lia.
 - apply (early_control_stable_1389_history inputs path history limit Boundary Steps t u); lia.
 - apply (early_control_stable_1391_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
Theorem early_control_concrete_1360_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (64 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists width bits, VM.find 1360 (history time) = Some (Gval (Fuint width) bits).
Proof.
 intros Boundary Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 destruct (early_control_wire_1360_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].
 - apply (early_control_concrete_1392_history inputs path history limit Boundary Steps time); lia.
 - apply Steps. lia.
 - exists 1%nat, bits. exact Value.
Qed.
Theorem early_control_stable_1360_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (64 <= t)%coq_nat -> (64 <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 1360 (history t) = VM.find 1360 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 apply (early_control_wire_1360_congruent (formal_invalid_policy inputs path) (history t) (history u) (history (S t)) (history (S u))).
 - apply (early_control_stable_1392_history inputs path history limit Boundary Steps t u); lia.
 - apply Steps. lia.
 - apply Steps. lia.
Qed.
(* Audit the two public targets separately in EarlyControlStabilityHistoryAssumptions.v. *)
