Require Import CoreSocModel ComparisonNodes FormalPCControlNodes FormalSuccessfulNodeEvaluation EarlyControlWireBitNormalization EarlyBubbleNopControlKnown FetchPCDecodeStability FormalPCControlConcrete EarlyControlStabilityHistory JointUpdateBoundaryHistory JointBoundaryRegisters ConcreteRegisterInitialization FormalInstructionResetCycle.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem fetch_pc_decode_same_history inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (55 <= t)%coq_nat -> (55 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 exists word, VM.find 84 (history t) = Some (Gval (Fuint 2) word) /\ VM.find 84 (history u) = Some (Gval (Fuint 2) word).
Proof.
 intros Boundary Steps. apply (fetch_pc_decode_history_same _ history limit Steps).
 assert (Member : List.In (7748%nat,32%nat) joint_boundary_registers).
 { apply (List.nth_error_In joint_boundary_registers 53%nat). vm_compute; reflexivity. }
 intros t u T U.
 destruct (Boundary 7748%nat 32%nat Member) as [word [Size Initial]].
 exists word. split.
 - rewrite (joint_update_register_history_same _ history limit 7748 32 Member Steps t T). exact Initial.
 - rewrite (joint_update_register_history_same _ history limit 7748 32 Member Steps u U). exact Initial.
Qed.
Theorem fetch_pc_selector_7771_same inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (56 <= t)%coq_nat -> (56 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7771 (history t) = VM.find 7771 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 destruct (fetch_pc_decode_same_history inputs path history limit Boundary Steps t u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [word [Left Right]].
 destruct (pc_control_eval_7771 (history t) 2 word Left) as [bit Eval].
 assert (EvalR : eval_hfexpr_with_memory flat_memories pc_control_expr_7771 (history u) (history u) = Some (Gval (Fuint 1) [::bit])).
 { replace (eval_hfexpr_with_memory flat_memories pc_control_expr_7771 (history u) (history u)) with (eval_hfexpr_with_memory flat_memories pc_control_expr_7771 (history t) (history t)); [exact Eval|].
 cbn [pc_control_expr_7771 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right. reflexivity. }
 rewrite (pc_control_node_7771 _ _ _ _ _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
 rewrite (pc_control_node_7771 _ _ _ _ _ EvalR (Logic.eq_refl _) (Steps u ltac:(lia))). reflexivity.
Qed.
Theorem fetch_pc_selector_7772_same inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (56 <= t)%coq_nat -> (56 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7772 (history t) = VM.find 7772 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 destruct (fetch_pc_decode_same_history inputs path history limit Boundary Steps t u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [word [Left Right]].
 destruct (pc_control_eval_7772 (history t) 2 word Left) as [bit Eval].
 assert (EvalR : eval_hfexpr_with_memory flat_memories pc_control_expr_7772 (history u) (history u) = Some (Gval (Fuint 1) [::bit])).
 { replace (eval_hfexpr_with_memory flat_memories pc_control_expr_7772 (history u) (history u)) with (eval_hfexpr_with_memory flat_memories pc_control_expr_7772 (history t) (history t)); [exact Eval|].
 cbn [pc_control_expr_7772 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right. reflexivity. }
 rewrite (pc_control_node_7772 _ _ _ _ _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
 rewrite (pc_control_node_7772 _ _ _ _ _ EvalR (Logic.eq_refl _) (Steps u ltac:(lia))). reflexivity.
Qed.
Theorem fetch_pc_selector_7776_same inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (56 <= t)%coq_nat -> (56 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7776 (history t) = VM.find 7776 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 destruct (fetch_pc_decode_same_history inputs path history limit Boundary Steps t u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [word [Left Right]].
 destruct (pc_control_eval_7776 (history t) 2 word Left) as [bit Eval].
 assert (EvalR : eval_hfexpr_with_memory flat_memories pc_control_expr_7776 (history u) (history u) = Some (Gval (Fuint 1) [::bit])).
 { replace (eval_hfexpr_with_memory flat_memories pc_control_expr_7776 (history u) (history u)) with (eval_hfexpr_with_memory flat_memories pc_control_expr_7776 (history t) (history t)); [exact Eval|].
 cbn [pc_control_expr_7776 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right. reflexivity. }
 rewrite (pc_control_node_7776 _ _ _ _ _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
 rewrite (pc_control_node_7776 _ _ _ _ _ EvalR (Logic.eq_refl _) (Steps u ltac:(lia))). reflexivity.
Qed.
Theorem fetch_pc_selector_7773_same inputs path history limit :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall t u, (65 <= t)%coq_nat -> (65 <= u)%coq_nat -> (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find 7773 (history t) = VM.find 7773 (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
 destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
 pose proof (fetch_pc_selector_7772_same inputs path history limit Boundary Steps t u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Decode.
 pose proof (early_control_stable_1360_history inputs path history limit Boundary Steps t u ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Branch.
 (* Recover the actual successful node evaluation, then transport it. *)
 destruct (formal_successful_node_evaluation 8279 flat_statements pc_control_tail_7773 7773 pc_control_expr_7773 (formal_invalid_policy inputs path)
 flat_memories (history t) false (history t) (history (S t)) pc_control_position_7773 (Steps t ltac:(lia))) as [value Eval].
 rewrite add0n in Eval.
 assert (Typed : type_of_val value = Gtyp (Fuint 1)).
 { destruct (fetch_pc_decode_same_history inputs path history limit Boundary Steps (Nat.pred t) (Nat.pred t) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [word [Word Other]].
   destruct t as [|t]; [lia|]. cbn [Nat.pred] in Word.
   destruct (pc_control_concrete_7772 _ _ _ _ 2 word Word (Steps t ltac:(lia))) as [bit Bit].
   destruct (early_control_wire_1360_normalized _ (history t) (history t) (history (S t)) (Steps t ltac:(lia))) as [v [V Normal]].
   destruct (early_bubble_normalized_concrete _ 1360 v V Normal (early_control_concrete_1360_history inputs path history limit Boundary Steps (S t) ltac:(lia) ltac:(lia))) as [b B].
   cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory eval_hfexpr_validif_policy eval_href_validif_policy] in Eval. rewrite Bit B in Eval.
   destruct bit,b; inversion Eval; reflexivity. }
 assert (EvalR : eval_hfexpr_with_memory flat_memories pc_control_expr_7773 (history u) (history u) = Some value).
 { replace (eval_hfexpr_with_memory flat_memories pc_control_expr_7773 (history u) (history u)) with (eval_hfexpr_with_memory flat_memories pc_control_expr_7773 (history t) (history t)); [exact Eval|].
 cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Decode Branch. reflexivity. }
 rewrite (pc_control_node_7773 _ _ _ _ _ Eval Typed (Steps t ltac:(lia))).
 rewrite (pc_control_node_7773 _ _ _ _ _ EvalR Typed (Steps u ltac:(lia))). reflexivity.
Qed.
