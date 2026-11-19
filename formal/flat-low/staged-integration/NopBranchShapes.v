From nbits Require Import NBits.
Require Import CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalSuccessfulNodeEvaluation JointUpdateNodePositions JointUpdateExpressionCertificates NormalizedBit.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma nop_branch_normalized_type value : normalized_bit value -> type_of_val value = Gtyp (Fuint 1).
Proof. intro H; destruct H; reflexivity. Qed.
Lemma nop_branch_mux_normalized mm old (condition : hfexpr VarOrder.T) (yes no : VarOrder.T) left right result :
 VM.find yes old = Some left -> type_of_val left = Gtyp (Fuint 1) ->
 VM.find no old = Some right -> type_of_val right = Gtyp (Fuint 1) ->
 eval_hfexpr_with_memory mm (Emux condition (Eref (Eid yes)) (Eref (Eid no))) old old = Some result ->
 normalized_bit result.
Proof.
 intros Left LeftType Right RightType Eval.
 assert (YesType : eval_type_of_expr (Eref (Eid yes)) old = Some (Gtyp (Fuint 1))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Left. cbn [option_map]. rewrite LeftType. reflexivity. }
 assert (NoType : eval_type_of_expr (Eref (Eid no)) old = Some (Gtyp (Fuint 1))).
 { unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Right. cbn [option_map]. rewrite RightType. reflexivity. }
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Left Right YesType NoType in Eval.
 destruct (eval_hfexpr_with_memory mm condition old old) as [value|] eqn:Condition; [|discriminate Eval].
 destruct value as [ground bits|element values|fields|typ|typ|typ]; try discriminate Eval.
 - destruct ground; try discriminate Eval. destruct (is_zero bits);
   unfold extend_hvalue_as_type in Eval; rewrite ?LeftType ?RightType in Eval;
   cbn [ftype_mux fgtyp_mux] in Eval;
   eapply adapted_bit_normalized; exact Eval.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [ftype_mux fgtyp_mux option_map] in Eval;
   inversion Eval; constructor.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [ftype_mux fgtyp_mux option_map] in Eval;
   inversion Eval; constructor.
 - destruct typ as [ground|element count|fields]; try discriminate Eval.
   destruct ground; try discriminate Eval; cbn [ftype_mux fgtyp_mux option_map] in Eval;
   inversion Eval; constructor.
Qed.

Lemma nop_branch_reduction_or_normalized value result :
 eval_unop Uorr value = Some result -> normalized_bit result.
Proof.
 destruct value as [ground bits|element array|bundle|t|t|t];
 try destruct ground; try destruct t;
 try match goal with x : fgtyp |- _ => destruct x end;
 cbn [eval_unop]; intro H; try discriminate H; inversion H; subst; constructor.
Qed.

Lemma nop_branch_comparison_false_normalized value result :
 eval_binop (Bcomp Beq) value (Gval (Fuint 1) [::false]) = Some result ->
 normalized_bit result.
Proof.
 destruct value as [ground bits|element array|bundle|t|t|t];
 unfold eval_binop, absorbing_bit, refine_boolean_result, eval_binop_basic;
 try (intro H; discriminate H).
 all: try destruct ground; try destruct t.
 all: try match goal with x : fgtyp |- _ => destruct x end.
 all: cbn; intro H.
 all: repeat match type of H with context [if ?b then _ else _] => destruct b end.
 all: cbn in H; try discriminate H; inversion H; subst; constructor.
Qed.

Lemma nop_branch_extract_result_type hi lo value result :
 eval_unop (Uextr hi lo) value = Some result ->
 type_of_val result = Gtyp (Fuint (hi.+1 - lo)).
Proof.
 destruct value as [ground bits|element array|bundle|typ|typ|typ];
 try destruct typ; try destruct ground; try match goal with f : fgtyp |- _ => destruct f end; cbn [eval_unop]; intro Eval;
 try discriminate Eval.
 all: repeat match type of Eval with context [if ?condition then _ else _] => destruct condition end;
 try discriminate Eval; inversion Eval; reflexivity.
Qed.
Lemma nop_branch_zero_and_normalized value : normalized_bit value ->
 eval_binop Band (Gval (Fuint 1) [::false]) value = Some (Gval (Fuint 1) [::false]).
Proof. intro Normal; destruct Normal as [b| | |]; try destruct b; reflexivity. Qed.
Lemma nop_branch_node_shape node expression (P : hvalue -> Prop) invalid old current result :
 List.In (node,expression) joint_update_expected_nodes ->
 (forall site value, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories expression old old = Some value -> P value) ->
 (forall value, P value -> type_of_val value = Gtyp (Fuint 1)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find node result = Some value /\ P value.
Proof.
 intros Member Shape Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes node expression joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node expression invalid flat_memories old false current result Position Step) as [value Eval].
 rewrite add0n in Eval.
 pose proof (Shape _ _ Eval) as Shaped.
 exists value; split; [|exact Shaped].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg|exact Eval|apply Typed;exact Shaped|exact Step].
Qed.
