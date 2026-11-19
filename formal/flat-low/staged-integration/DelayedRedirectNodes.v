Require Import CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation FormalInstructionResetConstants FormalPCControlNodes FormalPCControlConcrete JointRegisterCommits8 FormalRegisterReferenceObservation FormalRegisterCommitIdentity.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma delayed_redirect_member_7858 : List.In (7858,joint_update_expr_7858) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 913%nat). vm_compute. reflexivity. Qed.
Theorem delayed_redirect_node_7858 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7858 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7858 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7858 joint_update_expr_7858 joint_update_node_positions joint_update_node_safety delayed_redirect_member_7858)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma delayed_redirect_member_7859 : List.In (7859,joint_update_expr_7859) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 914%nat). vm_compute. reflexivity. Qed.
Theorem delayed_redirect_node_7859 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7859 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7859 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7859 joint_update_expr_7859 joint_update_node_positions joint_update_node_safety delayed_redirect_member_7859)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma delayed_redirect_member_7870 : List.In (7870,joint_update_expr_7870) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 925%nat). vm_compute. reflexivity. Qed.
Theorem delayed_redirect_node_7870 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7870 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7870 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7870 joint_update_expr_7870 joint_update_node_positions joint_update_node_safety delayed_redirect_member_7870)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Lemma delayed_redirect_member_7876 : List.In (7876,joint_update_expr_7876) joint_update_expected_nodes.
Proof. apply (List.nth_error_In joint_update_expected_nodes 931%nat). vm_compute. reflexivity. Qed.
Theorem delayed_redirect_node_7876 invalid old current result value :
 eval_hfexpr_with_memory flat_memories joint_update_expr_7876 old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7876 result = Some value.
Proof.
 intros Eval Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes 7876 joint_update_expr_7876 joint_update_node_positions joint_update_node_safety delayed_redirect_member_7876)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg|exact Eval|exact Typed|exact Step].
Qed.
Theorem delayed_redirect_same_after_two invalid s0 s1 s2 word branch :
 VM.find 84 s0 = Some (Gval (Fuint 2) word) ->
 VM.find 1360 s1 = Some (Gval (Fuint 1) [::branch]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7859 s2 = VM.find 7773 s2.
Proof.
 intros Word Branch S1 S2.
 destruct (pc_control_eval_7772 s0 2 word Word) as [bit Eval].
 pose proof (pc_control_node_7772 invalid s0 s0 s1 _ Eval (Logic.eq_refl _) S1) as Decode.
 assert (Other : VM.find 7858 s1 = Some (Gval (Fuint 1) [::bit])).
 { apply (delayed_redirect_node_7858 invalid s0 s0 s1); [exact Eval|reflexivity|exact S1]. }
 assert (V : VM.find 7859 s2 = Some (Gval (Fuint 1) [::bit || branch])).
 { apply (delayed_redirect_node_7859 invalid s1 s1 s2); [|reflexivity|exact S2].
 cbn [joint_update_expr_7859 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Other Branch. destruct bit,branch;reflexivity. }
 rewrite V. symmetry. apply (pc_control_node_7773 invalid s1 s1 s2); [|reflexivity|exact S2].
 cbn [pc_control_expr_7773 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Decode Branch. destruct bit,branch;reflexivity.
Qed.
Theorem delayed_redirect_select invalid s0 s1 s2 old bit :
 VM.find 7855 s0 = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7859 s0 = Some (Gval (Fuint 1) [::bit]) ->
 VM.find 7760 s0 = Some (Gval (Fuint 1) old) ->
 VM.find 7852 s1 = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7876 s2 = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Advance Source Old Flush S1 S2.
 assert (Value : VM.find 7870 s1 = Some (Gval (Fuint 1) [::bit])).
 { apply (delayed_redirect_node_7870 invalid s0 s0 s1); [|reflexivity|exact S1].
 cbn [joint_update_expr_7870 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Advance Source.
 unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Old. destruct bit;reflexivity. }
 apply (delayed_redirect_node_7876 invalid s1 s1 s2); [|reflexivity|exact S2].
 cbn [joint_update_expr_7876 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Flush Value. destruct bit;reflexivity.
Qed.
Theorem delayed_redirect_commit invalid old current result old_value bit :
 VM.find 7760 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 1) ->
 VM.find 7876 old = Some (Gval (Fuint 1) [::bit]) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7760 result = Some (Gval (Fuint 1) [::bit]).
Proof.
 intros Old Typed Source Step. unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old true current flat_statements) as [proposed|] eqn:Statements; [|discriminate Step].
 destruct (formal_register_reference_observation 8266 flat_statements joint_register_7760_decl joint_register_7760_mid joint_register_7760_tail 7760 joint_register_7760_reg (@Eid VarOrder.T 7876) invalid flat_memories old true current proposed old_value 1
 joint_register_7760_position joint_register_7760_split (Logic.eq_refl _) joint_register_7760_straight joint_register_7760_mid_safe joint_register_7760_tail_safe Old Typed Statements)
 as [source [value [Eval [Adapt Value]]]].
 cbn [eval_href_with_memory] in Eval. rewrite Source in Eval. inversion Eval; subst source.
 destruct bit; cbn [adapt_hvalue_as_type] in Adapt; inversion Adapt; subst value;
 rewrite (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result 7760 joint_register_7760_identity Step); exact Value.
Qed.
