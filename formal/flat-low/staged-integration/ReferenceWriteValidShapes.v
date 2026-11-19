From nbits Require Import NBits.
Require Import ReferenceRequestSpine NopBranchShapes NormalizedBit SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma reference_write_constant_mux_normalized mm old (condition: hfexpr VarOrder.T) (no:VarOrder.T) result :
 VM.find no old=Some(Gval(Fuint 1)[::false]) ->
 eval_hfexpr_with_memory mm (Emux condition (@Econst VarOrder.T(Fuint 1)[::true])(Eref(Eid no)))old old=Some result ->
 normalized_bit result.
Proof.
 intros No Eval.
 cbn[eval_hfexpr_with_memory eval_href_with_memory]in Eval.
 rewrite No in Eval.
 unfold eval_type_of_expr in Eval. cbn[type_of_expr' eval_type_of_ref]in Eval. rewrite No in Eval.
 destruct(eval_hfexpr_with_memory mm condition old old)as[value|];[|discriminate].
 destruct value as[ground bits|element values|fields|typ|typ|typ];try discriminate Eval.
 - destruct ground;try discriminate Eval. destruct(is_zero bits);inversion Eval;constructor.
 - destruct typ as[ground|element count|fields];try discriminate Eval.
   destruct ground;try discriminate Eval;inversion Eval;constructor.
 - destruct typ as[ground|element count|fields];try discriminate Eval.
   destruct ground;try discriminate Eval;inversion Eval;constructor.
 - destruct typ as[ground|element count|fields];try discriminate Eval.
   destruct ground;try discriminate Eval;inversion Eval;constructor.
Qed.
Lemma reference_write_valid_node_shape node expression (P:hvalue->Prop) invalid old current result :
 List.In(node,expression)reference_request_nodes ->
 (forall site value,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expression old old=Some value ->P value) ->
 (forall value,P value ->type_of_val value=Gtyp(Fuint 1)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 exists value,VM.find node result=Some value /\P value.
Proof.
 intros Member Shape Typed Step.
 destruct(selected_node_safe_position flat_memories flat_statements reference_request_offsets flat_statements reference_request_nodes node expression
 reference_request_positions reference_request_safety Member)as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail node expression invalid flat_memories old false current result Position Step)as[value Eval].
 rewrite add0n in Eval. pose proof(Shape _ _ Eval)as Shaped.
 exists value. split;[|exact Shaped].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Eval|apply Typed;exact Shaped|exact Step].
Qed.
Lemma reference_write_false_mux_typed invalid site old (guard yes no:VarOrder.T) other :
 VM.find guard old=Some(Gval(Fuint 1)[::false]) ->
 VM.find yes old=Some other ->type_of_val other=Gtyp(Fuint 1) ->
 VM.find no old=Some(Gval(Fuint 1)[::false]) ->
 eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories
 (Emux(Eref(Eid guard))(Eref(Eid yes))(Eref(Eid no)))old old=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Guard Yes Typed No. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite Guard. cbn. rewrite No. unfold eval_type_of_expr. cbn[type_of_expr' eval_type_of_ref]. rewrite Yes. cbn[option_map]. rewrite Typed. reflexivity.
Qed.

Lemma reference_write_alignment_6659_type invalid old current result :
 VM.find 6642 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 exists value,VM.find 6659 result=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros No Step.
 destruct(reference_write_valid_node_shape 6659 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6642))) normalized_bit invalid old current result)as[value[Value Normal]].
 - apply(List.nth_error_In reference_request_nodes 24%nat). vm_compute;reflexivity.
 - intros site value Eval. change(eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6642))) old old=Some value)in Eval. exact(reference_write_constant_mux_normalized flat_memories old (@Eref VarOrder.T (@Eid VarOrder.T 2723)) 6642 value No Eval).
 - exact nop_branch_normalized_type.
 - exact Step.
 - exists value. split;[exact Value|apply nop_branch_normalized_type;exact Normal].
Qed.

Lemma reference_write_alignment_6683_type invalid old current result :
 VM.find 6668 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 exists value,VM.find 6683 result=Some value /\type_of_val value=Gtyp(Fuint 1).
Proof.
 intros No Step.
 destruct(reference_write_valid_node_shape 6683 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6668))) normalized_bit invalid old current result)as[value[Value Normal]].
 - apply(List.nth_error_In reference_request_nodes 28%nat). vm_compute;reflexivity.
 - intros site value Eval. change(eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 6668))) old old=Some value)in Eval. exact(reference_write_constant_mux_normalized flat_memories old (@Eref VarOrder.T (@Eid VarOrder.T 2708)) 6668 value No Eval).
 - exact nop_branch_normalized_type.
 - exact Step.
 - exists value. split;[exact Value|apply nop_branch_normalized_type;exact Normal].
Qed.
