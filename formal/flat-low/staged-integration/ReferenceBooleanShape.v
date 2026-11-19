Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate CoreSocModel ComparisonNodes SelectedNodeSafety ReferenceRedirectSpine FormalSuccessfulNodeEvaluation FormalGroundNodeEquation ComparisonConstantBitShape NormalizedBit.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_zero_comparison_normalized offsets nodes node source invalid old result :
 select_node_offsets offsets flat_statements = Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements = true ->
 List.In (node, @Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T source)) (@Econst VarOrder.T (Fuint 1) [::false])) nodes ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find node result = Some value /\ normalized_bit value.
Proof.
 intros Positions Safety Member Step.
 destruct (selected_node_safe_position flat_memories flat_statements offsets flat_statements nodes node _ Positions Safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false old result Position Step) as [value Eval].
 rewrite add0n in Eval.
 assert (Normal : normalized_bit value).
 { cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find source old) as [operand|] eqn:Source;[|discriminate Eval].
   exact (comparison_uint_constant_right_normalized operand 1 [::false] value Eval). }
 exists value;split;[|exact Normal].
 eapply (formal_combinational_known_ground_node count flat_statements tail node _ (Fuint 1));
 [exact Position|exact Safe|exact Nonreg|exact Eval|destruct Normal;reflexivity|exact Step].
Qed.
