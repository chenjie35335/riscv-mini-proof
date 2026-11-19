Require Import CoreSocModel ComparisonNodes X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma zero_word_resize source target :zext_to target(take target(zeros source))=zeros target.
Proof.
 rewrite take_zeros. unfold zext_to. rewrite size_zeros zext_zero.
 rewrite subnK;[reflexivity|apply geq_minl].
Qed.
Theorem selected_zero_mux offsets nodes node (condition yes no:hfexpr VarOrder.T) invalid old result bit width :
 select_node_offsets offsets flat_statements=Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements=true ->
 List.In(node,@Emux VarOrder.T condition yes no)nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories condition old old=Some(Gval(Fuint 1)[::bit])) ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(if bit then yes else no)old old=Some(Gval(Fuint width)(zeros width))) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists output_width,VM.find node result=Some(Gval(Fuint output_width)(zeros output_width)).
Proof.
 intros Positions Safety Member Condition Selected Step.
 destruct(selected_node_safe_position flat_memories flat_statements offsets flat_statements nodes node _ Positions Safety Member)as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false old result Position Step)as[value Eval].
 pose proof Eval as Original.
 cbn [eval_hfexpr_validif_policy]in Eval. rewrite Condition in Eval.
 destruct bit;cbn in Eval;rewrite Selected in Eval;
 destruct(eval_type_of_expr _)as[typ|]eqn:Branch;try discriminate;
 unfold extend_hvalue_as_type in Eval;destruct typ as[ground|elt length|fields];try discriminate;
 destruct ground;cbn[type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type]in Eval;try discriminate;
 rewrite zero_word_resize in Eval;inversion Eval;subst value.
 all: eexists;eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Original|reflexivity|exact Step].
Qed.
