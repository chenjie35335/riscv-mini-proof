Require Import X0ConcreteSafetyCertificate X0ConcretePositionCertificate RFReferenceWriteEffect SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_selected_low_mux offsets nodes node (condition:hfexpr VarOrder.T) yes no invalid old result bit selected word :
 select_node_offsets offsets flat_statements=Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements=true ->
 List.In(node,@Emux VarOrder.T condition(@Eref VarOrder.T(@Eid VarOrder.T yes))(@Eref VarOrder.T(@Eid VarOrder.T no)))nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories condition old old=Some(Gval(Fuint 1)[::bit])) ->
 VM.find(if bit then yes else no)old=Some selected ->rf_reference_low_word word selected ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find node result=Some value /\rf_reference_low_word word value.
Proof.
 intros Positions Safety Member Condition Selected [width[raw[Value[Size[Wide Low]]]]] Step. subst selected.
 destruct(selected_node_safe_position flat_memories flat_statements offsets flat_statements nodes node _ Positions Safety Member)as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false old result Position Step)as[value Eval].
 pose proof Eval as Original.
 cbn[eval_hfexpr_validif_policy]in Eval. rewrite Condition in Eval.
 destruct bit;cbn in Eval;rewrite Selected in Eval;
 destruct(eval_type_of_expr _)as[typ|]eqn:Branch;try discriminate;
 unfold extend_hvalue_as_type in Eval;destruct typ as[ground|elt length|fields];try discriminate;
 destruct ground;cbn[type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type]in Eval;try discriminate;
 inversion Eval;subst value.
 all: eexists;split;[eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg|exact Original|reflexivity|exact Step]|].
 all: destruct(rf_reference_low_resize word (Gval(Fuint width)raw) (maxn width n))as[adapted[Adapt Result]].
all: try (exists width,raw;repeat split;assumption).
all: try (intros source bits Equal;inversion Equal;subst;apply leq_maxl).
all: cbn[adapt_hvalue_as_type]in Adapt;inversion Adapt;subst;exact Result.
Qed.
