Require Import UIntResizeRoundtrip X0ConcreteSafetyCertificate X0ConcretePositionCertificate RFReferenceWriteEffect SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_boolean_word bit value :=exists width,(1<=width)%coq_nat /\value=Gval(Fuint width)(zext_to width [::bit]).
Lemma rf_boolean_resize width bit larger :(1<=width)%coq_nat ->(width<=larger)%nat ->
 adapt_hvalue_as_type (Gval(Fuint width)(zext_to width[::bit]))(Gtyp(Fuint larger))=Some(Gval(Fuint larger)(zext_to larger[::bit])).
Proof.
 intros Width Large. cbn[adapt_hvalue_as_type]. f_equal;f_equal.
 rewrite<-(take_oversize (n:=width) (s:=[::bit]) ltac:(apply/leP;exact Width)) at 1.
 apply(resize_uint_roundtrip_widen 1);[reflexivity|apply/leP;move/leP:Large;lia|apply/leP;lia].
Qed.
Lemma rf_boolean_mux offsets nodes node (condition:hfexpr VarOrder.T) yes no invalid old result bit selected word :
 select_node_offsets offsets flat_statements=Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements=true ->
 List.In(node,@Emux VarOrder.T condition(@Eref VarOrder.T(@Eid VarOrder.T yes))(@Eref VarOrder.T(@Eid VarOrder.T no)))nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories condition old old=Some(Gval(Fuint 1)[::bit])) ->
 VM.find(if bit then yes else no)old=Some selected ->rf_boolean_word word selected ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find node result=Some value /\rf_boolean_word word value.
Proof.
 intros Positions Safety Member Condition Selected [width[Wide Value]] Step. subst selected.
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
 all: exists(maxn width n);split;[move/leP:(leq_maxl width n);lia|].
 all: f_equal;change(zext_to(maxn width n)(take(maxn width n)(zext_to width[::word]))=zext_to(maxn width n)[::word]);rewrite<-(take_oversize (n:=width) (s:=[::word]) ltac:(apply/leP;exact Wide)) at 1;apply(resize_uint_roundtrip_widen 1);[reflexivity|apply/leP;move/leP:(leq_maxl width n);lia|apply/leP;lia].
Qed.
