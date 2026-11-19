Require Import CoreSocModel ComparisonNodes UIntResizeRoundtrip.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_reference_word_extension (base : bits) value :=
 exists width, (32 <= width)%nat /\ value = Gval (Fuint width) (zext_to width base).
Lemma rf_reference_word_resize base width target :
 size base = 32%nat -> (32 <= width)%nat -> (32 <= target)%nat ->
 zext_to target (take target (zext_to width base)) = zext_to target base.
Proof.
 intros Size Width Target.
 assert (Take : take width base = base).
 { apply take_oversize. rewrite Size. exact Width. }
 rewrite <- Take at 1.
 exact (resize_uint_roundtrip_widen 32 target width base Size Target Width).
Qed.
Lemma rf_reference_word_false_mux_extension mm old (condition yes no : VarOrder.T) base input source :
 size base = 32%nat -> rf_reference_word_extension base input ->
 VM.find condition old = Some (Gval (Fuint 1) [::false]) ->
 VM.find no old = Some input ->
 eval_hfexpr_with_memory mm (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 rf_reference_word_extension base source.
Proof.
 intros Size [width [Width Input]] Condition No Eval. subst input.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Condition in Eval. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 change (is_zero [:: false]) with true in Eval. cbn in Eval.
 rewrite No in Eval.
 destruct (eval_type_of_expr (Eref (Eid yes)) old) as [ty|]; [|discriminate].
 unfold extend_hvalue_as_type in Eval.
 destruct ty as [ground|element count|fields]; try discriminate.
 destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
 inversion Eval; subst source.
 exists (maxn width n). split.
 - exact (leq_trans Width (leq_maxl _ _)).
 - f_equal. apply rf_reference_word_resize; [exact Size|exact Width|exact (leq_trans Width (leq_maxl _ _))].
Qed.
Lemma rf_reference_word_base base : size base = 32%nat -> rf_reference_word_extension base (Gval (Fuint 32) base).
Proof.
 intro Size. exists 32%nat. split; [reflexivity|].
 unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
Qed.
Lemma rf_reference_word_true_mux_extension mm old (condition yes no : VarOrder.T) base input source :
 size base = 32%nat -> rf_reference_word_extension base input ->
 VM.find condition old = Some (Gval (Fuint 1) [::true]) ->
 VM.find yes old = Some input ->
 eval_hfexpr_with_memory mm (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 rf_reference_word_extension base source.
Proof.
 intros Size [width [Width Input]] Condition Yes Eval. subst input.
 cbn [eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 rewrite Condition in Eval. cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory] in Eval.
 change (is_zero [:: true]) with false in Eval. cbn in Eval.
 rewrite Yes in Eval.
 destruct (eval_type_of_expr (Eref (Eid no)) old) as [ty|]; [|discriminate].
 unfold extend_hvalue_as_type in Eval.
 destruct ty as [ground|element count|fields]; try discriminate.
 destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
 inversion Eval; subst source.
 exists (maxn width n). split.
 - exact (leq_trans Width (leq_maxl _ _)).
 - f_equal. apply rf_reference_word_resize; [exact Size|exact Width|exact (leq_trans Width (leq_maxl _ _))].
Qed.
Require Import X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation FormalGroundNodeEquation.
Lemma rf_reference_word_false_node offsets nodes node condition yes no invalid old current result base input :
 select_node_offsets offsets flat_statements = Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements = true ->
 List.In (node,@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
  (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) nodes ->
 size base = 32%nat -> rf_reference_word_extension base input ->
 VM.find condition old = Some (Gval (Fuint 1) [::false]) ->
 VM.find no old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find node result = Some value /\ rf_reference_word_extension base value.
Proof.
 intros Positions Safety Member Size Extended Condition Input Step.
 destruct (selected_node_safe_position flat_memories flat_statements offsets flat_statements
 nodes node _ Positions Safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false current result Position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some value) in Eval.
 pose proof (rf_reference_word_false_mux_extension flat_memories old condition yes no base input value Size Extended Condition Input Eval) as Out.
 exists value. split; [|exact Out].
 destruct Out as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg|exact Eval|reflexivity|exact Step].
Qed.

Lemma rf_reference_word_true_node offsets nodes node condition yes no invalid old current result base input :
 select_node_offsets offsets flat_statements = Some nodes ->
 selected_node_safety flat_memories flat_statements offsets flat_statements = true ->
 List.In (node,@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
  (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) nodes ->
 size base = 32%nat -> rf_reference_word_extension base input ->
 VM.find condition old = Some (Gval (Fuint 1) [::true]) ->
 VM.find yes old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find node result = Some value /\ rf_reference_word_extension base value.
Proof.
 intros Positions Safety Member Size Extended Condition Input Step.
 destruct (selected_node_safe_position flat_memories flat_statements offsets flat_statements
 nodes node _ Positions Safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false current result Position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some value) in Eval.
 pose proof (rf_reference_word_true_mux_extension flat_memories old condition yes no base input value Size Extended Condition Input Eval) as Out.
 exists value. split; [|exact Out].
 destruct Out as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg|exact Eval|reflexivity|exact Step].
Qed.
