Require Import CoreSocModel ComparisonNodes UIntResizeRoundtrip.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition fetch_pc_extension (base : bits) value :=
 exists width, (33 <= width)%nat /\ value = Gval (Fuint width) (zext_to width base).
Lemma fetch_pc_resize base width target :
 size base = 33%nat -> (33 <= width)%nat -> (33 <= target)%nat ->
 zext_to target (take target (zext_to width base)) = zext_to target base.
Proof.
 intros Size Width Target.
 assert (Take : take width base = base).
 { apply take_oversize. rewrite Size. exact Width. }
 rewrite <- Take at 1.
 exact (resize_uint_roundtrip_widen 33 target width base Size Target Width).
Qed.
Lemma fetch_pc_false_mux_extension mm old (condition yes no : VarOrder.T) base input source :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find condition old = Some (Gval (Fuint 1) [::false]) ->
 VM.find no old = Some input ->
 eval_hfexpr_with_memory mm (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 fetch_pc_extension base source.
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
 - f_equal. apply fetch_pc_resize; [exact Size|exact Width|exact (leq_trans Width (leq_maxl _ _))].
Qed.
Definition fetch_pc_plus_four (pc : bits) : bits := take 33 (from_N 34 (to_N pc + 4)).
Lemma fetch_pc_plus_four_size pc : size (fetch_pc_plus_four pc) = 33%nat.
Proof. unfold fetch_pc_plus_four. rewrite size_take size_from_N. reflexivity. Qed.
Lemma fetch_pc_base_extension base : size base = 33%nat -> fetch_pc_extension base (Gval (Fuint 33) base).
Proof.
 intro Size. exists 33%nat. split; [reflexivity|].
 unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
Qed.
Require Import FormalPCIncrementNodes FormalSuccessfulNodeEvaluation FormalTypedNodeEquation FormalStalledPC FormalPCIncrementHistory FormalPCChoiceNodes FormalUnstalledPC FormalLocalHistory FetchPCCommitSource FormalPCRegister.
Lemma fetch_pc_increment_exact invalid s0 s1 s2 pc :
 VM.find 7768 s0 = Some (Gval (Fuint 33) pc) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 VM.find 7770 s2 = Some (Gval (Fuint 33) (fetch_pc_plus_four pc)).
Proof.
 intros PC S1 S2.
 assert (Middle : VM.find 7769 s1 = Some (Gval (Fuint 34) (from_N 34 (to_N pc + 4)))).
 { eapply pc_normal_node_7769; [|reflexivity|exact S1].
   cbn [pc_normal_expr_7769 eval_hfexpr_with_memory eval_href_with_memory]. rewrite PC. reflexivity. }
 eapply pc_normal_node_7770; [|reflexivity|exact S2].
 cbn [pc_normal_expr_7770 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Middle. reflexivity.
Qed.
Lemma fetch_pc_sequential_7777 invalid old current result base input :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find 7776 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7770 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7777 result = Some value /\ fetch_pc_extension base value.
Proof.
 intros Size Ext Cond Input Step.
 destruct (formal_successful_node_evaluation 8283 flat_statements pc_choice_7777_tail 7777 pc_choice_7777_expr invalid flat_memories old false current result pc_choice_7777_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7777_expr old old = Some value) in Eval.
 pose proof (fetch_pc_false_mux_extension flat_memories old 7776 7768 7770 base input value Size Ext Cond Input Eval) as Extended.
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact pc_choice_7777_position|exact pc_choice_7777_suffix|exact pc_choice_7777_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Lemma fetch_pc_sequential_7778 invalid old current result base input :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find 7773 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7777 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7778 result = Some value /\ fetch_pc_extension base value.
Proof.
 intros Size Ext Cond Input Step.
 destruct (formal_successful_node_evaluation 8284 flat_statements pc_choice_7778_tail 7778 pc_choice_7778_expr invalid flat_memories old false current result pc_choice_7778_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7778_expr old old = Some value) in Eval.
 pose proof (fetch_pc_false_mux_extension flat_memories old 7773 7775 7777 base input value Size Ext Cond Input Eval) as Extended.
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact pc_choice_7778_position|exact pc_choice_7778_suffix|exact pc_choice_7778_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Lemma fetch_pc_sequential_7779 invalid old current result base input :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find 7771 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7778 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7779 result = Some value /\ fetch_pc_extension base value.
Proof.
 intros Size Ext Cond Input Step.
 destruct (formal_successful_node_evaluation 8285 flat_statements pc_choice_7779_tail 7779 pc_choice_7779_expr invalid flat_memories old false current result pc_choice_7779_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7779_expr old old = Some value) in Eval.
 pose proof (fetch_pc_false_mux_extension flat_memories old 7771 130 7778 base input value Size Ext Cond Input Eval) as Extended.
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact pc_choice_7779_position|exact pc_choice_7779_suffix|exact pc_choice_7779_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Lemma fetch_pc_sequential_7780 invalid old current result base input :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find 128 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7779 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7780 result = Some value /\ fetch_pc_extension base value.
Proof.
 intros Size Ext Cond Input Step.
 destruct (formal_successful_node_evaluation 8286 flat_statements pc_choice_7780_tail 7780 pc_choice_7780_expr invalid flat_memories old false current result pc_choice_7780_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_choice_7780_expr old old = Some value) in Eval.
 pose proof (fetch_pc_false_mux_extension flat_memories old 128 129 7779 base input value Size Ext Cond Input Eval) as Extended.
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact pc_choice_7780_position|exact pc_choice_7780_suffix|exact pc_choice_7780_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Lemma fetch_pc_sequential_7781 invalid old current result base input :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find 7765 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7780 old = Some input ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 7781 result = Some value /\ fetch_pc_extension base value.
Proof.
 intros Size Ext Cond Input Step.
 destruct (formal_successful_node_evaluation 8287 flat_statements pc_selected_tail 7781 pc_selected_expr invalid flat_memories old false current result pc_selected_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories pc_selected_expr old old = Some value) in Eval.
 pose proof (fetch_pc_false_mux_extension flat_memories old 7765 7768 7780 base input value Size Ext Cond Input Eval) as Extended.
 exists value. split; [|exact Extended].
 destruct Extended as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact pc_selected_position|exact pc_selected_suffix|exact pc_selected_nonregister|exact Eval|reflexivity|exact Step].
Qed.
Theorem fetch_pc_sequential_after_seven invalid s0 s1 s2 s3 s4 s5 s6 s7 pc :
 VM.find 7768 s0 = Some (Gval (Fuint 33) pc) ->
 VM.find 7776 s2 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 s3 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7771 s4 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s5 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7765 s6 = Some (Gval (Fuint 1) [::false]) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 -> formal_flat_local_step invalid s5 s6 ->
 formal_flat_local_step invalid s6 s7 ->
 exists value, VM.find 7781 s7 = Some value /\ fetch_pc_extension (fetch_pc_plus_four pc) value.
Proof.
 intros PC C2 C3 C4 C5 C6 S1 S2 S3 S4 S5 S6 S7.
 pose proof (fetch_pc_plus_four_size pc) as Size.
 pose proof (fetch_pc_increment_exact invalid s0 s1 s2 pc PC S1 S2) as V2.
 pose proof (fetch_pc_base_extension _ Size) as E2.
 destruct (fetch_pc_sequential_7777 invalid s2 s2 s3 _ _ Size E2 C2 V2 S3) as [v3 [V3 E3]].
 destruct (fetch_pc_sequential_7778 invalid s3 s3 s4 _ _ Size E3 C3 V3 S4) as [v4 [V4 E4]].
 destruct (fetch_pc_sequential_7779 invalid s4 s4 s5 _ _ Size E4 C4 V4 S5) as [v5 [V5 E5]].
 destruct (fetch_pc_sequential_7780 invalid s5 s5 s6 _ _ Size E5 C5 V5 S6) as [v6 [V6 E6]].
 exact (fetch_pc_sequential_7781 invalid s6 s6 s7 _ _ Size E6 C6 V6 S7).
Qed.
Lemma fetch_pc_sequential_commit invalid old current result pc base input :
 size base = 33%nat -> fetch_pc_extension base input ->
 VM.find 7768 old = Some (Gval (Fuint 33) pc) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7781 old = Some input ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7768 result = Some (Gval (Fuint 33) base).
Proof.
 intros Size Ext PC Reset Input Step.
 destruct (fetch_pc_formal_commit_source invalid old current result _ PC (Logic.eq_refl _) Step)
 as [source [value [Eval [Adapt Value]]]].
 pose proof (fetch_pc_false_mux_extension flat_memories old 65 7767 7781 base input source Size Ext Reset Input Eval) as Source.
 destruct Source as [width [Width Source]]. subst source.
 cbn [adapt_hvalue_as_type] in Adapt. rewrite (fetch_pc_resize base width 33 Size Width (leqnn _)) in Adapt.
 unfold zext_to, zext in Adapt. rewrite Size subnn cats0 in Adapt.
 inversion Adapt; subst value. exact Value.
Qed.
Theorem fetch_pc_sequential_seven_and_commit invalid s0 s1 s2 s3 s4 s5 s6 s7 result pc :
 VM.find 7768 s0 = Some (Gval (Fuint 33) pc) ->
 VM.find 7776 s2 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7773 s3 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7771 s4 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 128 s5 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7765 s6 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 65 s7 = Some (Gval (Fuint 1) [::false]) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 formal_flat_local_step invalid s2 s3 -> formal_flat_local_step invalid s3 s4 ->
 formal_flat_local_step invalid s4 s5 -> formal_flat_local_step invalid s5 s6 ->
 formal_flat_local_step invalid s6 s7 ->
 formal_value_iter invalid flat_memories s7 true s7 flat_statements = Some result ->
 VM.find 7768 result = Some (Gval (Fuint 33) (fetch_pc_plus_four pc)).
Proof.
 intros PC C2 C3 C4 C5 C6 Reset S1 S2 S3 S4 S5 S6 S7 Commit.
 destruct (fetch_pc_sequential_after_seven invalid s0 s1 s2 s3 s4 s5 s6 s7 pc PC C2 C3 C4 C5 C6 S1 S2 S3 S4 S5 S6 S7) as [value [Value Ext]].
 assert (PC7 : VM.find 7768 s7 = Some (Gval (Fuint 33) pc)).
 { rewrite (pc_register_combinational_hold _ _ _ _ S7)
 (pc_register_combinational_hold _ _ _ _ S6) (pc_register_combinational_hold _ _ _ _ S5)
 (pc_register_combinational_hold _ _ _ _ S4) (pc_register_combinational_hold _ _ _ _ S3)
 (pc_register_combinational_hold _ _ _ _ S2) (pc_register_combinational_hold _ _ _ _ S1). exact PC. }
 exact (fetch_pc_sequential_commit invalid s7 s7 result pc _ value (fetch_pc_plus_four_size pc) Ext PC7 Reset Value Commit).
Qed.
Print Assumptions fetch_pc_sequential_seven_and_commit.
