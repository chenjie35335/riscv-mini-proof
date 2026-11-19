Require Import CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation FormalGroundNodeEquation.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition rf_writeback_nodes := [::(7931,joint_update_expr_7931);(7932,joint_update_expr_7932);(7933,joint_update_expr_7933);(7934,joint_update_expr_7934);(7935,joint_update_expr_7935);(7936,joint_update_expr_7936);(7937,joint_update_expr_7937);(7926,joint_update_expr_7926);(7929,joint_update_expr_7929);(7930,joint_update_expr_7930);(7927,joint_update_expr_7927);(7928,joint_update_expr_7928);(7898,joint_update_expr_7898);(7900,joint_update_expr_7900);(7902,joint_update_expr_7902);(7904,joint_update_expr_7904);(7897,joint_update_expr_7897);(7899,joint_update_expr_7899);(7901,joint_update_expr_7901);(7903,joint_update_expr_7903);(7889,joint_update_expr_7889);(7890,joint_update_expr_7890);(7891,joint_update_expr_7891);(7892,joint_update_expr_7892);(7893,joint_update_expr_7893);(7894,joint_update_expr_7894);(7895,joint_update_expr_7895);(7896,joint_update_expr_7896);(7888,joint_update_expr_7888);(7882,joint_update_expr_7882);(7883,joint_update_expr_7883);(7884,joint_update_expr_7884);(7885,joint_update_expr_7885);(7886,joint_update_expr_7886);(7887,joint_update_expr_7887)].
Lemma rf_writeback_member index : (index < 35)%coq_nat ->
 List.In (nth (0,joint_update_expr_7931) rf_writeback_nodes index) joint_update_expected_nodes.
Proof.
 intro Bound. apply (List.nth_error_In joint_update_expected_nodes (nth 0%nat [::965%nat;966%nat;967%nat;968%nat;969%nat;970%nat;971%nat;960%nat;963%nat;964%nat;961%nat;962%nat;953%nat;955%nat;957%nat;959%nat;952%nat;954%nat;956%nat;958%nat;944%nat;945%nat;946%nat;947%nat;948%nat;949%nat;950%nat;951%nat;943%nat;937%nat;938%nat;939%nat;940%nat;941%nat;942%nat] index)).
 do 35 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_writeback_node_step invalid old current result index value ground :
 (index < 35)%coq_nat ->
 eval_hfexpr_with_memory flat_memories (snd (nth (0,joint_update_expr_7931) rf_writeback_nodes index)) old old = Some value ->
 type_of_val value = Gtyp ground ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (fst (nth (0,joint_update_expr_7931) rf_writeback_nodes index)) result = Some value.
Proof.
 intros Bound Eval Typed Step.
 pose proof (rf_writeback_member index Bound) as Member.
 destruct (nth (0,joint_update_expr_7931) rf_writeback_nodes index) as [node expression] eqn:Entry.
 cbn [fst snd] in *.
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements
 joint_update_expected_nodes _ _ joint_update_node_positions joint_update_node_safety Member)
 as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |exact Typed|exact Step].
 do 35 (destruct index as [|index]; [cbn [rf_writeback_nodes nth] in Entry; inversion Entry; subst; exact Eval|]). lia.
Qed.
Theorem rf_writeback_decode_step invalid old current result low high :
 VM.find 7756 old = Some (Gval (Fuint 2) [::low;high]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7931 result = Some (Gval (Fuint 1) [::low && negb high]) /\
 VM.find 7933 result = Some (Gval (Fuint 1) [::negb low && high]) /\
 VM.find 7935 result = Some (Gval (Fuint 1) [::low && high]).
Proof.
 intros Mode Step. split; [|split].
 - apply (rf_writeback_node_step invalid old current result 0 _ (Fuint 1)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7931 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Mode. destruct low,high; reflexivity.
 - apply (rf_writeback_node_step invalid old current result 2 _ (Fuint 1)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7933 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Mode. destruct low,high; reflexivity.
 - apply (rf_writeback_node_step invalid old current result 4 _ (Fuint 1)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7935 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Mode. destruct low,high; reflexivity.
Qed.
From nbits Require Import NBits.
Lemma rf_writeback_signed_mux mm env (condition yes no : VarOrder.T) bit left right :
 size left = 33%nat -> size right = 33%nat ->
 VM.find condition env = Some (Gval (Fuint 1) [::bit]) ->
 VM.find yes env = Some (Gval (Fsint 33) left) ->
 VM.find no env = Some (Gval (Fsint 33) right) ->
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) env env =
 Some (Gval (Fsint 33) (if bit then left else right)).
Proof.
 intros LeftSize RightSize Condition Left Right.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Condition.
 destruct bit; cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory];
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite Left Right;
 cbn [option_map make_ftype_explicit extend_hvalue_as_type type_of_val ftype_mux fgtyp_mux adapt_hvalue_as_type];
 rewrite maxnn.
 - rewrite -LeftSize take_size. unfold sext_to,sext. rewrite subnn cats0. reflexivity.
 - rewrite -RightSize take_size. unfold sext_to,sext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_writeback_select_chain invalid s0 s1 s2 s3 s4 load_mode pc_mode csr_mode alu load pc csr :
 size alu = 33%nat -> size load = 33%nat -> size pc = 33%nat -> size csr = 33%nat ->
 VM.find 7931 s0 = Some (Gval (Fuint 1) [::load_mode]) ->
 VM.find 7904 s0 = Some (Gval (Fsint 33) load) ->
 VM.find 7926 s0 = Some (Gval (Fsint 33) alu) ->
 VM.find 7933 s1 = Some (Gval (Fuint 1) [::pc_mode]) ->
 VM.find 7929 s1 = Some (Gval (Fsint 33) pc) ->
 VM.find 7935 s2 = Some (Gval (Fuint 1) [::csr_mode]) ->
 VM.find 7930 s2 = Some (Gval (Fsint 33) csr) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 7937 s4 = Some (Gval (Fuint 33)
 (if csr_mode then csr else if pc_mode then pc else if load_mode then load else alu)).
Proof.
 intros AluSize LoadSize PcSize CsrSize LoadMode Load Alu PcMode Pc CsrMode Csr S1 S2 S3 S4.
 assert (A : VM.find 7932 s1 = Some (Gval (Fsint 33) (if load_mode then load else alu))).
 { apply (rf_writeback_node_step invalid s0 s0 s1 1 _ (Fsint 33)); [lia| |reflexivity|exact S1].
   exact (rf_writeback_signed_mux flat_memories s0 7931 7904 7926 load_mode load alu LoadSize AluSize LoadMode Load Alu). }
 assert (ASize : size (if load_mode then load else alu) = 33%nat).
 { destruct load_mode; assumption. }
 assert (B : VM.find 7934 s2 = Some (Gval (Fsint 33) (if pc_mode then pc else if load_mode then load else alu))).
 { apply (rf_writeback_node_step invalid s1 s1 s2 3 _ (Fsint 33)); [lia| |reflexivity|exact S2].
   exact (rf_writeback_signed_mux flat_memories s1 7933 7929 7932 pc_mode pc _ PcSize ASize PcMode Pc A). }
 assert (BSize : size (if pc_mode then pc else if load_mode then load else alu) = 33%nat).
 { destruct pc_mode; assumption. }
 assert (C : VM.find 7936 s3 = Some (Gval (Fsint 33) (if csr_mode then csr else if pc_mode then pc else if load_mode then load else alu))).
 { apply (rf_writeback_node_step invalid s2 s2 s3 5 _ (Fsint 33)); [lia| |reflexivity|exact S3].
   exact (rf_writeback_signed_mux flat_memories s2 7935 7930 7934 csr_mode csr _ CsrSize BSize CsrMode Csr B). }
 apply (rf_writeback_node_step invalid s3 s3 s4 6 _ (Fuint 33)); [lia| |reflexivity|exact S4].
 cbn [rf_writeback_nodes nth snd joint_update_expr_7937 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite C. reflexivity.
Qed.
Require Import StagedRegisterHold RegisterInvariants.
Lemma rf_writeback_mode_register : has_register 7756 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_writeback_select_from_mode invalid s0 s1 s2 s3 s4 s5 low high alu load pc csr :
 size alu = 33%nat -> size load = 33%nat -> size pc = 33%nat -> size csr = 33%nat ->
 VM.find 7756 s0 = Some (Gval (Fuint 2) [::low;high]) ->
 VM.find 7904 s1 = Some (Gval (Fsint 33) load) ->
 VM.find 7926 s1 = Some (Gval (Fsint 33) alu) ->
 VM.find 7929 s2 = Some (Gval (Fsint 33) pc) ->
 VM.find 7930 s3 = Some (Gval (Fsint 33) csr) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 VM.find 7937 s5 = Some (Gval (Fuint 33)
 (if high then if low then csr else pc else if low then load else alu)).
Proof.
 intros AluSize LoadSize PcSize CsrSize Mode Load Alu Pc Csr S1 S2 S3 S4 S5.
 assert (Mode1 : VM.find 7756 s1 = Some (Gval (Fuint 2) [::low;high])).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s0 s0 s1 flat_statements 7756 rf_writeback_mode_register S1). exact Mode. }
 assert (Mode2 : VM.find 7756 s2 = Some (Gval (Fuint 2) [::low;high])).
 { rewrite (staged_combinational_holds_registers invalid flat_memories s1 s1 s2 flat_statements 7756 rf_writeback_mode_register S2). exact Mode1. }
 destruct (rf_writeback_decode_step invalid s0 s0 s1 low high Mode S1) as [LoadMode _].
 destruct (rf_writeback_decode_step invalid s1 s1 s2 low high Mode1 S2) as [_ [PcMode _]].
 destruct (rf_writeback_decode_step invalid s2 s2 s3 low high Mode2 S3) as [_ [_ CsrMode]].
 pose proof (rf_writeback_select_chain invalid s1 s2 s3 s4 s5 (low && negb high) (negb low && high) (low && high)
 alu load pc csr AluSize LoadSize PcSize CsrSize LoadMode Load Alu PcMode Pc CsrMode Csr S2 S3 S4 S5) as Result.
 destruct low,high; exact Result.
Qed.
Theorem rf_writeback_unsigned_sources invalid old current result alu pc csr :
 VM.find 7752 old = Some (Gval (Fuint 32) alu) ->
 VM.find 7928 old = Some (Gval (Fuint 32) pc) ->
 VM.find 120 old = Some (Gval (Fuint 32) csr) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7926 result = Some (Gval (Fsint 33) (zext 1 alu)) /\
 VM.find 7929 result = Some (Gval (Fsint 33) (zext 1 pc)) /\
 VM.find 7930 result = Some (Gval (Fsint 33) (zext 1 csr)).
Proof.
 intros Alu Pc Csr Step. split; [|split].
 - apply (rf_writeback_node_step invalid old current result 7 _ (Fsint 33)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7926 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Alu. reflexivity.
 - apply (rf_writeback_node_step invalid old current result 8 _ (Fsint 33)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7929 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Pc. reflexivity.
 - apply (rf_writeback_node_step invalid old current result 9 _ (Fsint 33)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7930 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Csr. reflexivity.
Qed.
Require Import ReferencePCSequentialValues.
Theorem rf_writeback_return_pc invalid s0 s1 s2 pc :
 VM.find 7751 s0 = Some (Gval (Fuint 32) pc) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7928 s2 = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros Pc S1 S2.
 assert (Sum : VM.find 7927 s1 = Some (Gval (Fuint 33) (from_N 33 (to_N pc + 4)))).
 { apply (rf_writeback_node_step invalid s0 s0 s1 10 _ (Fuint 33)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7927 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Pc. reflexivity. }
 apply (rf_writeback_node_step invalid s1 s1 s2 11 _ (Fuint 32)); [lia| |reflexivity|exact S2].
 cbn [rf_writeback_nodes nth snd joint_update_expr_7928 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Sum. reflexivity.
Qed.
Theorem rf_writeback_return_pc_signed invalid s0 s1 s2 s3 pc :
 VM.find 7751 s0 = Some (Gval (Fuint 32) pc) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 7929 s3 = Some (Gval (Fsint 33) (zext 1 (reference_pc_plus_four pc))).
Proof.
 intros Pc S1 S2 S3.
 pose proof (rf_writeback_return_pc invalid s0 s1 s2 pc Pc S1 S2) as Return.
 apply (rf_writeback_node_step invalid s2 s2 s3 8 _ (Fsint 33)); [lia| |reflexivity|exact S3].
 cbn [rf_writeback_nodes nth snd joint_update_expr_7929 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Return. reflexivity.
Qed.
Require Import PipelinePCRelation.
Theorem rf_writeback_return_pc_from_pipeline invalid s0 s1 s2 s3 reference_pc :
 pipeline_pc_relation s0 ->
 VM.find 7947 s0 = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7331 s0 = Some (Gval (Fuint 32) reference_pc) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 VM.find 7929 s3 = Some (Gval (Fsint 33) (zext 1 (reference_pc_plus_four reference_pc))).
Proof.
 intros [pc [Size [Aligned [Reference Phase]]]] Active ReferencePc S1 S2 S3.
 rewrite ReferencePc in Reference. inversion Reference; subst pc.
 destruct Phase as [[Flag Commit]|[[Flag Rest]|[Flag Rest]]].
 - exact (rf_writeback_return_pc_signed invalid s0 s1 s2 s3 reference_pc Commit S1 S2 S3).
 - rewrite Active in Flag. discriminate.
 - rewrite Active in Flag. discriminate.
Qed.

Require Import RFPreviewEffect.
Theorem rf_writeback_port_from_mode invalid s0 s1 s2 s3 s4 s5 s6 low high alu load pc csr :
 size alu = 33%nat -> size load = 33%nat -> size pc = 33%nat -> size csr = 33%nat ->
 VM.find 7756 s0 = Some (Gval (Fuint 2) [::low;high]) ->
 VM.find 7904 s1 = Some (Gval (Fsint 33) load) ->
 VM.find 7926 s1 = Some (Gval (Fsint 33) alu) ->
 VM.find 7929 s2 = Some (Gval (Fsint 33) pc) ->
 VM.find 7930 s3 = Some (Gval (Fsint 33) csr) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 VM.find 786 s6 = Some (Gval (Fuint 32)
 (take 32 (if high then if low then csr else pc else if low then load else alu))).
Proof.
 intros AluSize LoadSize PcSize CsrSize Mode Load Alu Pc Csr S1 S2 S3 S4 S5 S6.
 pose proof (rf_writeback_select_from_mode invalid s0 s1 s2 s3 s4 s5 low high alu load pc csr
 AluSize LoadSize PcSize CsrSize Mode Load Alu Pc Csr S1 S2 S3 S4 S5) as Source.
 apply (rf_preview_data_port_exact invalid s5 s5 s6 33 _); [lia| |exact Source|exact S6].
 destruct high,low; assumption.
Qed.

Theorem rf_writeback_port_from_sources invalid s0 s1 s2 s3 s4 s5 s6 low high alu load pc csr :
 size alu = 32%nat -> size load = 33%nat -> size pc = 32%nat -> size csr = 32%nat ->
 VM.find 7756 s0 = Some (Gval (Fuint 2) [::low;high]) ->
 VM.find 7904 s1 = Some (Gval (Fsint 33) load) ->
 VM.find 7752 s0 = Some (Gval (Fuint 32) alu) ->
 VM.find 7928 s1 = Some (Gval (Fuint 32) pc) ->
 VM.find 120 s2 = Some (Gval (Fuint 32) csr) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 formal_value_iter invalid flat_memories s4 false s4 flat_statements = Some s5 ->
 formal_value_iter invalid flat_memories s5 false s5 flat_statements = Some s6 ->
 VM.find 786 s6 = Some (Gval (Fuint 32)
 (if high then if low then csr else pc else if low then take 32 load else alu)).
Proof.
 intros AluSize LoadSize PcSize CsrSize Mode Load Alu Pc Csr S1 S2 S3 S4 S5 S6.
 assert (A : VM.find 7926 s1 = Some (Gval (Fsint 33) (zext 1 alu))).
 { apply (rf_writeback_node_step invalid s0 s0 s1 7 _ (Fsint 33)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7926 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Alu. reflexivity. }
 assert (P : VM.find 7929 s2 = Some (Gval (Fsint 33) (zext 1 pc))).
 { apply (rf_writeback_node_step invalid s1 s1 s2 8 _ (Fsint 33)); [lia| |reflexivity|exact S2].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7929 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Pc. reflexivity. }
 assert (C : VM.find 7930 s3 = Some (Gval (Fsint 33) (zext 1 csr))).
 { apply (rf_writeback_node_step invalid s2 s2 s3 9 _ (Fsint 33)); [lia| |reflexivity|exact S3].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7930 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Csr. reflexivity. }
 assert (AZ : size (zext 1 alu) = 33%nat) by (rewrite size_zext AluSize;reflexivity).
 assert (PZ : size (zext 1 pc) = 33%nat) by (rewrite size_zext PcSize;reflexivity).
 assert (CZ : size (zext 1 csr) = 33%nat) by (rewrite size_zext CsrSize;reflexivity).
 pose proof (rf_writeback_port_from_mode invalid s0 s1 s2 s3 s4 s5 s6 low high (zext 1 alu) load (zext 1 pc) (zext 1 csr)
 AZ LoadSize PZ CZ Mode Load A P C S1 S2 S3 S4 S5 S6) as Result.
 assert (Low : forall word, size word = 32%nat -> take 32 (zext 1 word) = word).
 { intros word Size. unfold zext. rewrite take_cat Size ltnn subnn take0 cats0. reflexivity. }
 destruct high,low; cbn [andb] in Result; rewrite ?(Low csr CsrSize) ?(Low pc PcSize) ?(Low alu AluSize) in Result; exact Result.
Qed.
Lemma rf_writeback_signed_mux_widen mm env (condition yes no : VarOrder.T) bit width left right :
 (width <= 33)%coq_nat -> size left = width -> size right = 33%nat ->
 VM.find condition env = Some (Gval (Fuint 1) [::bit]) ->
 VM.find yes env = Some (Gval (Fsint width) left) ->
 VM.find no env = Some (Gval (Fsint 33) right) ->
 eval_hfexpr_with_memory mm
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T condition))
 (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) env env =
 Some (Gval (Fsint 33) (if bit then sext_to 33 left else right)).
Proof.
 intros Bound LeftSize RightSize Condition Left Right.
 assert (Max : maxn width 33 = 33%nat). { apply/maxn_idPr. apply/leP. exact Bound. }
 assert (TakeLeft : take 33 left = left). { apply take_oversize. rewrite LeftSize. apply/leP. exact Bound. }
 cbn [eval_hfexpr_with_memory eval_href_with_memory]. rewrite Condition.
 destruct bit; cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory];
 unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref]; rewrite Left Right;
 cbn [option_map make_ftype_explicit extend_hvalue_as_type type_of_val ftype_mux fgtyp_mux adapt_hvalue_as_type];
 rewrite Max.
 - rewrite TakeLeft. reflexivity.
 - change (is_zero [::false]) with true. cbn [andb]. rewrite (maxnC 33 width) Max. rewrite -RightSize take_size. unfold sext_to,sext. rewrite subnn cats0. reflexivity.
Qed.

Definition rf_load_branch_width index := nth 0%nat [::16%nat;8%nat;17%nat;9%nat] index.
Definition rf_load_branch_previous index := if index is O then 7888 else N.of_nat (7896+2*index)%nat.
Theorem rf_load_mux_step invalid old current result index enabled narrow previous :
 (index < 4)%coq_nat ->
 size narrow = rf_load_branch_width index -> size previous = 33%nat ->
 VM.find (N.of_nat (7897+2*index)%nat) old = Some (Gval (Fuint 1) [::enabled]) ->
 VM.find (N.of_nat (7890+2*index)%nat) old = Some (Gval (Fsint (rf_load_branch_width index)) narrow) ->
 VM.find (rf_load_branch_previous index) old = Some (Gval (Fsint 33) previous) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (N.of_nat (7898+2*index)%nat) result = Some (Gval (Fsint 33)
 (if enabled then sext_to 33 narrow else previous)).
Proof.
 intros Bound NarrowSize PreviousSize Gate Narrow Previous Step.
 destruct index as [|[|[|[|index]]]]; try lia.
 - apply (rf_writeback_node_step invalid old current result 12 _ (Fsint 33)); [lia| |reflexivity|exact Step].
   exact (rf_writeback_signed_mux_widen flat_memories old 7897 7890 7888 enabled 16 narrow previous
    ltac:(lia) NarrowSize PreviousSize Gate Narrow Previous).
 - apply (rf_writeback_node_step invalid old current result 13 _ (Fsint 33)); [lia| |reflexivity|exact Step].
   exact (rf_writeback_signed_mux_widen flat_memories old 7899 7892 7898 enabled 8 narrow previous
    ltac:(lia) NarrowSize PreviousSize Gate Narrow Previous).
 - apply (rf_writeback_node_step invalid old current result 14 _ (Fsint 33)); [lia| |reflexivity|exact Step].
   exact (rf_writeback_signed_mux_widen flat_memories old 7901 7894 7900 enabled 17 narrow previous
    ltac:(lia) NarrowSize PreviousSize Gate Narrow Previous).
 - apply (rf_writeback_node_step invalid old current result 15 _ (Fsint 33)); [lia| |reflexivity|exact Step].
   exact (rf_writeback_signed_mux_widen flat_memories old 7903 7896 7902 enabled 9 narrow previous
    ltac:(lia) NarrowSize PreviousSize Gate Narrow Previous).
Qed.

Theorem rf_load_decode_step invalid old current result low middle high :
 VM.find 7755 old = Some (Gval (Fuint 3) [::low;middle;high]) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 7897 result = Some (Gval (Fuint 1) [::negb low && middle && negb high]) /\
 VM.find 7899 result = Some (Gval (Fuint 1) [::low && middle && negb high]) /\
 VM.find 7901 result = Some (Gval (Fuint 1) [::negb low && negb middle && high]) /\
 VM.find 7903 result = Some (Gval (Fuint 1) [::low && negb middle && high]).
Proof.
 intros Mode Step. split; [|split; [|split]].
 - apply (rf_writeback_node_step invalid old current result 16 _ (Fuint 1)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7897 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Mode. destruct low,middle,high; reflexivity.
 - apply (rf_writeback_node_step invalid old current result 17 _ (Fuint 1)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7899 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Mode. destruct low,middle,high; reflexivity.
 - apply (rf_writeback_node_step invalid old current result 18 _ (Fuint 1)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7901 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Mode. destruct low,middle,high; reflexivity.
 - apply (rf_writeback_node_step invalid old current result 19 _ (Fuint 1)); [lia| |reflexivity|exact Step].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7903 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Mode. destruct low,middle,high; reflexivity.
Qed.

Lemma rf_load_mode_register : has_register 7755 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Theorem rf_load_decode_history invalid history limit low middle high :
 VM.find 7755 (history 0%nat) = Some (Gval (Fuint 3) [::low;middle;high]) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (time < limit)%coq_nat ->
 VM.find 7897 (history (S time)) = Some (Gval (Fuint 1) [::negb low && middle && negb high]) /\
 VM.find 7899 (history (S time)) = Some (Gval (Fuint 1) [::low && middle && negb high]) /\
 VM.find 7901 (history (S time)) = Some (Gval (Fuint 1) [::negb low && negb middle && high]) /\
 VM.find 7903 (history (S time)) = Some (Gval (Fuint 1) [::low && negb middle && high]).
Proof.
 intros Initial Steps.
 assert (Mode : forall time, (time <= limit)%coq_nat ->
   VM.find 7755 (history time) = Some (Gval (Fuint 3) [::low;middle;high])).
 { induction time as [|time IH]; intro Bound; [exact Initial|].
   rewrite (staged_combinational_holds_registers invalid flat_memories (history time) (history time) (history (S time)) flat_statements
    7755 rf_load_mode_register (Steps time ltac:(lia))).
   apply IH. lia. }
 intros time Bound.
 exact (rf_load_decode_step invalid (history time) (history time) (history (S time)) low middle high
 (Mode time ltac:(lia)) (Steps time Bound)).
Qed.

Theorem rf_load_extract_extend invalid s0 s1 s2 word :
 VM.find 7887 s0 = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 VM.find 7890 s2 = Some (Gval (Fsint 16) (take 16 word)) /\
 VM.find 7892 s2 = Some (Gval (Fsint 8) (take 8 word)) /\
 VM.find 7894 s2 = Some (Gval (Fsint 17) (zext 1 (take 16 word))) /\
 VM.find 7896 s2 = Some (Gval (Fsint 9) (zext 1 (take 8 word))).
Proof.
 intros Word S1 S2.
 assert (E7889 : VM.find 7889 s1 = Some (Gval (Fuint 16) (take 16 word))).
 { apply (rf_writeback_node_step invalid s0 s0 s1 20 _ (Fuint 16)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7889 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Word. unfold eval_unop.
   assert (Check : (0 <= 15 < 32)%nat = true) by (vm_compute;reflexivity).
   rewrite Check subn0 drop0. reflexivity. }
 assert (E7891 : VM.find 7891 s1 = Some (Gval (Fuint 8) (take 8 word))).
 { apply (rf_writeback_node_step invalid s0 s0 s1 22 _ (Fuint 8)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7891 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Word. unfold eval_unop.
   assert (Check : (0 <= 7 < 32)%nat = true) by (vm_compute;reflexivity).
   rewrite Check subn0 drop0. reflexivity. }
 assert (E7893 : VM.find 7893 s1 = Some (Gval (Fuint 16) (take 16 word))).
 { apply (rf_writeback_node_step invalid s0 s0 s1 24 _ (Fuint 16)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7893 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Word. unfold eval_unop.
   assert (Check : (0 <= 15 < 32)%nat = true) by (vm_compute;reflexivity).
   rewrite Check subn0 drop0. reflexivity. }
 assert (E7895 : VM.find 7895 s1 = Some (Gval (Fuint 8) (take 8 word))).
 { apply (rf_writeback_node_step invalid s0 s0 s1 26 _ (Fuint 8)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7895 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Word. unfold eval_unop.
   assert (Check : (0 <= 7 < 32)%nat = true) by (vm_compute;reflexivity).
   rewrite Check subn0 drop0. reflexivity. }
 split; [|split; [|split]].
 - apply (rf_writeback_node_step invalid s1 s1 s2 21 _ (Fsint 16)); [lia| |reflexivity|exact S2].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7890 eval_hfexpr_with_memory eval_href_with_memory]. rewrite E7889. reflexivity.
 - apply (rf_writeback_node_step invalid s1 s1 s2 23 _ (Fsint 8)); [lia| |reflexivity|exact S2].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7892 eval_hfexpr_with_memory eval_href_with_memory]. rewrite E7891. reflexivity.
 - apply (rf_writeback_node_step invalid s1 s1 s2 25 _ (Fsint 17)); [lia| |reflexivity|exact S2].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7894 eval_hfexpr_with_memory eval_href_with_memory]. rewrite E7893. reflexivity.
 - apply (rf_writeback_node_step invalid s1 s1 s2 27 _ (Fsint 9)); [lia| |reflexivity|exact S2].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7896 eval_hfexpr_with_memory eval_href_with_memory]. rewrite E7895. reflexivity.
Qed.
Lemma rf_load_mux_size bit width narrow previous :
 (width <= 33)%coq_nat -> size narrow = width -> size previous = 33%nat ->
 size (if bit then sext_to 33 narrow else previous) = 33%nat.
Proof.
 intros Bound Narrow Previous. destruct bit; [|exact Previous].
 unfold sext_to. rewrite size_sext addnC subnK; [reflexivity|].
 rewrite Narrow. apply/leP. exact Bound.
Qed.
Definition rf_load_selected half_signed byte_signed half_unsigned byte_unsigned whole half byte uhalf ubyte :=
 if byte_unsigned then sext_to 33 ubyte else
 if half_unsigned then sext_to 33 uhalf else
 if byte_signed then sext_to 33 byte else
 if half_signed then sext_to 33 half else whole.
Theorem rf_load_select_chain invalid s0 s1 s2 s3 s4 half_signed byte_signed half_unsigned byte_unsigned whole half byte uhalf ubyte :
 size whole = 33%nat -> size half = 16%nat -> size byte = 8%nat -> size uhalf = 17%nat -> size ubyte = 9%nat ->
 VM.find 7888 s0 = Some (Gval (Fsint 33) whole) ->
 VM.find 7890 s0 = Some (Gval (Fsint 16) half) ->
 VM.find 7897 s0 = Some (Gval (Fuint 1) [::half_signed]) ->
 VM.find 7892 s1 = Some (Gval (Fsint 8) byte) ->
 VM.find 7899 s1 = Some (Gval (Fuint 1) [::byte_signed]) ->
 VM.find 7894 s2 = Some (Gval (Fsint 17) uhalf) ->
 VM.find 7901 s2 = Some (Gval (Fuint 1) [::half_unsigned]) ->
 VM.find 7896 s3 = Some (Gval (Fsint 9) ubyte) ->
 VM.find 7903 s3 = Some (Gval (Fuint 1) [::byte_unsigned]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 7904 s4 = Some (Gval (Fsint 33)
 (rf_load_selected half_signed byte_signed half_unsigned byte_unsigned whole half byte uhalf ubyte)).
Proof.
 intros WholeSize HalfSize ByteSize UHalfSize UByteSize Whole Half HalfGate Byte ByteGate UHalf UHalfGate UByte UByteGate S1 S2 S3 S4.
 pose proof (rf_load_mux_step invalid s0 s0 s1 0 half_signed half whole ltac:(lia) HalfSize WholeSize HalfGate Half Whole S1) as A.
 pose proof (rf_load_mux_size half_signed 16 half whole ltac:(lia) HalfSize WholeSize) as ASize.
 pose proof (rf_load_mux_step invalid s1 s1 s2 1 byte_signed byte _ ltac:(lia) ByteSize ASize ByteGate Byte A S2) as B.
 pose proof (rf_load_mux_size byte_signed 8 byte _ ltac:(lia) ByteSize ASize) as BSize.
 pose proof (rf_load_mux_step invalid s2 s2 s3 2 half_unsigned uhalf _ ltac:(lia) UHalfSize BSize UHalfGate UHalf B S3) as C.
 pose proof (rf_load_mux_size half_unsigned 17 uhalf _ ltac:(lia) UHalfSize BSize) as CSize.
 exact (rf_load_mux_step invalid s3 s3 s4 3 byte_unsigned ubyte _ ltac:(lia) UByteSize CSize UByteGate UByte C S4).
Qed.

Theorem rf_load_from_history invalid history low middle high word raw :
 size word = 32%nat -> size raw = 32%nat ->
 VM.find 7755 (history 0%nat) = Some (Gval (Fuint 3) [::low;middle;high]) ->
 VM.find 82 (history 1%nat) = Some (Gval (Fuint 32) raw) ->
 (forall i, (i <= 3)%coq_nat -> VM.find 7887 (history i) = Some (Gval (Fuint 32) word)) ->
 (forall i, (i < 6)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7904 (history 6%nat) = Some (Gval (Fsint 33)
 (rf_load_selected (negb low && middle && negb high) (low && middle && negb high)
 (negb low && negb middle && high) (low && negb middle && high)
 (zext 1 raw) (take 16 word) (take 8 word) (zext 1 (take 16 word)) (zext 1 (take 8 word)))).
Proof.
 intros WordSize RawSize Mode Raw Words Steps.
 assert (Whole : VM.find 7888 (history 2%nat) = Some (Gval (Fsint 33) (zext 1 raw))).
 { apply (rf_writeback_node_step invalid (history 1%nat) (history 1%nat) (history 2%nat) 28 _ (Fsint 33)); [lia| |reflexivity|exact (Steps 1%nat ltac:(lia))].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7888 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Raw. reflexivity. }
 destruct (rf_load_extract_extend invalid (history 0%nat) (history 1%nat) (history 2%nat) word (Words 0%nat ltac:(lia)) (Steps 0%nat ltac:(lia)) (Steps 1%nat ltac:(lia))) as [Half _].
 destruct (rf_load_extract_extend invalid (history 1%nat) (history 2%nat) (history 3%nat) word (Words 1%nat ltac:(lia)) (Steps 1%nat ltac:(lia)) (Steps 2%nat ltac:(lia))) as [_ [Byte _]].
 destruct (rf_load_extract_extend invalid (history 2%nat) (history 3%nat) (history 4%nat) word (Words 2%nat ltac:(lia)) (Steps 2%nat ltac:(lia)) (Steps 3%nat ltac:(lia))) as [_ [_ [UHalf _]]].
 destruct (rf_load_extract_extend invalid (history 3%nat) (history 4%nat) (history 5%nat) word (Words 3%nat ltac:(lia)) (Steps 3%nat ltac:(lia)) (Steps 4%nat ltac:(lia))) as [_ [_ [_ UByte]]].
 destruct (rf_load_decode_history invalid history 6%nat low middle high Mode Steps 1%nat ltac:(lia)) as [HalfGate _].
 destruct (rf_load_decode_history invalid history 6%nat low middle high Mode Steps 2%nat ltac:(lia)) as [_ [ByteGate _]].
 destruct (rf_load_decode_history invalid history 6%nat low middle high Mode Steps 3%nat ltac:(lia)) as [_ [_ [UHalfGate _]]].
 destruct (rf_load_decode_history invalid history 6%nat low middle high Mode Steps 4%nat ltac:(lia)) as [_ [_ [_ UByteGate]]].
 assert (WholeSize : size (zext 1 raw) = 33%nat) by (rewrite size_zext RawSize;reflexivity).
 assert (HalfSize : size (take 16 word) = 16%nat) by (rewrite size_take WordSize;reflexivity).
 assert (ByteSize : size (take 8 word) = 8%nat) by (rewrite size_take WordSize;reflexivity).
 assert (UHalfSize : size (zext 1 (take 16 word)) = 17%nat) by (rewrite size_zext HalfSize;reflexivity).
 assert (UByteSize : size (zext 1 (take 8 word)) = 9%nat) by (rewrite size_zext ByteSize;reflexivity).
 exact (rf_load_select_chain invalid (history 2%nat) (history 3%nat) (history 4%nat) (history 5%nat) (history 6%nat)
 _ _ _ _ _ _ _ _ _ WholeSize HalfSize ByteSize UHalfSize UByteSize
 Whole Half HalfGate Byte ByteGate UHalf UHalfGate UByte UByteGate
 (Steps 2%nat ltac:(lia)) (Steps 3%nat ltac:(lia)) (Steps 4%nat ltac:(lia)) (Steps 5%nat ltac:(lia))).
Qed.

Theorem rf_load_address_shift invalid s0 s1 s2 s3 s4 b0 b1 rest raw :
 VM.find 7752 s0 = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 82 s3 = Some (Gval (Fuint 32) raw) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements = Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements = Some s4 ->
 VM.find 7887 s4 = Some (Gval (Fuint 32)
 (zext_to 32 (drop ((if b1 then 16 else 0)+(if b0 then 8 else 0))%nat raw))).
Proof.
 intros Address Raw S1 S2 S3 S4.
 assert (E7882 : VM.find 7882 s1 = Some (Gval (Fuint 1) [::b1])).
 { apply (rf_writeback_node_step invalid s0 s0 s1 29 _ (Fuint 1)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7882 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Address. destruct rest; destruct b0,b1; vm_compute; reflexivity. }
 assert (E7884 : VM.find 7884 s1 = Some (Gval (Fuint 1) [::b0])).
 { apply (rf_writeback_node_step invalid s0 s0 s1 31 _ (Fuint 1)); [lia| |reflexivity|exact S1].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7884 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite Address. destruct rest; destruct b0,b1; vm_compute; reflexivity. }
 assert (E7883 : VM.find 7883 s2 = Some (Gval (Fuint 8) [::false;false;false;false;b1;false;false;false])).
 { apply (rf_writeback_node_step invalid s1 s1 s2 30 _ (Fuint 8)); [lia| |reflexivity|exact S2].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7883 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite E7882. destruct rest; destruct b0,b1; vm_compute; reflexivity. }
 assert (E7885 : VM.find 7885 s2 = Some (Gval (Fuint 4) [::false;false;false;b0])).
 { apply (rf_writeback_node_step invalid s1 s1 s2 32 _ (Fuint 4)); [lia| |reflexivity|exact S2].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7885 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite E7884. destruct rest; destruct b0,b1; vm_compute; reflexivity. }
 assert (E7886 : VM.find 7886 s3 = Some (Gval (Fuint 8) [::false;false;false;b0;b1;false;false;false])).
 { apply (rf_writeback_node_step invalid s2 s2 s3 33 _ (Fuint 8)); [lia| |reflexivity|exact S3].
   cbn [rf_writeback_nodes nth snd joint_update_expr_7886 eval_hfexpr_with_memory eval_href_with_memory].
   rewrite E7883 E7885. destruct rest; destruct b0,b1; vm_compute; reflexivity. }
 apply (rf_writeback_node_step invalid s3 s3 s4 34 _ (Fuint 32)); [lia| |reflexivity|exact S4].
 cbn [rf_writeback_nodes nth snd joint_update_expr_7887 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Raw E7886. destruct b0,b1; reflexivity.
Qed.
Lemma rf_load_address_register : has_register 7752 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Definition rf_load_shift raw b0 b1 :=
 zext_to 32 (drop ((if b1 then 16 else 0)+(if b0 then 8 else 0))%nat raw).
Lemma rf_load_shift_size raw b0 b1 : size raw = 32%nat -> size (rf_load_shift raw b0 b1) = 32%nat.
Proof.
 intro Size. unfold rf_load_shift,zext_to. rewrite size_zext addnC subnK; [reflexivity|].
 rewrite size_drop Size. apply leq_subr.
Qed.
Definition rf_load_result low middle high raw b0 b1 :=
 let word := rf_load_shift raw b0 b1 in
 rf_load_selected (negb low && middle && negb high) (low && middle && negb high)
 (negb low && negb middle && high) (low && negb middle && high)
 (zext 1 raw) (take 16 word) (take 8 word) (zext 1 (take 16 word)) (zext 1 (take 8 word)).
Theorem rf_load_from_address_history invalid history low middle high b0 b1 rest raw :
 size raw = 32%nat ->
 VM.find 7755 (history 0%nat) = Some (Gval (Fuint 3) [::low;middle;high]) ->
 VM.find 7752 (history 0%nat) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 (forall i, (i <= 9)%coq_nat -> VM.find 82 (history i) = Some (Gval (Fuint 32) raw)) ->
 (forall i, (i < 10)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7904 (history 10%nat) = Some (Gval (Fsint 33) (rf_load_result low middle high raw b0 b1)).
Proof.
 intros RawSize Mode Address Raw Steps.
 assert (Held : forall i, (i <= 10)%coq_nat ->
 VM.find 7755 (history i) = Some (Gval (Fuint 3) [::low;middle;high]) /\
 VM.find 7752 (history i) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { induction i as [|i IH]; intro Bound; [split;assumption|].
   destruct (IH ltac:(lia)) as [M A]. split.
   - rewrite (staged_combinational_holds_registers invalid flat_memories (history i) (history i) (history (S i)) flat_statements
     7755 rf_load_mode_register (Steps i ltac:(lia))). exact M.
   - rewrite (staged_combinational_holds_registers invalid flat_memories (history i) (history i) (history (S i)) flat_statements
     7752 rf_load_address_register (Steps i ltac:(lia))). exact A. }
 assert (Shifted : forall i, (i <= 3)%coq_nat ->
 VM.find 7887 (history (4+i)%nat) = Some (Gval (Fuint 32) (rf_load_shift raw b0 b1))).
 { intros i Bound. destruct (Held i ltac:(lia)) as [_ A].
   rewrite !addSn add0n.
   exact (rf_load_address_shift invalid (history i) (history (S i)) (history (S (S i)))
    (history (S (S (S i)))) (history (S (S (S (S i))))) b0 b1 rest raw A
    (Raw (S (S (S i))) ltac:(lia)) (Steps i ltac:(lia)) (Steps (S i) ltac:(lia))
    (Steps (S (S i)) ltac:(lia)) (Steps (S (S (S i))) ltac:(lia))). }
 destruct (Held 4%nat ltac:(lia)) as [Mode4 _].
 exact (rf_load_from_history invalid (fun i => history (4+i)%nat) low middle high (rf_load_shift raw b0 b1) raw
 (rf_load_shift_size raw b0 b1 RawSize) RawSize Mode4 (Raw 5%nat ltac:(lia)) Shifted
 (fun i Bound => Steps (4+i)%nat ltac:(rewrite !addSn add0n;lia))).
Qed.
Require Import JointUpdateConnectionCertificates FormalDeclaredConnection.
Lemma rf_load_raw_register : has_register 9222 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_load_adapt32 word : size word = 32%nat ->
 adapt_hvalue_as_type (Gval (Fuint 32) word) (Gtyp (Fuint 32)) = Some (Gval (Fuint 32) word).
Proof.
 intro Size. cbn [adapt_hvalue_as_type]. rewrite -Size take_size.
 unfold zext_to,zext. rewrite subnn cats0. reflexivity.
Qed.
Theorem rf_load_raw_connection second invalid old current result word :
 size word = 32%nat ->
 VM.find (if second then 41 else 9222) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (if second then 82 else 41) result = Some (Gval (Fuint 32) word).
Proof.
 intros Size Source Step. destruct second.
 - eapply (declared_connection_value 59 flat_statements joint_update_connection_82_decl joint_update_connection_82_mid joint_update_connection_82_tail
   82 41 32 (Gval (Fuint 32) word));
   [exact joint_update_connection_82_position|exact joint_update_connection_82_split|exact joint_update_connection_82_straight|exact joint_update_connection_82_mid_safe|exact joint_update_connection_82_tail_safe|
   exact joint_update_connection_82_nonregister|reflexivity|exact Source|apply rf_load_adapt32;exact Size|exact Step].
 - eapply (declared_connection_value 18 flat_statements joint_update_connection_41_decl joint_update_connection_41_mid joint_update_connection_41_tail
   41 9222 32 (Gval (Fuint 32) word));
   [exact joint_update_connection_41_position|exact joint_update_connection_41_split|exact joint_update_connection_41_straight|exact joint_update_connection_41_mid_safe|exact joint_update_connection_41_tail_safe|
   exact joint_update_connection_41_nonregister|reflexivity|exact Source|apply rf_load_adapt32;exact Size|exact Step].
Qed.
Theorem rf_load_raw_history invalid history limit word :
 size word = 32%nat ->
 VM.find 9222 (history 0%nat) = Some (Gval (Fuint 32) word) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (S (S time) <= limit)%coq_nat ->
 VM.find 82 (history (S (S time))) = Some (Gval (Fuint 32) word).
Proof.
 intros Size Initial Steps.
 assert (Held : forall i, (i <= limit)%coq_nat -> VM.find 9222 (history i) = Some (Gval (Fuint 32) word)).
 { induction i as [|i IH]; intro Bound; [exact Initial|].
   rewrite (staged_combinational_holds_registers invalid flat_memories (history i) (history i) (history (S i)) flat_statements
   9222 rf_load_raw_register (Steps i ltac:(lia))). apply IH. lia. }
 intros time Bound.
 pose proof (rf_load_raw_connection false invalid (history time) (history time) (history (S time)) word
 Size (Held time ltac:(lia)) (Steps time ltac:(lia))) as First.
 exact (rf_load_raw_connection true invalid (history (S time)) (history (S time)) (history (S (S time))) word
 Size First (Steps (S time) ltac:(lia))).
Qed.
Theorem rf_load_from_register_history invalid history low middle high b0 b1 rest raw :
 size raw = 32%nat ->
 VM.find 7755 (history 0%nat) = Some (Gval (Fuint 3) [::low;middle;high]) ->
 VM.find 7752 (history 0%nat) = Some (Gval (Fuint 32) (b0::b1::rest)) ->
 VM.find 9222 (history 0%nat) = Some (Gval (Fuint 32) raw) ->
 (forall i, (i < 12)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 VM.find 7904 (history 12%nat) = Some (Gval (Fsint 33) (rf_load_result low middle high raw b0 b1)).
Proof.
 intros Size Mode Address Raw Steps.
 assert (Held : forall node, has_register node flat_statements = true ->
   VM.find node (history 2%nat) = VM.find node (history 0%nat)).
 { intros node Register.
   rewrite (staged_combinational_holds_registers invalid flat_memories (history 1%nat) (history 1%nat) (history 2%nat) flat_statements
   node Register (Steps 1%nat ltac:(lia))).
   exact (staged_combinational_holds_registers invalid flat_memories (history 0%nat) (history 0%nat) (history 1%nat) flat_statements
   node Register (Steps 0%nat ltac:(lia))). }
 assert (Mode2 : VM.find 7755 (history 2%nat) = Some (Gval (Fuint 3) [::low;middle;high])).
 { rewrite (Held 7755 rf_load_mode_register). exact Mode. }
 assert (Address2 : VM.find 7752 (history 2%nat) = Some (Gval (Fuint 32) (b0::b1::rest))).
 { rewrite (Held 7752 rf_load_address_register). exact Address. }
 apply (rf_load_from_address_history invalid (fun i => history (S (S i))) low middle high b0 b1 rest raw
 Size Mode2 Address2).
 - intros i Bound. exact (rf_load_raw_history invalid history 12%nat raw Size Raw Steps i ltac:(lia)).
 - intros i Bound. exact (Steps (S (S i)) ltac:(lia)).
Qed.
