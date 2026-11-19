Require Import CoreSocModel ComparisonNodes JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalGroundNodeEquation RFPreviewEffect.
Require Import RFReadForwarding.
Require Import RFWritebackSelection RFReferenceWriteEffect FormalSuccessfulNodeEvaluation FormalTypedNodeEquation FormalObservedHistory FormalLocalHistory JointUpdateBoundaryHistory RFReadPorts RFNonAluReset CycleView.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_signed_low_word word value := exists width raw,
 value=Gval(Fsint width)raw /\size raw=width /\(32<=width)%nat /\take 32 raw=word.
Lemma rf_signed_low_resize word value width :rf_signed_low_word word value ->
 (forall source raw,value=Gval(Fsint source)raw ->(source<=width)%nat) ->
 exists adapted,adapt_hvalue_as_type value(Gtyp(Fsint width))=Some adapted /\rf_signed_low_word word adapted.
Proof.
 intros[source[raw[Value[Size[Wide Low]]]]] Width. subst value.
 specialize(Width source raw (Logic.eq_refl _)).
 exists(Gval(Fsint width)(sext_to width(take width raw))). split;[reflexivity|].
 exists width,(sext_to width(take width raw)). split;[reflexivity|].
 assert(Take:take width raw=raw)by(apply take_oversize;rewrite Size;exact Width).
 rewrite Take. split.
 - unfold sext_to. rewrite size_sext Size. exact(subnKC Width).
 - split;[exact(leq_trans Wide Width)|]. unfold sext_to,sext. rewrite take_cat.
 destruct(ltnP 32(size raw))as[Strict|Bound];[exact Low|].
 assert(Equal:size raw=32%nat)by(apply/eqP;rewrite eqn_leq;apply/andP;split;[exact Bound|rewrite Size;exact Wide]).
 rewrite Equal subnn take0 cats0. rewrite -Low. symmetry;apply take_oversize;rewrite Equal;reflexivity.
Qed.
Lemma rf_writeback_signed_selected node condition yes no invalid old result selected word :
 List.In(node,@Emux VarOrder.T(@Eref VarOrder.T(@Eid VarOrder.T condition))(@Eref VarOrder.T(@Eid VarOrder.T yes))(@Eref VarOrder.T(@Eid VarOrder.T no)))joint_update_expected_nodes ->
 VM.find condition old=Some(Gval(Fuint 1)[::false]) ->
 VM.find no old=Some selected ->rf_signed_low_word word selected ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 exists value,VM.find node result=Some value /\rf_signed_low_word word value.
Proof.
 intros Member Condition Selected [width[raw[Value[Size[Wide Low]]]]] Step. subst selected.
 destruct(selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes node _ joint_update_node_positions joint_update_node_safety Member)as[count[tail[Position[Safe Nonreg]]]].
 destruct(formal_successful_node_evaluation count flat_statements tail node _ invalid flat_memories old false old result Position Step)as[value Eval].
 pose proof Eval as Original.
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]in Eval. rewrite Condition in Eval.
 cbn in Eval;rewrite Selected in Eval;
 destruct(eval_type_of_expr _)as[typ|]eqn:Branch;try discriminate;
 unfold extend_hvalue_as_type in Eval;destruct typ as[ground|elt length|fields];try discriminate;
 destruct ground;cbn[type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type]in Eval;try discriminate;
 inversion Eval;subst value.
 all: eexists;split;[eapply formal_combinational_known_ground_node;[exact Position|exact Safe|exact Nonreg|exact Original|reflexivity|exact Step]|].
 all: destruct(rf_signed_low_resize word (Gval(Fsint width)raw) (maxn width n))as[adapted[Adapt Result]].
 all: try (exists width,raw;repeat split;assumption).
 all: try (intros source bits Equal;inversion Equal;subst;apply leq_maxl).
 all: cbn[adapt_hvalue_as_type]in Adapt;inversion Adapt;subst;exact Result.
Qed.
Theorem rf_alu_writeback_history invalid history limit word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::false;false])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 7752(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 786(history t)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Modes Alus Steps t Lower Upper.
 assert (Guards:forall u,(1<=u)%coq_nat ->(u<=limit)%coq_nat ->
 VM.find 7931(history u)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 7933(history u)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 7935(history u)=Some(Gval(Fuint 1)[::false])).
 { intros [|u] Lo Hi;[lia|]. exact(rf_writeback_decode_step invalid(history u)(history u)(history(S u))false false(Modes u ltac:(lia))(Steps u ltac:(lia))). }
 assert(A:VM.find 7926(history(Nat.sub t 5)%nat)=Some(Gval(Fsint 33)(zext 1 word))).
 { replace(Nat.sub t 5)%nat with(S(Nat.sub t 6))by lia.
 apply(rf_writeback_node_step invalid(history(Nat.sub t 6)%nat)(history(Nat.sub t 6)%nat)(history(S(Nat.sub t 6)))7 _ (Fsint 33));[lia| |reflexivity|apply Steps;lia].
 cbn[rf_writeback_nodes nth snd joint_update_expr_7926 eval_hfexpr_with_memory eval_href_with_memory]. rewrite Alus;[reflexivity|lia]. }
 assert(L:rf_signed_low_word word(Gval(Fsint 33)(zext 1 word))).
 { exists 33%nat,(zext 1 word). repeat split;try reflexivity.
 - rewrite size_zext Size;reflexivity.
 - unfold zext. rewrite take_cat Size ltnn subnn take0 cats0;reflexivity. }
 destruct(Guards(Nat.sub t 5)%nat ltac:(lia)ltac:(lia))as[G1 _].
 destruct(rf_writeback_signed_selected 7932 7931 7904 7926 invalid(history(Nat.sub t 5)%nat)(history(S(Nat.sub t 5)))_ word ltac:(exact(rf_writeback_member 1 ltac:(lia)))G1 A L(Steps(Nat.sub t 5)%nat ltac:(lia)))as[v1[V1 L1]].
 replace(S(Nat.sub t 5))with(Nat.sub t 4)%nat in V1 by lia.
 destruct(Guards(Nat.sub t 4)%nat ltac:(lia)ltac:(lia))as[_[G2 _]].
 destruct(rf_writeback_signed_selected 7934 7933 7929 7932 invalid(history(Nat.sub t 4)%nat)(history(S(Nat.sub t 4)))_ word ltac:(exact(rf_writeback_member 3 ltac:(lia)))G2 V1 L1(Steps(Nat.sub t 4)%nat ltac:(lia)))as[v2[V2 L2]].
 replace(S(Nat.sub t 4))with(Nat.sub t 3)%nat in V2 by lia.
 destruct(Guards(Nat.sub t 3)%nat ltac:(lia)ltac:(lia))as[_[_ G3]].
 destruct(rf_writeback_signed_selected 7936 7935 7930 7934 invalid(history(Nat.sub t 3)%nat)(history(S(Nat.sub t 3)))_ word ltac:(exact(rf_writeback_member 5 ltac:(lia)))G3 V2 L2(Steps(Nat.sub t 3)%nat ltac:(lia)))as[v3[V3[width[raw[Value[RawSize[Wide Low]]]]]]].
 subst v3. replace(S(Nat.sub t 3))with(Nat.sub t 2)%nat in V3 by lia.
 assert(Cast:VM.find 7937(history(Nat.sub t 1)%nat)=Some(Gval(Fuint width)raw)).
 { replace(Nat.sub t 1)%nat with(S(Nat.sub t 2))by lia.
 apply(rf_writeback_node_step invalid(history(Nat.sub t 2)%nat)(history(Nat.sub t 2)%nat)(history(S(Nat.sub t 2)))6 _ (Fuint width));[lia| |reflexivity|apply Steps;lia].
 cbn[rf_writeback_nodes nth snd joint_update_expr_7937 eval_hfexpr_with_memory eval_href_with_memory]. rewrite V3. reflexivity. }
 replace t with(S(Nat.sub t 1))at 1 by lia. rewrite -Low.
 apply(rf_preview_data_port_exact invalid(history(Nat.sub t 1)%nat)(history(Nat.sub t 1)%nat)(history(S(Nat.sub t 1)))width raw);[exact/leP|exact RawSize|exact Cast|apply Steps;lia].
Qed.
Require Import RFNonAluBubbleHazard.
Theorem rf_alu_writeback_observed memory inputs k observed word :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 size word=32%nat ->
 VM.find 7756(top_environment observed)=Some(Gval(Fuint 2)[::false;false]) ->
 VM.find 7752(top_environment observed)=Some(Gval(Fuint 32)word) ->
 VM.find 786(top_environment observed)=Some(Gval(Fuint 32)word).
Proof.
 intros Observe Legal Size Mode Alu.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Modes:forall t,(t<=9259)%coq_nat ->VM.find 7756(history t)=Some(Gval(Fuint 2)[::false;false])).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7756 2 rf_nonalu_mode_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last;exact Mode. }
 assert(Alus:forall t,(t<=9259)%coq_nat ->VM.find 7752(history t)=Some(Gval(Fuint 32)word)).
 { intros t Upper. pose proof(joint_update_register_history_same _ history 9259 7752 32 rf_read_alu_member Steps)as Hold.
 rewrite(Hold t Upper). rewrite <- (Hold 9259%nat ltac:(lia)). rewrite Last;exact Alu. }
 rewrite <-Last. exact(rf_alu_writeback_history _ history 9259 word Size Modes Alus Steps 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)).
Qed.
Theorem cycle_alu_writeback memory inputs k observed view :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)view ->
 cv_write_select_low view=false ->cv_write_select_high view=false ->
 cv_pending_alu view=cv_write_data view.
Proof.
 intros Observe Legal View Low High.
 pose proof(cva_write_select _ _ View)as Mode. rewrite Low High in Mode.
 pose proof(rf_alu_writeback_observed memory inputs k observed(cv_pending_alu view)Observe Legal(cva_pending_width _ _ View)Mode(cva_pending_alu _ _ View))as Value.
 rewrite(cva_write_data _ _ View)in Value.
 symmetry;exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Value).
Qed.
Require Import RFWriteEffect JointBoundaryInitialization ObservedJointRegisterConcrete.
Definition cycle_pending_effect view :=
 if cv_write_enabled view then RFWrite(to_nat(cv_destination view))(cv_write_data view) else RFNoWrite.
Require Import ReferenceBankObservation RFArchitecturalNormalRelation FlatRegFileX0.
Lemma cycle_dut_x0 memory inputs k observed view :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)view ->cv_dut_bank view 0%nat=zeros 32.
Proof.
 intros Observe Legal View. pose proof Observe as Expanded.
 unfold generated_observe,generated_observe_cycle in Expanded.
 destruct(generated_run memory inputs k)as[committed|]eqn:Run;[|discriminate Expanded].
 destruct(rf_storage_x0_reachable memory inputs k committed Run Legal)as[env[Env Zero]].
 pose proof(joint_register_run_observed memory inputs k committed observed 851 32 (rf_read_bank_member 0 ltac:(lia)) Run Observe)as Copy.
 unfold top_environment in Copy. rewrite Env in Copy. rewrite Zero in Copy.
 pose proof(proj2(cva_dut_bank _ _ View 0 ltac:(vm_compute;lia)))as Value.
 change(VM.find 851(top_environment observed)=Some(Gval(Fuint 32)(cv_dut_bank view 0%nat)))in Value.
 change(VM.find 851(top_environment observed)=Some rf_zero32)in Copy.
 rewrite Copy in Value. exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)(Logic.eq_sym Value)).
Qed.
Theorem cycle_forwarded_read memory inputs k observed view second :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_view_at(top_environment observed)view ->cycle_banks_agree view ->
 (if second then cv_right view else cv_left view)=
 rf_apply_effect(cv_reference_bank view)(cycle_pending_effect view)
 (to_nat(rf_instruction_address second(cv_front_instruction view))).
Proof.
 intros Observe Legal View Paired.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal rf_read_front_member)as[front[Size Front]].
 rewrite(cva_front_instruction _ _ View)in Front. inversion Front;subst front.
 assert(Bound:(to_nat(rf_instruction_address second(cv_front_instruction view))<32)%coq_nat).
 { pose proof(to_nat_bounded(rf_instruction_address second(cv_front_instruction view)))as H.
 rewrite(rf_instruction_address_size second _ Size)in H. exact(elimT ltP H). }
 pose proof(rf_actual_forwarding_observed memory inputs k observed second(cv_dut_bank view)(cv_reference_bank view)(cv_front_instruction view)(cv_destination view)(cv_write_enabled view)(cv_write_select_low view)(cv_write_select_high view)(cv_pending_alu view)(cv_write_data view)
 Observe Legal(cva_dut_bank _ _ View)Size(cva_front_instruction _ _ View)(cva_destination _ _ View)(cva_write_enabled _ _ View)(cva_write_select _ _ View)(cva_pending_width _ _ View)(cva_pending_alu _ _ View))as Value.
 assert(Zero:cv_reference_bank view 0%nat=zeros 32).
 { rewrite <-(Paired 0%nat ltac:(lia)). exact(cycle_dut_x0 memory inputs k observed view Observe Legal View). }
 specialize(Value ltac:(rewrite(rf_apply_effect_no_write _ Zero);exact(Paired _ Bound))).
 assert(Alu:(~~cv_write_select_low view && ~~cv_write_select_high view)=true ->cv_pending_alu view=cv_write_data view).
 { intro Both. apply(cycle_alu_writeback memory inputs k observed view Observe Legal View).
 - destruct(cv_write_select_low view);[discriminate Both|reflexivity].
 - destruct(cv_write_select_high view);[rewrite andbF in Both;discriminate|reflexivity]. }
 specialize(Value Alu). unfold cycle_pending_effect.
 destruct second;cbn[rf_forward_node]in Value;rewrite ?(cva_right _ _ View) ?(cva_left _ _ View)in Value;
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Value).
Qed.
