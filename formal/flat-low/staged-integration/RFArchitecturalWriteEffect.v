Require Import CoreSocModel ComparisonNodes RFWriteEffect RFArchitecturalNormalRelation RFArchitecturalRelation RFPreviewEffect RFReadPorts JointUpdateNodePositions JointUpdateExpressionCertificates SelectedNodeSafety FormalTypedNodeEquation ConcreteDecodeOperations RFReferenceWriteEffect RFReferenceNopHistory.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_storage_rd_condition index := @Eprim_binop VarOrder.T(Bcomp Beq)
 (@Econst VarOrder.T(Fuint(rf_preview_index_width index))(from_N(rf_preview_index_width index)(N.of_nat index)))
 (@Eref VarOrder.T(@Eid VarOrder.T 785)).
Lemma rf_storage_rd_condition_eval index invalid site old rd :(index<32)%coq_nat ->VM.find 785 old=Some(Gval(Fuint 5)rd) ->
 eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories(rf_storage_rd_condition index)old old=Some(Gval(Fuint 1)[::index==to_nat rd]).
Proof.
 intros Bound Rd. cbn [rf_storage_rd_condition eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Rd size_from_N ltnn.
 assert(Constant:zext_to(rf_preview_index_width index)(from_N(rf_preview_index_width index)(N.of_nat index))=from_N(rf_preview_index_width index)(N.of_nat index)).
 { unfold zext_to,zext. rewrite size_from_N subnn cats0. reflexivity. }
 rewrite Constant. unfold eval_binop. cbn [eval_binop_basic]. rewrite refine_concrete_uint(rf_preview_index_exact index Bound)rf_preview_rd_match. reflexivity.
Qed.
Lemma rf_storage_select_step index invalid old result rd data prior :(index<32)%coq_nat ->size data=32%nat ->size prior=32%nat ->
 VM.find 785 old=Some(Gval(Fuint 5)rd) ->VM.find 955 old=Some(Gval(Fuint 32)data) ->
 VM.find(N.of_nat(851+index)%nat)old=Some(Gval(Fuint 32)prior) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(N.of_nat(956+index)%nat)result=Some(Gval(Fuint 32)(if index==to_nat rd then data else prior)).
Proof.
 intros Bound DataSize PriorSize Rd Data Prior Step.
 destruct(selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes _ _ joint_update_node_positions joint_update_node_safety(rf_dut_select_member index Bound))as[count[tail[Position[Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 change(eval_hfexpr_validif_policy(isolated_validif_policy invalid)(validif_raw_address nil count 0 nil)flat_memories
 (@Emux VarOrder.T(rf_storage_rd_condition index)(@Eref VarOrder.T(@Eid VarOrder.T 955))(@Eref VarOrder.T(@Eid VarOrder.T(N.of_nat(851+index)%nat))))old old=Some(Gval(Fuint 32)(if index==to_nat rd then data else prior))).
 eapply rf_read_mux_exact;[intro site;exact(rf_storage_rd_condition_eval index invalid site old rd Bound Rd)|exact Data|reflexivity|exact Prior|reflexivity|destruct(index==to_nat rd);reflexivity|destruct(index==to_nat rd);assumption].
Qed.
Lemma rf_storage_gate_step index invalid old result enabled selected prior :(index<32)%coq_nat ->size selected=32%nat ->size prior=32%nat ->
 VM.find 954 old=Some(Gval(Fuint 1)[::enabled]) ->VM.find(N.of_nat(956+index)%nat)old=Some(Gval(Fuint 32)selected) ->
 VM.find(N.of_nat(851+index)%nat)old=Some(Gval(Fuint 32)prior) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(N.of_nat(1021+index)%nat)result=Some(Gval(Fuint 32)(if enabled then selected else prior)).
Proof.
 intros Bound SelectedSize PriorSize Gate Selected Prior Step.
 destruct(selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes _ _ joint_update_node_positions joint_update_node_safety(rf_dut_normal_member index Bound))as[count[tail[Position[Safe Nonreg]]]].
 eapply formal_combinational_known_node;[exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 unfold rf_dut_normal_expr. eapply rf_read_mux_exact;[intro site;exact Gate|exact Selected|reflexivity|exact Prior|reflexivity|destruct enabled;reflexivity|destruct enabled;assumption].
Qed.
Theorem rf_storage_nonzero_effect_after_two index invalid s0 s1 s2 bank rd data enabled :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->rf_dut_bank_at s0 bank ->size data=32%nat ->
 VM.find 785 s0=Some(Gval(Fuint 5)rd) ->VM.find 955 s0=Some(Gval(Fuint 32)data) ->
 VM.find 954 s1=Some(Gval(Fuint 1)[::enabled]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 VM.find(N.of_nat(1021+index)%nat)s2=Some(Gval(Fuint 32)(rf_apply_effect bank(if enabled then RFWrite(to_nat rd)data else RFNoWrite)index)).
Proof.
 intros Lower Upper Bank DataSize Rd Data Gate S1 S2.
 destruct(Bank index Upper)as[PriorSize Prior].
 pose proof(rf_storage_select_step index invalid s0 s1 rd data(bank index)Upper DataSize PriorSize Rd Data Prior S1)as Selected.
 pose proof(proj2(rf_dut_bank_comb_hold invalid s0 s0 s1 bank Bank S1 index Upper))as Prior1.
 pose proof(rf_storage_gate_step index invalid s1 s2 enabled(if index==to_nat rd then data else bank index)(bank index)Upper ltac:(destruct(index==to_nat rd);assumption) PriorSize Gate Selected Prior1 S2)as Output.
 unfold rf_apply_effect. assert(Zero:(index==0%nat)=false)by(apply/eqP;lia). rewrite Zero.
 destruct enabled;exact Output.
Qed.
Theorem rf_dut_nonzero_effect_commit index invalid s0 s1 s2 result bank rd data enabled :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->rf_dut_bank_at s0 bank ->size data=32%nat ->
 VM.find 785 s0=Some(Gval(Fuint 5)rd) ->VM.find 955 s0=Some(Gval(Fuint 32)data) ->VM.find 954 s1=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 779 s2=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements=Some result ->
 VM.find(N.of_nat(851+index)%nat)result=Some(Gval(Fuint 32)(rf_apply_effect bank(if enabled then RFWrite(to_nat rd)data else RFNoWrite)index)).
Proof.
 intros Lower Upper Bank DataSize Rd Data Gate Reset S1 S2 Commit.
 pose proof(rf_dut_bank_comb_hold invalid s0 s0 s1 bank Bank S1)as B1.
 pose proof(rf_dut_bank_comb_hold invalid s1 s1 s2 bank B1 S2)as B2.
 eapply rf_dut_normal_commit_value;[exact Upper|exact(proj2(B2 index Upper))|reflexivity|exact Reset|exact(rf_storage_nonzero_effect_after_two index invalid s0 s1 s2 bank rd data enabled Lower Upper Bank DataSize Rd Data Gate S1 S2)| |exact Commit].
 unfold rf_apply_effect. destruct(index==0%nat);[reflexivity|]. destruct enabled;[destruct(index==to_nat rd);[exact DataSize|exact(proj1(Bank index Upper))]|exact(proj1(Bank index Upper))].
Qed.
Require Import RFReferenceNopIngress.
Theorem rf_reference_nonzero_effect_commit invalid history (limit start:nat) index rd bank guards permissions words active result :
 (1<=index)%coq_nat ->(index<32)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (Nat.add start 111<=limit)%coq_nat ->VM.find 1515(history limit)=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories(history limit)true(history limit)flat_statements=Some result ->
 VM.find(N.of_nat(7299+index)%nat)result=Some(Gval(Fuint 32)
 (rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index)).
Proof.
 intros Lower Upper Rd Start Bank Data Guards Permissions Active Steps Ready Reset Commit.
 assert(Initial:forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(N.of_nat(2177-index)%nat)(history t)=Some value /\rf_reference_low_word(bank index)value).
 { intros t L U. destruct t as[|[|t]];try lia.
   destruct(rf_reference_bank_history_hold invalid history limit bank Bank Steps t ltac:(lia) index Upper)as[Size Value].
   exists(Gval(Fuint 32)(bank index)). split.
   - exact(rf_reference_old_word_ingress index invalid(history t)(history(S t))(history(S(S t)))(bank index)Upper Size Value(Steps t ltac:(lia))(Steps(S t)ltac:(lia))).
   - exists 32%nat,(bank index). repeat split;try assumption;try reflexivity. rewrite -Size take_size. reflexivity. }
 destruct limit as[|[|[|time]]];try lia.
 destruct(rf_reference_effect_history invalid history(S(S(S time)))start index rd(bank index)guards permissions words Lower Upper Rd Initial Data Guards Permissions Steps 36 time ltac:(lia) ltac:(change(Nat.add start 108<=time)%coq_nat;lia) ltac:(lia))as[value[Value Low]].
 destruct(Initial time ltac:(lia) ltac:(lia))as[prior[Prior PLow]].
 assert(Choice:(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)index).
 { destruct active;[exact(rf_reference_fold_effect guards permissions words(to_nat rd)index bank 36 Lower)|].
   unfold rf_apply_effect. assert(Zero:(index==0%nat)=false)by(apply/eqP;lia). rewrite Zero. reflexivity. }
 assert(Size:size(if active then rf_reference_fold_word guards permissions words(to_nat rd)index(bank index)36 else bank index)=32%nat).
 { destruct active;[exact(rf_reference_low_word_size _ _ Low)|exact(rf_reference_low_word_size _ _ PLow)]. }
 pose proof(rf_reference_effect_exit index invalid(history time)(history(S time))(history(S(S time)))(history(S(S(S time))))active value prior _ _ Lower Upper (Active time ltac:(lia) ltac:(lia)) Value Low Prior PLow (Steps time ltac:(lia))(Steps(S time)ltac:(lia))(Steps(S(S time))ltac:(lia)))as Port.
 rewrite Choice in Size,Port.
 pose proof(rf_reference_bank_history_hold invalid history(S(S(S time)))bank Bank Steps(S(S(S time)))ltac:(lia))as FinalBank.
 eapply rf_reference_normal_commit_value;[exact Upper|exact(proj2(FinalBank index Upper))|reflexivity|exact Reset|exact Port|exact Size|exact Commit].
Qed.

(* Writes to x0 are architecturally NoWrite, including reference NOP. *)
Definition rf_effect_normalize effect :=match effect with
 |RFNoWrite=>RFNoWrite
 |RFWrite destination word=>if destination==0%nat then RFNoWrite else RFWrite destination word end.
Lemma rf_apply_effect_normalize bank effect index :rf_apply_effect bank(rf_effect_normalize effect)index=rf_apply_effect bank effect index.
Proof.
 destruct effect as[|destination word];[reflexivity|]. unfold rf_effect_normalize.
 destruct(destination==0%nat)eqn:Zero;[|reflexivity]. move/eqP:Zero=>Zero. subst destination.
 unfold rf_apply_effect. destruct(index==0%nat);reflexivity.
Qed.
Lemma rf_normalized_effect_agreement bank left right :rf_effect_normalize left=rf_effect_normalize right ->forall index,rf_apply_effect bank left index=rf_apply_effect bank right index.
Proof. intros Equal index. rewrite -(rf_apply_effect_normalize bank left index) -(rf_apply_effect_normalize bank right index) Equal. reflexivity. Qed.
Lemma rf_scalar_effect_agreement rd left_data right_data left_enabled right_enabled :
 (left_enabled && (rd!=0%nat))=(right_enabled && (rd!=0%nat)) ->
 (left_enabled && (rd!=0%nat)=true ->left_data=right_data) ->
 rf_effect_normalize(if left_enabled then RFWrite rd left_data else RFNoWrite)=rf_effect_normalize(if right_enabled then RFWrite rd right_data else RFNoWrite).
Proof.
 intros Enable Data. destruct(rd==0%nat)eqn:Zero.
 - destruct left_enabled,right_enabled;cbn [rf_effect_normalize];rewrite ?Zero;reflexivity.
 - change(left_enabled && true=right_enabled && true)in Enable. rewrite !andbT in Enable. subst right_enabled.
   destruct left_enabled;[|reflexivity]. assert(Same:left_data=right_data)by(apply Data;reflexivity). rewrite Same. reflexivity.
Qed.
Lemma rf_reference_effect_zero guards permissions words count :rf_effect_normalize(rf_reference_effect guards permissions words 0 count)=RFNoWrite.
Proof. induction count as[|count IH];[reflexivity|]. cbn [rf_reference_effect]. destruct(guards count && rf_reference_permission_value count(permissions count));[reflexivity|exact IH]. Qed.
Theorem rf_paired_nonzero_effect_history invalid history (limit start:nat) rd bank guards permissions words active result dut_rd dut_data dut_enabled :
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 rf_dut_bank_at(history 0%nat)bank ->size dut_data=32%nat ->
 VM.find 785(history(Nat.sub limit 2))=Some(Gval(Fuint 5)dut_rd) ->
 VM.find 955(history(Nat.sub limit 2))=Some(Gval(Fuint 32)dut_data) ->
 VM.find 954(history(Nat.sub limit 1))=Some(Gval(Fuint 1)[::dut_enabled]) ->
 VM.find 779(history limit)=Some(Gval(Fuint 1)[::false]) ->
 rf_effect_normalize(if dut_enabled then RFWrite(to_nat dut_rd)dut_data else RFNoWrite)=
 rf_effect_normalize(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite) ->
 (Nat.add start 111<=limit)%coq_nat ->VM.find 1515(history limit)=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories(history limit)true(history limit)flat_statements=Some result ->
 forall index,(1<=index)%coq_nat ->(index<32)%coq_nat ->exists word,size word=32%nat /\
 VM.find(N.of_nat(851+index)%nat)result=Some(Gval(Fuint 32)word) /\
 VM.find(N.of_nat(7299+index)%nat)result=Some(Gval(Fuint 32)word).
Proof.
 intros Rd Start Bank Data Guards Permissions Active Steps DutBank DataSize DutRd DutData DutGate DutReset Effect Ready RefReset Commit index Lower Upper.
 pose proof(rf_reference_nonzero_effect_commit invalid history limit start index rd bank guards permissions words active result Lower Upper Rd Start Bank Data Guards Permissions Active Steps Ready RefReset Commit)as Reference.
 destruct limit as[|[|time]];try lia. cbn [Nat.sub] in DutRd,DutData,DutGate. rewrite ?Nat.sub_0_r in DutRd,DutData,DutGate.
 pose proof(rf_dut_bank_history_hold invalid history(S(S time))bank DutBank Steps time ltac:(lia))as Bank0.
 pose proof(rf_dut_nonzero_effect_commit index invalid(history time)(history(S time))(history(S(S time)))result bank dut_rd dut_data dut_enabled Lower Upper Bank0 DataSize DutRd DutData DutGate DutReset(Steps time ltac:(lia))(Steps(S time)ltac:(lia))Commit)as Dut.
 pose proof(rf_normalized_effect_agreement bank _ _ Effect index)as WordAgreement. rewrite <-WordAgreement in Reference.
 exists(rf_apply_effect bank(if dut_enabled then RFWrite(to_nat dut_rd)dut_data else RFNoWrite)index). split.
 - unfold rf_apply_effect. destruct(index==0%nat);[reflexivity|]. destruct dut_enabled;[destruct(index==to_nat dut_rd);[exact DataSize|exact(proj1(DutBank index Upper))]|exact(proj1(DutBank index Upper))].
 - split;assumption.
Qed.

(* Original RF assertion interface. *)
Require Import FormalAssertionDischarge ComparisonTruth AssertionInstances PipelinePCAssertions.
Definition rf_original_assertion_local(index:nat)(env:VM.t hvalue):Prop := nth(fun _=>False)[::generated_assert_m0_8_local;generated_assert_m0_9_local;generated_assert_m0_10_local;generated_assert_m0_11_local;generated_assert_m0_12_local;generated_assert_m0_13_local;generated_assert_m0_14_local;generated_assert_m0_15_local;generated_assert_m0_16_local;generated_assert_m0_17_local;generated_assert_m0_18_local;generated_assert_m0_19_local;generated_assert_m0_20_local;generated_assert_m0_21_local;generated_assert_m0_22_local;generated_assert_m0_23_local;generated_assert_m0_24_local;generated_assert_m0_25_local;generated_assert_m0_26_local;generated_assert_m0_27_local;generated_assert_m0_28_local;generated_assert_m0_29_local;generated_assert_m0_30_local;generated_assert_m0_31_local;generated_assert_m0_32_local;generated_assert_m0_33_local;generated_assert_m0_34_local;generated_assert_m0_35_local;generated_assert_m0_36_local;generated_assert_m0_37_local;generated_assert_m0_38_local;generated_assert_m0_39_local]index env.
Definition rf_original_assertion_all(index:nat)(states:SVM.t(VM.t hvalue)):Prop := nth(fun _=>False)[::generated_assert_m0_8_all;generated_assert_m0_9_all;generated_assert_m0_10_all;generated_assert_m0_11_all;generated_assert_m0_12_all;generated_assert_m0_13_all;generated_assert_m0_14_all;generated_assert_m0_15_all;generated_assert_m0_16_all;generated_assert_m0_17_all;generated_assert_m0_18_all;generated_assert_m0_19_all;generated_assert_m0_20_all;generated_assert_m0_21_all;generated_assert_m0_22_all;generated_assert_m0_23_all;generated_assert_m0_24_all;generated_assert_m0_25_all;generated_assert_m0_26_all;generated_assert_m0_27_all;generated_assert_m0_28_all;generated_assert_m0_29_all;generated_assert_m0_30_all;generated_assert_m0_31_all;generated_assert_m0_32_all;generated_assert_m0_33_all;generated_assert_m0_34_all;generated_assert_m0_35_all;generated_assert_m0_36_all;generated_assert_m0_37_all;generated_assert_m0_38_all;generated_assert_m0_39_all]index states.
Lemma rf_original_assertion_at_top index states env :(index<32)%coq_nat ->SVM.find nil states=Some env ->rf_original_assertion_local index env ->rf_original_assertion_all index states.
Proof. intros Bound Env Local.
 destruct index as[|index]. { apply(proj2(assertion_8_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_9_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_10_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_11_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_12_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_13_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_14_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_15_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_16_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_17_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_18_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_19_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_20_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_21_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_22_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_23_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_24_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_25_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_26_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_27_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_28_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_29_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_30_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_31_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_32_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_33_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_34_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_35_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_36_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_37_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_38_at_top states)). rewrite Env. exact Local. }
 destruct index as[|index]. { apply(proj2(assertion_39_at_top states)). rewrite Env. exact Local. }
 lia. Qed.
Theorem rf_original_assertion_from_common_effect index invalid old result states bank effect :
 (index<32)%coq_nat ->SVM.find nil states=Some result ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 (generated_expr_true(pipeline_pc_enable 1395(pipeline_pc_guard_id(S index)))result ->
 VM.find(N.of_nat(Nat.add 1399 index))old=Some(Gval(Fuint 32)(rf_apply_effect bank effect index)) /\
 VM.find(N.of_nat(Nat.add 1597 index))old=Some(Gval(Fuint 32)(rf_apply_effect bank effect index))) ->
 rf_original_assertion_all index states.
Proof.
 intros Bound Env Step Sources. eapply rf_original_assertion_at_top;[exact Bound|exact Env|].
 destruct index as[|index]. { apply(assertion_8_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 0%nat),(rf_apply_effect bank effect 0%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_9_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 1%nat),(rf_apply_effect bank effect 1%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_10_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 2%nat),(rf_apply_effect bank effect 2%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_11_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 3%nat),(rf_apply_effect bank effect 3%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_12_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 4%nat),(rf_apply_effect bank effect 4%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_13_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 5%nat),(rf_apply_effect bank effect 5%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_14_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 6%nat),(rf_apply_effect bank effect 6%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_15_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 7%nat),(rf_apply_effect bank effect 7%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_16_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 8%nat),(rf_apply_effect bank effect 8%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_17_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 9%nat),(rf_apply_effect bank effect 9%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_18_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 10%nat),(rf_apply_effect bank effect 10%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_19_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 11%nat),(rf_apply_effect bank effect 11%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_20_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 12%nat),(rf_apply_effect bank effect 12%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_21_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 13%nat),(rf_apply_effect bank effect 13%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_22_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 14%nat),(rf_apply_effect bank effect 14%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_23_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 15%nat),(rf_apply_effect bank effect 15%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_24_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 16%nat),(rf_apply_effect bank effect 16%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_25_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 17%nat),(rf_apply_effect bank effect 17%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_26_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 18%nat),(rf_apply_effect bank effect 18%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_27_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 19%nat),(rf_apply_effect bank effect 19%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_28_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 20%nat),(rf_apply_effect bank effect 20%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_29_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 21%nat),(rf_apply_effect bank effect 21%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_30_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 22%nat),(rf_apply_effect bank effect 22%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_31_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 23%nat),(rf_apply_effect bank effect 23%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_32_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 24%nat),(rf_apply_effect bank effect 24%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_33_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 25%nat),(rf_apply_effect bank effect 25%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_34_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 26%nat),(rf_apply_effect bank effect 26%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_35_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 27%nat),(rf_apply_effect bank effect 27%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_36_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 28%nat),(rf_apply_effect bank effect 28%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_37_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 29%nat),(rf_apply_effect bank effect 29%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_38_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 30%nat),(rf_apply_effect bank effect 30%nat). repeat split;assumption. }
 destruct index as[|index]. { apply(assertion_39_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect 31%nat),(rf_apply_effect bank effect 31%nat). repeat split;assumption. }
 lia. Qed.
