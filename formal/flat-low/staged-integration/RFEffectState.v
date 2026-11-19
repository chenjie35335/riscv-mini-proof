Require Import CoreSocModel ComparisonNodes RFWriteEffect RFArchitecturalWriteEffect RFReferenceWriteEffect RFReferenceNopHistory RFReferenceNopIngress FormalReferenceX0 FormalReferenceX0Connections.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_effect_sized effect :=match effect with RFNoWrite=>True|RFWrite _ word=>size word=32%nat end.
Lemma rf_reference_effect_sized guards permissions words destination count :
 (forall stage,(stage<count)%coq_nat ->size(words stage)=32%nat) ->rf_effect_sized(rf_reference_effect guards permissions words destination count).
Proof.
 intro Sizes. induction count as[|count IH];[exact I|]. cbn[rf_reference_effect].
 destruct(guards count && rf_reference_permission_value count(permissions count));[apply Sizes;lia|apply IH;intros stage Bound;apply Sizes;lia].
Qed.
Lemma rf_apply_effect_size bank effect index :size(bank index)=32%nat ->rf_effect_sized effect ->size(rf_apply_effect bank effect index)=32%nat.
Proof.
 intros Bank Effect. unfold rf_apply_effect. destruct(index==0%nat);[reflexivity|].
 destruct effect;[exact Bank|]. destruct(index==destination);assumption.
Qed.
Lemma rf_reference_x0_source_history invalid history limit start bank active :rf_reference_bank_at(history 0%nat)bank ->bank 0%nat=nseq 32 false ->(2<=start)%coq_nat ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall time,(Nat.add start 3<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1787(history time)=Some(Gval(Fuint 32)(nseq 32 false)).
Proof.
 intros Bank Zero Start Active Steps[|[|[|[|[|time]]]]]Lower Upper;try lia.
 destruct(rf_reference_bank_history_hold invalid history limit bank Bank Steps time ltac:(lia)0%nat ltac:(lia))as[Size Old].
 rewrite Zero in Size,Old.
 pose proof(rf_reference_old_word_ingress 0 invalid(history time)(history(S time))(history(S(S time)))(nseq 32 false)ltac:(lia)Size Old(Steps time ltac:(lia))(Steps(S time)ltac:(lia)))as Input.
 assert(Entry:VM.find 3255(history(S(S(S time))))=Some(Gval(Fuint 32)(nseq 32 false))).
 { eapply reference_x0_node_3255;[|reflexivity|apply Steps;lia].
 cbn[reference_x0_expr_3255 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite(Active(S(S time))ltac:(lia)ltac:(lia)).
 unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref]. rewrite Input.
 destruct active;reflexivity. }
 assert(Alias:VM.find 3256(history(S(S(S(S time)))))=Some(Gval(Fuint 32)(nseq 32 false))).
 { eapply reference_x0_node_3256;[|reflexivity|apply Steps;lia].
 cbn[reference_x0_expr_3256 eval_hfexpr_with_memory eval_href_with_memory]. exact Entry. }
 eapply reference_output_connection_1787;[exact Alias|reflexivity|apply Steps;lia].
Qed.
Theorem rf_reference_bank_effect_commit invalid history (limit start:nat) rd bank guards permissions words active result :
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->bank 0%nat=nseq 32 false ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (Nat.add start 111<=limit)%coq_nat ->VM.find 1515(history limit)=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories(history limit)true(history limit)flat_statements=Some result ->
 rf_reference_bank_at result(rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)).
Proof.
 intros Rd Start Bank Zero Data Guards Permissions Active Steps Ready Reset Commit index Index.
 split.
 - apply rf_apply_effect_size;[exact(proj1(Bank index Index))|].
 destruct active;[|exact I]. apply rf_reference_effect_sized. intros stage Stage.
 destruct(Data stage start Stage ltac:(lia)ltac:(lia))as[value[Value Low]]. exact(rf_reference_low_word_size _ _ Low).
 - destruct index as[|index].
 + change(VM.find 7299 result=Some(Gval(Fuint 32)(nseq 32 false))).
 destruct(rf_reference_bank_history_hold invalid history limit bank Bank Steps limit ltac:(lia)0%nat ltac:(lia))as[Size Old].
 eapply(rf_reference_normal_commit_value invalid(history limit)(history limit)result 0(Gval(Fuint 32)(bank 0%nat))(nseq 32 false));[lia|exact Old|reflexivity|exact Reset| |reflexivity|exact Commit].
 exact(rf_reference_x0_source_history invalid history limit start bank active Bank Zero Start Active Steps limit ltac:(lia)ltac:(lia)).
 + exact(rf_reference_nonzero_effect_commit invalid history limit start(S index)rd bank guards permissions words active result ltac:(lia)Index Rd Start Bank Data Guards Permissions Active Steps Ready Reset Commit).
Qed.
Require Import RFArchitecturalNormalRelation.
Theorem rf_dut_bank_effect_commit invalid s0 s1 s2 result bank rd data enabled :
 rf_dut_bank_at s0 bank ->bank 0%nat=nseq 32 false ->size data=32%nat ->
 (enabled=true ->to_nat rd<>0%nat) ->
 VM.find 785 s0=Some(Gval(Fuint 5)rd) ->VM.find 955 s0=Some(Gval(Fuint 32)data) ->VM.find 954 s1=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 779 s2=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 true s2 flat_statements=Some result ->
 rf_dut_bank_at result(rf_apply_effect bank(if enabled then RFWrite(to_nat rd)data else RFNoWrite)).
Proof.
 intros Bank Zero DataSize Guard Rd Data Gate Reset S1 S2 Commit index Index.
 split.
 - apply rf_apply_effect_size;[exact(proj1(Bank index Index))|]. destruct enabled;[exact DataSize|exact I].
 - destruct index as[|index].
 + change(VM.find 851 result=Some(Gval(Fuint 32)(nseq 32 false))).
 destruct(Bank 0%nat ltac:(lia))as[PriorSize Prior].
 pose proof(rf_storage_select_step 0 invalid s0 s1 rd data(bank 0%nat)ltac:(lia)DataSize PriorSize Rd Data Prior S1)as Selected.
 pose proof(rf_dut_bank_comb_hold invalid s0 s0 s1 bank Bank S1)as B1.
 pose proof(rf_dut_bank_comb_hold invalid s1 s1 s2 bank B1 S2)as B2.
 pose proof(rf_storage_gate_step 0 invalid s1 s2 enabled(if 0%nat==to_nat rd then data else bank 0%nat)(bank 0%nat)ltac:(lia)ltac:(destruct(0%nat==to_nat rd);assumption)PriorSize Gate Selected(proj2(B1 0%nat ltac:(lia)))S2)as Source.
 assert(Value:(if enabled then if 0%nat==to_nat rd then data else bank 0%nat else bank 0%nat)=nseq 32 false).
 { destruct enabled;[|exact Zero]. assert(Nonzero:(0%nat==to_nat rd)=false)by(apply/eqP;intro Same;apply(Guard(Logic.eq_refl _));lia). rewrite Nonzero. exact Zero. }
 rewrite Value in Source.
 eapply(rf_dut_normal_commit_value invalid s2 s2 result 0(Gval(Fuint 32)(bank 0%nat))(nseq 32 false));[lia|exact(proj2(B2 0%nat ltac:(lia)))|reflexivity|exact Reset|exact Source|reflexivity|exact Commit].
 + exact(rf_dut_nonzero_effect_commit(S index)invalid s0 s1 s2 result bank rd data enabled ltac:(lia)Index Bank DataSize Rd Data Gate Reset S1 S2 Commit).
Qed.
Theorem rf_paired_bank_effect_commit invalid history (limit start:nat) rd bank guards permissions words active result dut_rd dut_data dut_enabled :
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3221(history t)=Some(Gval(Fuint 5)rd)) ->
 (2<=start)%coq_nat ->rf_reference_bank_at(history 0%nat)bank ->bank 0%nat=nseq 32 false ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(rf_reference_write_data stage)(history t)=Some value /\rf_reference_low_word(words stage)value) ->
 (forall stage t,(stage<36)%coq_nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_chain_guard stage)(history t)=Some(Gval(Fuint 1)[::guards stage])) ->
 (forall stage t,(stage<36)%coq_nat ->rf_reference_write_depth stage=2%nat ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find(rf_reference_permission_node stage)(history t)=Some(Gval(Fuint 1)[::permissions stage])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::active])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 rf_dut_bank_at(history 0%nat)bank ->size dut_data=32%nat ->(dut_enabled=true ->to_nat dut_rd<>0%nat) ->
 VM.find 785(history(Nat.sub limit 2))=Some(Gval(Fuint 5)dut_rd) ->VM.find 955(history(Nat.sub limit 2))=Some(Gval(Fuint 32)dut_data) ->VM.find 954(history(Nat.sub limit 1))=Some(Gval(Fuint 1)[::dut_enabled]) ->
 VM.find 779(history limit)=Some(Gval(Fuint 1)[::false]) ->
 rf_effect_normalize(if dut_enabled then RFWrite(to_nat dut_rd)dut_data else RFNoWrite)=rf_effect_normalize(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite) ->
 (Nat.add start 111<=limit)%coq_nat ->VM.find 1515(history limit)=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories(history limit)true(history limit)flat_statements=Some result ->
 rf_dut_bank_at result(rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)) /\
 rf_reference_bank_at result(rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite)).
Proof.
 intros Rd Start RefBank Zero Data Guards Permissions Active Steps DutBank DataSize Guard DutRd DutData DutGate DutReset Effect Ready RefReset Commit.
 assert(Reference:rf_reference_bank_at result(rf_apply_effect bank(if active then rf_reference_effect guards permissions words(to_nat rd)36 else RFNoWrite))).
 { exact(rf_reference_bank_effect_commit invalid history limit start rd bank guards permissions words active result Rd Start RefBank Zero Data Guards Permissions Active Steps Ready RefReset Commit). }
 split;[|exact Reference].
 destruct limit as[|[|time]];try lia. cbn[Nat.sub]in DutRd,DutData,DutGate. rewrite Nat.sub_0_r in DutRd,DutData,DutGate.
 pose proof(rf_dut_bank_history_hold invalid history(S(S time))bank DutBank Steps time ltac:(lia))as Bank.
 pose proof(rf_dut_bank_effect_commit invalid(history time)(history(S time))(history(S(S time)))result bank dut_rd dut_data dut_enabled Bank Zero DataSize Guard DutRd DutData DutGate DutReset(Steps time ltac:(lia))(Steps(S time)ltac:(lia))Commit)as Dut.
 intros index Index. rewrite <-(rf_normalized_effect_agreement bank _ _ Effect index). exact(Dut index Index).
Qed.
Require Import RFScalarControl RFPipelineEnable ReferenceInstructionDecode RFPreviewEffect ReferenceRedirectSpine.
Definition rf_isa_write_stage row :=if Nat.ltb row 23 then row else Nat.sub row 6.
Lemma rf_isa_write_stage_certificate row :(row<37)%coq_nat ->rf_isa_writes row=true ->(rf_isa_write_stage row<36)%coq_nat /\rf_write_decoder_index(rf_isa_write_stage row)=row.
Proof.
 intro Bound. do 37(destruct row as[|row];[vm_compute; intuition lia|]);lia.
Qed.
Definition rf_write_stage_match_check :=List.forallb(fun row=>List.forallb(fun stage=>if rf_isa_writes row then Bool.eqb(Nat.eqb(rf_write_decoder_index stage)row)(Nat.eqb stage(rf_isa_write_stage row))else true)(List.seq 0 36))(List.seq 0 37).
Lemma rf_write_stage_match_checked :rf_write_stage_match_check=true.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_write_stage_match row stage :(row<37)%coq_nat ->(stage<36)%coq_nat ->rf_isa_writes row=true ->Nat.eqb(rf_write_decoder_index stage)row=Nat.eqb stage(rf_isa_write_stage row).
Proof.
 intros Row Stage Writes. pose proof rf_write_stage_match_checked as Check. unfold rf_write_stage_match_check in Check.
 rewrite List.forallb_forall in Check. specialize(Check row ltac:(apply List.in_seq;lia)).
 rewrite List.forallb_forall in Check. specialize(Check stage ltac:(apply List.in_seq;lia)).
 rewrite Writes in Check. destruct (Nat.eqb (rf_write_decoder_index stage) row), (Nat.eqb stage (rf_isa_write_stage row));cbn in Check;congruence.
Qed.
Lemma rf_reference_effect_onehot guards permissions words destination target count :(target<count)%coq_nat ->
 (forall stage,(stage<count)%coq_nat ->guards stage=Nat.eqb stage target) ->
 rf_reference_effect guards permissions words destination count=
 if rf_reference_permission_value target(permissions target)then RFWrite destination(words target)else RFNoWrite.
Proof.
 induction count as[|count IH];intros Bound Guards;[lia|]. cbn[rf_reference_effect]. rewrite(Guards count ltac:(lia)).
 destruct(Nat.eq_dec count target)as[Same|Different].
 - subst target. rewrite Nat.eqb_refl. cbn[andb]. destruct(rf_reference_permission_value count(permissions count));[reflexivity|].
 apply rf_reference_effect_disabled. intros stage Stage. rewrite(Guards stage ltac:(lia)). apply Nat.eqb_neq;lia.
 - rewrite(proj2(Nat.eqb_neq count target)Different). cbn[andb]. apply IH;[lia|intros stage Stage;apply Guards;lia].
Qed.
Theorem rf_reference_class_write_effect instruction row permissions words destination :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->rf_isa_writes row=true ->
 rf_reference_effect(rf_write_opcode_bit instruction)permissions words destination 36=
 if rf_reference_permission_value(rf_isa_write_stage row)(permissions(rf_isa_write_stage row))then RFWrite destination(words(rf_isa_write_stage row))else RFNoWrite.
Proof.
 intros Row Match Writes. apply rf_reference_effect_onehot;[exact(proj1(rf_isa_write_stage_certificate row Row Writes))|].
 intros stage Stage. unfold rf_write_opcode_bit.
 rewrite(rf_reference_decode_onehot instruction row(rf_write_decoder_index stage)Row(proj1(rf_write_decoder_certificate stage Stage))Match).
 exact(rf_write_stage_match row stage Row Stage Writes).
Qed.
Lemma rf_instruction_nonzero_correct instruction :rf_instruction_nonzero instruction=(to_nat(rf_instruction_rd instruction)!=0%nat).
Proof.
 unfold rf_instruction_nonzero. rewrite -redirect_N_eqb (eq_sym(to_N(rf_instruction_rd instruction))0).
 rewrite(rf_preview_rd_match 0(rf_instruction_rd instruction))(eq_sym 0%nat(to_nat(rf_instruction_rd instruction))). reflexivity.
Qed.
Theorem rf_class_effect_agreement instruction row dut_data permissions words :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 (rf_isa_writes row=true ->rf_reference_permission_value(rf_isa_write_stage row)(permissions(rf_isa_write_stage row))=true) ->
 (rf_isa_writes row=true ->dut_data=words(rf_isa_write_stage row)) ->
 rf_effect_normalize(if rf_isa_writes row && rf_instruction_nonzero instruction then RFWrite(to_nat(rf_instruction_rd instruction))dut_data else RFNoWrite)=
 rf_effect_normalize(rf_reference_effect(rf_write_opcode_bit instruction)permissions words(to_nat(rf_instruction_rd instruction))36).
Proof.
 intros Row Match Permission Data. destruct(rf_isa_writes row)eqn:Writes.
 - rewrite(rf_reference_class_write_effect instruction row permissions words _ Row Match Writes)(Permission(Logic.eq_refl _)).
 cbn[andb]. rewrite rf_instruction_nonzero_correct.
 apply(rf_scalar_effect_agreement(to_nat(rf_instruction_rd instruction))dut_data(words(rf_isa_write_stage row))(to_nat(rf_instruction_rd instruction)!=0%nat)true).
 + rewrite andTb andbb. reflexivity.
 + intro Enabled. exact(Data(Logic.eq_refl _)).
 - rewrite(rf_reference_class_no_write instruction row permissions words _ Row Match Writes). reflexivity.
Qed.
