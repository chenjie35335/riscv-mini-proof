Require Import CoreSocModel ComparisonNodes RFReferenceNopRelation RFReferenceNopStorageCertificates RFReferenceNopDecode.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_reference_chain_member (index stage : nat) :
 ((1 <= index)%coq_nat /\ (index < 32)%coq_nat) -> (stage < 36)%coq_nat ->
 List.In (rf_reference_chain_node index stage,rf_reference_chain_expr index stage) rf_reference_chain_nodes.
Proof.
 intros Index Stage. unfold rf_reference_chain_nodes.
 apply List.in_flat_map. exists index. split; [apply List.in_seq;lia|].
 apply List.in_map_iff. exists stage. split; [reflexivity|apply List.in_seq;lia].
Qed.
Definition rf_reference_chain_guard (stage : nat) : VarOrder.T :=
 N.of_nat (let '(_,guard,_) := nth (0%nat,0%nat,0%nat) rf_reference_chain_specs stage in guard).
Local Opaque rf_reference_chain_nodes rf_reference_chain_specs.
Lemma rf_reference_chain_false_step invalid old result (index stage : nat) base input :
 ((1 <= index)%coq_nat /\ (index < 32)%coq_nat) -> ((0 < stage)%coq_nat /\ (stage < 36)%coq_nat) ->
 size base = 32%nat -> rf_reference_word_extension base input ->
 VM.find (rf_reference_chain_guard stage) old = Some (Gval (Fuint 1) [::false]) ->
 VM.find (rf_reference_chain_node index (stage-1)) old = Some input ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (rf_reference_chain_node index stage) result = Some value /\ rf_reference_word_extension base value.
Proof.
 intros Index Stage Size Ext Guard Input Step.
 pose proof (rf_reference_chain_member index stage Index ltac:(lia)) as Member.
 unfold rf_reference_chain_expr in Member.
 unfold rf_reference_chain_guard in Guard.
 destruct stage as [|stage]; [lia|].
 destruct (nth (0%nat,0%nat,0%nat) rf_reference_chain_specs stage.+1) as [[node guard]yes] eqn:Spec.
 cbn in Member,Guard.
 eapply rf_reference_word_false_node;
 [exact rf_reference_chain_positions|exact rf_reference_chain_safety|exact Member|exact Size|exact Ext|exact Guard|exact Input|exact Step].
Qed.
Lemma rf_reference_chain_first_step invalid old result (index : nat) base input :
 ((1 <= index)%coq_nat /\ (index < 32)%coq_nat) ->
 size base = 32%nat -> rf_reference_word_extension base input ->
 VM.find 2096 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find (N.of_nat (3223+index)) old = Some input ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 exists value, VM.find (rf_reference_chain_node index 0) result = Some value /\ rf_reference_word_extension base value.
Proof.
 intros Index Size Ext Guard Input Step.
 pose proof (rf_reference_chain_member index 0 Index ltac:(lia)) as Member.
 change (List.In (rf_reference_chain_node index 0,
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2096))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (3223+index))))
 (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (2177-index))))) rf_reference_chain_nodes) in Member.
 eapply rf_reference_word_true_node;
 [exact rf_reference_chain_positions|exact rf_reference_chain_safety|exact Member|exact Size|exact Ext|exact Guard|exact Input|exact Step].
Qed.
Lemma rf_reference_chain_guard_member (stage : nat) :
 ((0 < stage)%coq_nat /\ (stage < 36)%coq_nat) ->
 List.In (rf_reference_chain_guard stage,false) rf_reference_nop_guards.
Proof.
 intros Bounds.
 do 36 (destruct stage as [|stage]; [try lia; vm_compute; tauto|]). lia.
Qed.
Theorem rf_reference_nop_chain_history invalid history (limit start index : nat) word :
 ((1 <= index)%coq_nat /\ (index < 32)%coq_nat) -> size word = 32%nat ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
   exists value, VM.find (N.of_nat (3223+index)) (history time) = Some value /\ rf_reference_word_extension word value) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
   forall node bit, List.In (node,bit) rf_reference_nop_guards -> VM.find node (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall stage time, (stage < 36)%coq_nat -> ((Nat.add start (S stage) <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 exists value, VM.find (rf_reference_chain_node index stage) (history time) = Some value /\ rf_reference_word_extension word value.
Proof.
 intros Index Size Entry Guards Steps stage. induction stage as [|stage IH]; intros time Stage Bounds.
 - destruct time as [|time]; [lia|]. destruct (Entry time ltac:(lia)) as [value [Value Ext]].
   eapply rf_reference_chain_first_step; [exact Index|exact Size|exact Ext| |exact Value|apply Steps;lia].
   apply (Guards time ltac:(lia)). vm_compute. tauto.
 - destruct time as [|time]; [lia|]. destruct (IH time ltac:(lia) ltac:(lia)) as [value [Value Ext]].
   eapply (rf_reference_chain_false_step invalid (history time) (history (S time)) index (S stage));
   [exact Index|lia|exact Size|exact Ext| | |apply Steps;lia].
   + apply (Guards time ltac:(lia)). apply rf_reference_chain_guard_member. lia.
   + replace (stage.+1 - 1)%nat with stage by (rewrite subn1;reflexivity). exact Value.
Qed.
Require Import RFReferenceNopEntry FormalInstructionResetConstants.
Theorem rf_reference_nop_nonzero_chain invalid history (limit start index : nat) word :
 ((1 <= index)%coq_nat /\ (index < 32)%coq_nat) -> size word = 32%nat ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction_nop)) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find (N.of_nat (2177-index)) (history time) = Some (Gval (Fuint 32) word)) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, ((Nat.add start 84 <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 exists value, VM.find (rf_reference_chain_node index 35) (history time) = Some value /\ rf_reference_word_extension word value.
Proof.
 intros Index Size Instruction Enable Old Steps time Bounds.
 pose proof (rf_reference_nop_decode_history invalid history limit start Instruction Enable Steps) as Decode.
 eapply (rf_reference_nop_chain_history invalid history limit (Nat.add start 48) index word Index Size); [| |exact Steps|lia|lia].
 - intros t B. destruct t as [|t]; [lia|].
   destruct (Decode t ltac:(lia)) as [RD Guards].
   eapply rf_reference_nop_entry; [exact (proj1 Index)|exact (proj2 Index)|exact Size|exact RD|apply Old;lia|apply Steps;lia].
 - intros t B. exact (proj2 (Decode t ltac:(lia))).
Qed.
Require Import RFWriteEffect RFArchitecturalRelation StagedRegisterHold.
Definition rf_reference_bank_at env (bank : rf_bank) : Prop := forall index, (index < 32)%coq_nat ->
 size (bank index) = 32%nat /\ VM.find (N.of_nat (7299+index)%nat) env = Some (Gval (Fuint 32) (bank index)).
Lemma rf_reference_register_member (index : nat) : (index < 32)%coq_nat ->
 List.In (7299+index)%nat rf_architectural_register_ids.
Proof.
 intro Bound. apply (List.nth_error_In rf_architectural_register_ids (2*index+1)%nat).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_reference_bank_comb_hold invalid old current result bank :
 rf_reference_bank_at old bank -> formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 rf_reference_bank_at result bank.
Proof.
 intros Bank Step index Bound. destruct (Bank index Bound) as [Size Value]. split;[exact Size|].
 destruct (rf_architectural_register_properties _ (rf_reference_register_member index Bound)) as [Present Rest].
 rewrite (staged_combinational_holds_registers invalid flat_memories old current result flat_statements _ Present Step). exact Value.
Qed.
Lemma rf_reference_bank_history_hold invalid history (limit : nat) bank :
 rf_reference_bank_at (history 0%nat) bank ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (t <= limit)%coq_nat -> rf_reference_bank_at (history t) bank.
Proof.
 intros Initial Steps t. induction t as [|t IH]; intro Bound;[exact Initial|].
 exact (rf_reference_bank_comb_hold invalid (history t) (history t) (history (S t)) bank (IH ltac:(lia)) (Steps t ltac:(lia))).
Qed.

Require Import RegisterCommitCertificate FormalStatementSegments RegisterInvariants ScalarNodeFrames FormalTypedNodeFrames FormalUIntRegisterCommitSource NormalUIntMuxIdentity UIntMuxResultType.
Require Import RFArchitecturalResetCommits0 RFArchitecturalResetCommits1 RFArchitecturalResetCommits2 RFArchitecturalResetCommits3 RFArchitecturalResetCommits4 RFArchitecturalResetCommits5 RFArchitecturalResetCommits6 RFArchitecturalResetCommits7.
Lemma rf_reference_normal_commit_certificate count declared middle tail node reg yes no invalid old current result old_value word :
 straight_drop count flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T node reg) declared) ->
 declared = statement_append middle (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T node) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no)))) tail) ->
 straight_statements middle -> formal_typed_suffix_safe flat_memories node middle -> formal_typed_suffix_safe flat_memories node tail -> register_identity_b node flat_statements ->
 VM.find node old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find no old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find node result = Some (Gval (Fuint 32) word).
Proof.
 intros Position Split Straight MiddleSafe TailSafe Identity Old Typed Reset Source Size Commit.
 destruct (formal_committed_uint_register_mux_observation count flat_statements declared middle tail node reg
 (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no)) invalid flat_memories old current result old_value 32
 Position Split Straight MiddleSafe TailSafe Old Typed Identity Commit) as [source [value [Eval [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source) in Eval.
 pose proof (unselected_uint_mux_identity flat_memories old 1515 yes no 32 word source value Size Reset Source Eval Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rf_reference_normal_commit_value invalid old current result (index : nat) old_value word :
 (index < 32)%coq_nat ->
 VM.find (N.of_nat (7299+index)%nat) old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find (N.of_nat (1787+index)%nat) old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find (N.of_nat (7299+index)%nat) result = Some (Gval (Fuint 32) word).
Proof.
 intros Bound Old Typed Reset Source Size Commit.
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7470 rfa_register_7299_decl rfa_register_7299_mid rfa_register_7299_tail 7299 rfa_register_7299_reg 7370 1787 invalid old current result old_value word
 rfa_register_7299_position rfa_register_7299_split rfa_register_7299_straight rfa_register_7299_mid_safe rfa_register_7299_tail_safe rfa_register_7299_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7471 rfa_register_7300_decl rfa_register_7300_mid rfa_register_7300_tail 7300 rfa_register_7300_reg 7372 1788 invalid old current result old_value word
 rfa_register_7300_position rfa_register_7300_split rfa_register_7300_straight rfa_register_7300_mid_safe rfa_register_7300_tail_safe rfa_register_7300_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7472 rfa_register_7301_decl rfa_register_7301_mid rfa_register_7301_tail 7301 rfa_register_7301_reg 7374 1789 invalid old current result old_value word
 rfa_register_7301_position rfa_register_7301_split rfa_register_7301_straight rfa_register_7301_mid_safe rfa_register_7301_tail_safe rfa_register_7301_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7473 rfa_register_7302_decl rfa_register_7302_mid rfa_register_7302_tail 7302 rfa_register_7302_reg 7376 1790 invalid old current result old_value word
 rfa_register_7302_position rfa_register_7302_split rfa_register_7302_straight rfa_register_7302_mid_safe rfa_register_7302_tail_safe rfa_register_7302_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7474 rfa_register_7303_decl rfa_register_7303_mid rfa_register_7303_tail 7303 rfa_register_7303_reg 7378 1791 invalid old current result old_value word
 rfa_register_7303_position rfa_register_7303_split rfa_register_7303_straight rfa_register_7303_mid_safe rfa_register_7303_tail_safe rfa_register_7303_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7475 rfa_register_7304_decl rfa_register_7304_mid rfa_register_7304_tail 7304 rfa_register_7304_reg 7380 1792 invalid old current result old_value word
 rfa_register_7304_position rfa_register_7304_split rfa_register_7304_straight rfa_register_7304_mid_safe rfa_register_7304_tail_safe rfa_register_7304_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7476 rfa_register_7305_decl rfa_register_7305_mid rfa_register_7305_tail 7305 rfa_register_7305_reg 7382 1793 invalid old current result old_value word
 rfa_register_7305_position rfa_register_7305_split rfa_register_7305_straight rfa_register_7305_mid_safe rfa_register_7305_tail_safe rfa_register_7305_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7477 rfa_register_7306_decl rfa_register_7306_mid rfa_register_7306_tail 7306 rfa_register_7306_reg 7384 1794 invalid old current result old_value word
 rfa_register_7306_position rfa_register_7306_split rfa_register_7306_straight rfa_register_7306_mid_safe rfa_register_7306_tail_safe rfa_register_7306_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7478 rfa_register_7307_decl rfa_register_7307_mid rfa_register_7307_tail 7307 rfa_register_7307_reg 7386 1795 invalid old current result old_value word
 rfa_register_7307_position rfa_register_7307_split rfa_register_7307_straight rfa_register_7307_mid_safe rfa_register_7307_tail_safe rfa_register_7307_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7479 rfa_register_7308_decl rfa_register_7308_mid rfa_register_7308_tail 7308 rfa_register_7308_reg 7388 1796 invalid old current result old_value word
 rfa_register_7308_position rfa_register_7308_split rfa_register_7308_straight rfa_register_7308_mid_safe rfa_register_7308_tail_safe rfa_register_7308_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7480 rfa_register_7309_decl rfa_register_7309_mid rfa_register_7309_tail 7309 rfa_register_7309_reg 7390 1797 invalid old current result old_value word
 rfa_register_7309_position rfa_register_7309_split rfa_register_7309_straight rfa_register_7309_mid_safe rfa_register_7309_tail_safe rfa_register_7309_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7481 rfa_register_7310_decl rfa_register_7310_mid rfa_register_7310_tail 7310 rfa_register_7310_reg 7392 1798 invalid old current result old_value word
 rfa_register_7310_position rfa_register_7310_split rfa_register_7310_straight rfa_register_7310_mid_safe rfa_register_7310_tail_safe rfa_register_7310_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7482 rfa_register_7311_decl rfa_register_7311_mid rfa_register_7311_tail 7311 rfa_register_7311_reg 7394 1799 invalid old current result old_value word
 rfa_register_7311_position rfa_register_7311_split rfa_register_7311_straight rfa_register_7311_mid_safe rfa_register_7311_tail_safe rfa_register_7311_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7483 rfa_register_7312_decl rfa_register_7312_mid rfa_register_7312_tail 7312 rfa_register_7312_reg 7396 1800 invalid old current result old_value word
 rfa_register_7312_position rfa_register_7312_split rfa_register_7312_straight rfa_register_7312_mid_safe rfa_register_7312_tail_safe rfa_register_7312_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7484 rfa_register_7313_decl rfa_register_7313_mid rfa_register_7313_tail 7313 rfa_register_7313_reg 7398 1801 invalid old current result old_value word
 rfa_register_7313_position rfa_register_7313_split rfa_register_7313_straight rfa_register_7313_mid_safe rfa_register_7313_tail_safe rfa_register_7313_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7485 rfa_register_7314_decl rfa_register_7314_mid rfa_register_7314_tail 7314 rfa_register_7314_reg 7400 1802 invalid old current result old_value word
 rfa_register_7314_position rfa_register_7314_split rfa_register_7314_straight rfa_register_7314_mid_safe rfa_register_7314_tail_safe rfa_register_7314_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7486 rfa_register_7315_decl rfa_register_7315_mid rfa_register_7315_tail 7315 rfa_register_7315_reg 7402 1803 invalid old current result old_value word
 rfa_register_7315_position rfa_register_7315_split rfa_register_7315_straight rfa_register_7315_mid_safe rfa_register_7315_tail_safe rfa_register_7315_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7487 rfa_register_7316_decl rfa_register_7316_mid rfa_register_7316_tail 7316 rfa_register_7316_reg 7404 1804 invalid old current result old_value word
 rfa_register_7316_position rfa_register_7316_split rfa_register_7316_straight rfa_register_7316_mid_safe rfa_register_7316_tail_safe rfa_register_7316_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7488 rfa_register_7317_decl rfa_register_7317_mid rfa_register_7317_tail 7317 rfa_register_7317_reg 7406 1805 invalid old current result old_value word
 rfa_register_7317_position rfa_register_7317_split rfa_register_7317_straight rfa_register_7317_mid_safe rfa_register_7317_tail_safe rfa_register_7317_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7489 rfa_register_7318_decl rfa_register_7318_mid rfa_register_7318_tail 7318 rfa_register_7318_reg 7408 1806 invalid old current result old_value word
 rfa_register_7318_position rfa_register_7318_split rfa_register_7318_straight rfa_register_7318_mid_safe rfa_register_7318_tail_safe rfa_register_7318_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7490 rfa_register_7319_decl rfa_register_7319_mid rfa_register_7319_tail 7319 rfa_register_7319_reg 7410 1807 invalid old current result old_value word
 rfa_register_7319_position rfa_register_7319_split rfa_register_7319_straight rfa_register_7319_mid_safe rfa_register_7319_tail_safe rfa_register_7319_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7491 rfa_register_7320_decl rfa_register_7320_mid rfa_register_7320_tail 7320 rfa_register_7320_reg 7412 1808 invalid old current result old_value word
 rfa_register_7320_position rfa_register_7320_split rfa_register_7320_straight rfa_register_7320_mid_safe rfa_register_7320_tail_safe rfa_register_7320_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7492 rfa_register_7321_decl rfa_register_7321_mid rfa_register_7321_tail 7321 rfa_register_7321_reg 7414 1809 invalid old current result old_value word
 rfa_register_7321_position rfa_register_7321_split rfa_register_7321_straight rfa_register_7321_mid_safe rfa_register_7321_tail_safe rfa_register_7321_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7493 rfa_register_7322_decl rfa_register_7322_mid rfa_register_7322_tail 7322 rfa_register_7322_reg 7416 1810 invalid old current result old_value word
 rfa_register_7322_position rfa_register_7322_split rfa_register_7322_straight rfa_register_7322_mid_safe rfa_register_7322_tail_safe rfa_register_7322_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7494 rfa_register_7323_decl rfa_register_7323_mid rfa_register_7323_tail 7323 rfa_register_7323_reg 7418 1811 invalid old current result old_value word
 rfa_register_7323_position rfa_register_7323_split rfa_register_7323_straight rfa_register_7323_mid_safe rfa_register_7323_tail_safe rfa_register_7323_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7495 rfa_register_7324_decl rfa_register_7324_mid rfa_register_7324_tail 7324 rfa_register_7324_reg 7420 1812 invalid old current result old_value word
 rfa_register_7324_position rfa_register_7324_split rfa_register_7324_straight rfa_register_7324_mid_safe rfa_register_7324_tail_safe rfa_register_7324_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7496 rfa_register_7325_decl rfa_register_7325_mid rfa_register_7325_tail 7325 rfa_register_7325_reg 7422 1813 invalid old current result old_value word
 rfa_register_7325_position rfa_register_7325_split rfa_register_7325_straight rfa_register_7325_mid_safe rfa_register_7325_tail_safe rfa_register_7325_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7497 rfa_register_7326_decl rfa_register_7326_mid rfa_register_7326_tail 7326 rfa_register_7326_reg 7424 1814 invalid old current result old_value word
 rfa_register_7326_position rfa_register_7326_split rfa_register_7326_straight rfa_register_7326_mid_safe rfa_register_7326_tail_safe rfa_register_7326_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7498 rfa_register_7327_decl rfa_register_7327_mid rfa_register_7327_tail 7327 rfa_register_7327_reg 7426 1815 invalid old current result old_value word
 rfa_register_7327_position rfa_register_7327_split rfa_register_7327_straight rfa_register_7327_mid_safe rfa_register_7327_tail_safe rfa_register_7327_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7499 rfa_register_7328_decl rfa_register_7328_mid rfa_register_7328_tail 7328 rfa_register_7328_reg 7428 1816 invalid old current result old_value word
 rfa_register_7328_position rfa_register_7328_split rfa_register_7328_straight rfa_register_7328_mid_safe rfa_register_7328_tail_safe rfa_register_7328_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7500 rfa_register_7329_decl rfa_register_7329_mid rfa_register_7329_tail 7329 rfa_register_7329_reg 7430 1817 invalid old current result old_value word
 rfa_register_7329_position rfa_register_7329_split rfa_register_7329_straight rfa_register_7329_mid_safe rfa_register_7329_tail_safe rfa_register_7329_identity Old Typed Reset Source Size Commit).
 destruct index as [|index].
 - exact (rf_reference_normal_commit_certificate 7501 rfa_register_7330_decl rfa_register_7330_mid rfa_register_7330_tail 7330 rfa_register_7330_reg 7432 1818 invalid old current result old_value word
 rfa_register_7330_position rfa_register_7330_split rfa_register_7330_straight rfa_register_7330_mid_safe rfa_register_7330_tail_safe rfa_register_7330_identity Old Typed Reset Source Size Commit).
 lia.
Qed.
Theorem rf_reference_no_write_commit invalid old current result bank :
 rf_reference_bank_at old bank ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::false]) ->
 (forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (1787+index)%nat) old = Some (Gval (Fuint 32) (bank index))) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 rf_reference_bank_at result bank.
Proof.
 intros Bank Reset Sources Step index Bound. destruct (Bank index Bound) as [Size Value]. split;[exact Size|].
 eapply rf_reference_normal_commit_value; [exact Bound|exact Value|reflexivity|exact Reset|apply Sources;exact Bound|exact Size|exact Step].
Qed.
Require Import RFReferenceNopExit RFReferenceNopIngress FormalReferenceX0 FormalReferenceX0Connections.
Lemma rf_reference_chain_last_node (index:nat) : (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 rf_reference_chain_node index 35 = rf_exit_node 3614 index.
Proof.
 intros Lower Upper. do 32 (destruct index as [|index]; [try lia;vm_compute;reflexivity|]). lia.
Qed.
Theorem rf_reference_nop_nonzero_source invalid history (limit start index : nat) word :
 ((1 <= index)%coq_nat /\ (index < 32)%coq_nat) -> size word = 32%nat ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction_nop)) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find (N.of_nat (2177-index)) (history time) = Some (Gval (Fuint 32) word)) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, ((Nat.add start 87 <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 VM.find (N.of_nat (Nat.add 1787 index)) (history time) = Some (Gval (Fuint 32) word).
Proof.
 intros Index Size Instruction Enable Old Steps time Bounds.
 do 3 (destruct time as [|time]; [lia|]).
 destruct (rf_reference_nop_nonzero_chain invalid history limit start index word Index Size Instruction Enable Old Steps time ltac:(lia)) as [value [Value Ext]].
 rewrite (rf_reference_chain_last_node index (proj1 Index) (proj2 Index)) in Value.
 eapply rf_reference_nop_exit; [exact (proj1 Index)|exact (proj2 Index)|exact Size|exact Ext|exact Value|apply Enable;lia|apply Steps;lia|apply Steps;lia|apply Steps;lia].
Qed.
Theorem rf_reference_nop_sources invalid history (limit start : nat) bank :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false -> (2 <= start)%coq_nat ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction_nop)) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, ((Nat.add start 87 <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1787 index)) (history time) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Start Instruction Enable Steps time Bounds index Index.
 pose proof (rf_reference_bank_history_hold invalid history limit bank Bank Steps) as Banks.
 assert (Old : forall t, ((start <= t)%coq_nat /\ (t <= limit)%coq_nat) ->
  VM.find (N.of_nat (Nat.sub 2177 index)) (history t) = Some (Gval (Fuint 32) (bank index))).
 { intros t B. do 2 (destruct t as [|t]; [lia|]).
   destruct (Banks t ltac:(lia) index Index) as [Size Value].
   eapply rf_reference_old_word_ingress; [exact Index|exact Size|exact Value|apply Steps;lia|apply Steps;lia]. }
 destruct index as [|index].
 - rewrite Zero. do 3 (destruct time as [|time]; [lia|]).
   assert (Entry : VM.find 3255 (history (S time)) = Some (Gval (Fuint 32) (nseq 32 false))).
   { eapply (rf_reference_nop_x0_entry invalid (history time) (history time) (history (S time))); [apply Enable;lia|rewrite <- Zero;apply Old;lia|apply Steps;lia]. }
   assert (Alias : VM.find 3256 (history (S (S time))) = Some (Gval (Fuint 32) (nseq 32 false))).
   { eapply reference_x0_node_3256; [|reflexivity|apply Steps;lia].
     cbn [reference_x0_expr_3256 eval_hfexpr_with_memory eval_href_with_memory]. exact Entry. }
   eapply reference_output_connection_1787; [exact Alias|reflexivity|apply Steps;lia].
 - destruct (Bank (S index) Index) as [Size _].
   eapply rf_reference_nop_nonzero_source; [lia|exact Size|exact Instruction|exact Enable|exact Old|exact Steps|exact Bounds].
Qed.
Theorem rf_reference_nop_commit invalid history (limit start : nat) bank result :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 (2 <= start)%coq_nat -> (Nat.add start 87 <= limit)%coq_nat ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1706 (history time) = Some (Gval (Fuint 32) instruction_nop)) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1707 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 VM.find 1515 (history limit) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories (history limit) true (history limit) flat_statements = Some result ->
 rf_reference_bank_at result (fun index => rf_apply_effect bank RFNoWrite index).
Proof.
 intros Bank Zero Start Limit Instruction Enable Steps Reset Commit.
 assert (Result : rf_reference_bank_at result bank).
 { eapply (rf_reference_no_write_commit invalid (history limit) (history limit) result bank);
   [exact (rf_reference_bank_history_hold invalid history limit bank Bank Steps limit (Nat.le_refl _))|exact Reset| |exact Commit].
   exact (rf_reference_nop_sources invalid history limit start bank Bank Zero Start Instruction Enable Steps limit ltac:(lia)). }
 intros index Index. rewrite (rf_apply_effect_no_write bank Zero index). exact (Result index Index).
Qed.
Require Import RFReferenceNopInputs.
Theorem rf_reference_nop_from_writeback_sources invalid history (limit start:nat) bank :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1395 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, ((Nat.add start 90 <= time)%coq_nat /\ (time <= limit)%coq_nat) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1787 index)) (history time) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Instruction Enable Steps time Bounds.
 eapply (rf_reference_nop_sources invalid history limit (Nat.add start 3) bank Bank Zero); [lia| | |exact Steps|lia].
 - intros t B. eapply rf_reference_nop_inputs_history; [exact Instruction|exact Steps|lia|lia].
 - intros t B. eapply (rf_reference_enable_inputs_history invalid history limit start (fun t Lo Hi => Enable t (conj Lo Hi)) Steps);lia.
Qed.
Theorem rf_reference_nop_from_writeback_commit invalid history (limit start:nat) bank result :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (Nat.add start 90 <= limit)%coq_nat ->
 (forall time, ((start <= time)%coq_nat /\ (time <= limit)%coq_nat) -> VM.find 1395 (history time) = Some (Gval (Fuint 1) [::true])) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 VM.find 1515 (history limit) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories (history limit) true (history limit) flat_statements = Some result ->
 rf_reference_bank_at result (fun index => rf_apply_effect bank RFNoWrite index).
Proof.
 intros Bank Zero Instruction Limit Enable Steps Reset Commit.
 eapply (rf_reference_nop_commit invalid history limit (Nat.add start 3) bank result Bank Zero); [lia|lia| | |exact Steps|exact Reset|exact Commit].
 - intros t B. eapply rf_reference_nop_inputs_history; [exact Instruction|exact Steps|lia|lia].
 - intros t B. eapply (rf_reference_enable_inputs_history invalid history limit start (fun t Lo Hi => Enable t (conj Lo Hi)) Steps);lia.
Qed.
