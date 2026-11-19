Require Import RFArchitecturalResetSources0 RFArchitecturalResetCommits0 RFArchitecturalResetSources1 RFArchitecturalResetCommits1 RFArchitecturalResetSources2 RFArchitecturalResetCommits2 RFArchitecturalResetSources3 RFArchitecturalResetCommits3 RFArchitecturalResetSources4 RFArchitecturalResetCommits4 RFArchitecturalResetSources5 RFArchitecturalResetCommits5 RFArchitecturalResetSources6 RFArchitecturalResetCommits6 RFArchitecturalResetSources7 RFArchitecturalResetCommits7 RFArchitecturalRelation StagedFlatCircuitIteration FormalLocalHistory StagedCircuitRegisterHold StagedRegisterHold FormalResetTrace FormalResetPreparation FormalRFResetControl ReferencePCResetHistory ObservedLegalNoTrap StagedIterationCount ObservedArchitecturalRegisters CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_architectural_history_concrete invalid history limit :
 rf_architectural_registers_concrete (history 0%nat) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (t <= limit)%coq_nat -> rf_architectural_registers_concrete (history t).
Proof.
 intros Initial Steps t. induction t as [|t IH]; intro Bound; [exact Initial|].
 intros node Member. destruct (rf_architectural_register_properties node Member) as [Present Rest].
 destruct (IH ltac:(lia) node Member) as [word [Size Value]]. exists word; split; [exact Size|].
 rewrite (staged_combinational_holds_registers invalid flat_memories (history t) (history t) (history (S t)) flat_statements (N.of_nat node) Present (Steps t ltac:(lia))). exact Value.
Qed.
Theorem rf_architectural_reset_local inputs path history limit current result :
 rf_architectural_registers_concrete (history limit) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (6 <= limit)%coq_nat ->
 VM.find 779 (history limit) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1515 (history limit) = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history limit) true current flat_statements = Some result ->
 rf_architectural_relation result.
Proof.
 intros Concrete Steps Bound ResetD ResetR Commit.
 unfold rf_architectural_relation, rf_architectural_register_pairs.
 apply List.Forall_cons.
 { exists (rfa_reset_word_0 inputs path). split; [apply rfa_reset_word_0_size|]. split.
   - assert (Member : List.In 851%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 0%nat). reflexivity. }
     destruct (Concrete 851%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_851 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_0 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_0_size|exact Commit].
     apply (rfa_reset_history_1085 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7299%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 1%nat). reflexivity. }
     destruct (Concrete 7299%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7299 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_0 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_0_size|exact Commit].
     apply (rfa_reset_history_7370 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_1 inputs path). split; [apply rfa_reset_word_1_size|]. split.
   - assert (Member : List.In 852%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 2%nat). reflexivity. }
     destruct (Concrete 852%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_852 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_1 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_1_size|exact Commit].
     apply (rfa_reset_history_1086 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7300%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 3%nat). reflexivity. }
     destruct (Concrete 7300%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7300 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_1 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_1_size|exact Commit].
     apply (rfa_reset_history_7372 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_2 inputs path). split; [apply rfa_reset_word_2_size|]. split.
   - assert (Member : List.In 853%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 4%nat). reflexivity. }
     destruct (Concrete 853%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_853 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_2 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_2_size|exact Commit].
     apply (rfa_reset_history_1087 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7301%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 5%nat). reflexivity. }
     destruct (Concrete 7301%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7301 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_2 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_2_size|exact Commit].
     apply (rfa_reset_history_7374 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_3 inputs path). split; [apply rfa_reset_word_3_size|]. split.
   - assert (Member : List.In 854%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 6%nat). reflexivity. }
     destruct (Concrete 854%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_854 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_3 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_3_size|exact Commit].
     apply (rfa_reset_history_1088 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7302%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 7%nat). reflexivity. }
     destruct (Concrete 7302%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7302 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_3 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_3_size|exact Commit].
     apply (rfa_reset_history_7376 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_4 inputs path). split; [apply rfa_reset_word_4_size|]. split.
   - assert (Member : List.In 855%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 8%nat). reflexivity. }
     destruct (Concrete 855%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_855 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_4 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_4_size|exact Commit].
     apply (rfa_reset_history_1089 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7303%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 9%nat). reflexivity. }
     destruct (Concrete 7303%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7303 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_4 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_4_size|exact Commit].
     apply (rfa_reset_history_7378 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_5 inputs path). split; [apply rfa_reset_word_5_size|]. split.
   - assert (Member : List.In 856%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 10%nat). reflexivity. }
     destruct (Concrete 856%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_856 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_5 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_5_size|exact Commit].
     apply (rfa_reset_history_1090 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7304%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 11%nat). reflexivity. }
     destruct (Concrete 7304%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7304 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_5 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_5_size|exact Commit].
     apply (rfa_reset_history_7380 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_6 inputs path). split; [apply rfa_reset_word_6_size|]. split.
   - assert (Member : List.In 857%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 12%nat). reflexivity. }
     destruct (Concrete 857%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_857 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_6 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_6_size|exact Commit].
     apply (rfa_reset_history_1091 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7305%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 13%nat). reflexivity. }
     destruct (Concrete 7305%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7305 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_6 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_6_size|exact Commit].
     apply (rfa_reset_history_7382 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_7 inputs path). split; [apply rfa_reset_word_7_size|]. split.
   - assert (Member : List.In 858%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 14%nat). reflexivity. }
     destruct (Concrete 858%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_858 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_7 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_7_size|exact Commit].
     apply (rfa_reset_history_1092 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7306%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 15%nat). reflexivity. }
     destruct (Concrete 7306%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7306 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_7 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_7_size|exact Commit].
     apply (rfa_reset_history_7384 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_8 inputs path). split; [apply rfa_reset_word_8_size|]. split.
   - assert (Member : List.In 859%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 16%nat). reflexivity. }
     destruct (Concrete 859%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_859 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_8 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_8_size|exact Commit].
     apply (rfa_reset_history_1093 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7307%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 17%nat). reflexivity. }
     destruct (Concrete 7307%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7307 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_8 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_8_size|exact Commit].
     apply (rfa_reset_history_7386 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_9 inputs path). split; [apply rfa_reset_word_9_size|]. split.
   - assert (Member : List.In 860%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 18%nat). reflexivity. }
     destruct (Concrete 860%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_860 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_9 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_9_size|exact Commit].
     apply (rfa_reset_history_1094 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7308%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 19%nat). reflexivity. }
     destruct (Concrete 7308%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7308 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_9 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_9_size|exact Commit].
     apply (rfa_reset_history_7388 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_10 inputs path). split; [apply rfa_reset_word_10_size|]. split.
   - assert (Member : List.In 861%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 20%nat). reflexivity. }
     destruct (Concrete 861%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_861 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_10 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_10_size|exact Commit].
     apply (rfa_reset_history_1095 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7309%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 21%nat). reflexivity. }
     destruct (Concrete 7309%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7309 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_10 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_10_size|exact Commit].
     apply (rfa_reset_history_7390 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_11 inputs path). split; [apply rfa_reset_word_11_size|]. split.
   - assert (Member : List.In 862%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 22%nat). reflexivity. }
     destruct (Concrete 862%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_862 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_11 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_11_size|exact Commit].
     apply (rfa_reset_history_1096 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7310%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 23%nat). reflexivity. }
     destruct (Concrete 7310%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7310 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_11 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_11_size|exact Commit].
     apply (rfa_reset_history_7392 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_12 inputs path). split; [apply rfa_reset_word_12_size|]. split.
   - assert (Member : List.In 863%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 24%nat). reflexivity. }
     destruct (Concrete 863%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_863 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_12 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_12_size|exact Commit].
     apply (rfa_reset_history_1097 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7311%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 25%nat). reflexivity. }
     destruct (Concrete 7311%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7311 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_12 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_12_size|exact Commit].
     apply (rfa_reset_history_7394 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_13 inputs path). split; [apply rfa_reset_word_13_size|]. split.
   - assert (Member : List.In 864%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 26%nat). reflexivity. }
     destruct (Concrete 864%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_864 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_13 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_13_size|exact Commit].
     apply (rfa_reset_history_1098 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7312%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 27%nat). reflexivity. }
     destruct (Concrete 7312%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7312 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_13 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_13_size|exact Commit].
     apply (rfa_reset_history_7396 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_14 inputs path). split; [apply rfa_reset_word_14_size|]. split.
   - assert (Member : List.In 865%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 28%nat). reflexivity. }
     destruct (Concrete 865%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_865 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_14 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_14_size|exact Commit].
     apply (rfa_reset_history_1099 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7313%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 29%nat). reflexivity. }
     destruct (Concrete 7313%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7313 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_14 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_14_size|exact Commit].
     apply (rfa_reset_history_7398 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_15 inputs path). split; [apply rfa_reset_word_15_size|]. split.
   - assert (Member : List.In 866%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 30%nat). reflexivity. }
     destruct (Concrete 866%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_866 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_15 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_15_size|exact Commit].
     apply (rfa_reset_history_1100 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7314%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 31%nat). reflexivity. }
     destruct (Concrete 7314%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7314 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_15 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_15_size|exact Commit].
     apply (rfa_reset_history_7400 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_16 inputs path). split; [apply rfa_reset_word_16_size|]. split.
   - assert (Member : List.In 867%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 32%nat). reflexivity. }
     destruct (Concrete 867%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_867 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_16 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_16_size|exact Commit].
     apply (rfa_reset_history_1101 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7315%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 33%nat). reflexivity. }
     destruct (Concrete 7315%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7315 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_16 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_16_size|exact Commit].
     apply (rfa_reset_history_7402 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_17 inputs path). split; [apply rfa_reset_word_17_size|]. split.
   - assert (Member : List.In 868%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 34%nat). reflexivity. }
     destruct (Concrete 868%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_868 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_17 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_17_size|exact Commit].
     apply (rfa_reset_history_1102 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7316%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 35%nat). reflexivity. }
     destruct (Concrete 7316%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7316 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_17 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_17_size|exact Commit].
     apply (rfa_reset_history_7404 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_18 inputs path). split; [apply rfa_reset_word_18_size|]. split.
   - assert (Member : List.In 869%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 36%nat). reflexivity. }
     destruct (Concrete 869%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_869 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_18 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_18_size|exact Commit].
     apply (rfa_reset_history_1103 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7317%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 37%nat). reflexivity. }
     destruct (Concrete 7317%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7317 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_18 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_18_size|exact Commit].
     apply (rfa_reset_history_7406 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_19 inputs path). split; [apply rfa_reset_word_19_size|]. split.
   - assert (Member : List.In 870%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 38%nat). reflexivity. }
     destruct (Concrete 870%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_870 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_19 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_19_size|exact Commit].
     apply (rfa_reset_history_1104 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7318%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 39%nat). reflexivity. }
     destruct (Concrete 7318%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7318 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_19 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_19_size|exact Commit].
     apply (rfa_reset_history_7408 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_20 inputs path). split; [apply rfa_reset_word_20_size|]. split.
   - assert (Member : List.In 871%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 40%nat). reflexivity. }
     destruct (Concrete 871%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_871 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_20 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_20_size|exact Commit].
     apply (rfa_reset_history_1105 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7319%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 41%nat). reflexivity. }
     destruct (Concrete 7319%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7319 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_20 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_20_size|exact Commit].
     apply (rfa_reset_history_7410 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_21 inputs path). split; [apply rfa_reset_word_21_size|]. split.
   - assert (Member : List.In 872%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 42%nat). reflexivity. }
     destruct (Concrete 872%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_872 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_21 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_21_size|exact Commit].
     apply (rfa_reset_history_1106 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7320%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 43%nat). reflexivity. }
     destruct (Concrete 7320%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7320 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_21 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_21_size|exact Commit].
     apply (rfa_reset_history_7412 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_22 inputs path). split; [apply rfa_reset_word_22_size|]. split.
   - assert (Member : List.In 873%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 44%nat). reflexivity. }
     destruct (Concrete 873%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_873 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_22 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_22_size|exact Commit].
     apply (rfa_reset_history_1107 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7321%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 45%nat). reflexivity. }
     destruct (Concrete 7321%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7321 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_22 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_22_size|exact Commit].
     apply (rfa_reset_history_7414 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_23 inputs path). split; [apply rfa_reset_word_23_size|]. split.
   - assert (Member : List.In 874%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 46%nat). reflexivity. }
     destruct (Concrete 874%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_874 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_23 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_23_size|exact Commit].
     apply (rfa_reset_history_1108 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7322%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 47%nat). reflexivity. }
     destruct (Concrete 7322%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7322 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_23 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_23_size|exact Commit].
     apply (rfa_reset_history_7416 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_24 inputs path). split; [apply rfa_reset_word_24_size|]. split.
   - assert (Member : List.In 875%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 48%nat). reflexivity. }
     destruct (Concrete 875%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_875 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_24 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_24_size|exact Commit].
     apply (rfa_reset_history_1109 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7323%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 49%nat). reflexivity. }
     destruct (Concrete 7323%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7323 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_24 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_24_size|exact Commit].
     apply (rfa_reset_history_7418 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_25 inputs path). split; [apply rfa_reset_word_25_size|]. split.
   - assert (Member : List.In 876%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 50%nat). reflexivity. }
     destruct (Concrete 876%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_876 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_25 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_25_size|exact Commit].
     apply (rfa_reset_history_1110 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7324%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 51%nat). reflexivity. }
     destruct (Concrete 7324%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7324 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_25 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_25_size|exact Commit].
     apply (rfa_reset_history_7420 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_26 inputs path). split; [apply rfa_reset_word_26_size|]. split.
   - assert (Member : List.In 877%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 52%nat). reflexivity. }
     destruct (Concrete 877%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_877 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_26 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_26_size|exact Commit].
     apply (rfa_reset_history_1111 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7325%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 53%nat). reflexivity. }
     destruct (Concrete 7325%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7325 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_26 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_26_size|exact Commit].
     apply (rfa_reset_history_7422 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_27 inputs path). split; [apply rfa_reset_word_27_size|]. split.
   - assert (Member : List.In 878%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 54%nat). reflexivity. }
     destruct (Concrete 878%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_878 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_27 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_27_size|exact Commit].
     apply (rfa_reset_history_1112 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7326%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 55%nat). reflexivity. }
     destruct (Concrete 7326%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7326 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_27 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_27_size|exact Commit].
     apply (rfa_reset_history_7424 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_28 inputs path). split; [apply rfa_reset_word_28_size|]. split.
   - assert (Member : List.In 879%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 56%nat). reflexivity. }
     destruct (Concrete 879%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_879 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_28 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_28_size|exact Commit].
     apply (rfa_reset_history_1113 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7327%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 57%nat). reflexivity. }
     destruct (Concrete 7327%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7327 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_28 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_28_size|exact Commit].
     apply (rfa_reset_history_7426 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_29 inputs path). split; [apply rfa_reset_word_29_size|]. split.
   - assert (Member : List.In 880%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 58%nat). reflexivity. }
     destruct (Concrete 880%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_880 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_29 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_29_size|exact Commit].
     apply (rfa_reset_history_1114 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7328%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 59%nat). reflexivity. }
     destruct (Concrete 7328%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7328 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_29 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_29_size|exact Commit].
     apply (rfa_reset_history_7428 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_30 inputs path). split; [apply rfa_reset_word_30_size|]. split.
   - assert (Member : List.In 881%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 60%nat). reflexivity. }
     destruct (Concrete 881%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_881 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_30 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_30_size|exact Commit].
     apply (rfa_reset_history_1115 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7329%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 61%nat). reflexivity. }
     destruct (Concrete 7329%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7329 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_30 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_30_size|exact Commit].
     apply (rfa_reset_history_7430 inputs path history limit Steps limit); lia.
 }
 apply List.Forall_cons.
 { exists (rfa_reset_word_31 inputs path). split; [apply rfa_reset_word_31_size|]. split.
   - assert (Member : List.In 882%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 62%nat). reflexivity. }
     destruct (Concrete 882%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_882 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_31 inputs path));
     [exact Old|reflexivity|exact ResetD| |apply rfa_reset_word_31_size|exact Commit].
     apply (rfa_reset_history_1116 inputs path history limit Steps limit); lia.
   - assert (Member : List.In 7330%nat rf_architectural_register_ids).
     { apply (List.nth_error_In rf_architectural_register_ids 63%nat). reflexivity. }
     destruct (Concrete 7330%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_7330 (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_31 inputs path));
     [exact Old|reflexivity|exact ResetR| |apply rfa_reset_word_31_size|exact Commit].
     apply (rfa_reset_history_7432 inputs path history limit Steps limit); lia.
 }
 constructor.
Qed.
Theorem rf_architectural_settle_reset_commit inputs initial stable result :
 state_reset initial true ->
 rf_architectural_registers_concrete (top_environment initial) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_architectural_relation env.
Proof.
 intros Reset Concrete Iterations Commit.
 destruct (rf_control_9259 inputs initial stable true Reset Iterations) as [control [Control ResetD]].
 destruct Reset as [start [Start Reset]].
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Start. exact Reset. }
 pose proof (legal_local_reset_history _ history 9259 true Steps Reset0) as Resets.
 pose proof (reference_pc_reset_after_four (formal_invalid_policy inputs nil)
 (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) true
 (Resets 9255%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia))
 (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as ResetR.
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit)
 as [before [after [Before [Local After]]]].
 assert (HistoryBefore : history 9259%nat = before).
 { rewrite Last. unfold top_environment. rewrite Before. reflexivity. }
 rewrite <- HistoryBefore in Local.
 assert (D : VM.find 779 (history 9259%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite Last. unfold top_environment. rewrite Control. exact ResetD. }
 exists after; split; [exact After|].
 apply (rf_architectural_reset_local inputs nil history 9259 (history 9259%nat) after).
 - apply (rf_architectural_history_concrete (formal_invalid_policy inputs nil) history 9259); [rewrite First;exact Concrete|exact Steps|lia].
 - exact Steps.
 - vm_compute; lia.
 - exact D.
 - exact ResetR.
 - exact Local.
Qed.
Theorem rf_architectural_real_reset_cycle inputs previous old result :
 SVM.find nil previous = Some old -> rf_architectural_registers_concrete old ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_architectural_relation env.
Proof.
 intros Previous Concrete Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Steps; [|discriminate Cycle].
 apply (rf_architectural_settle_reset_commit inputs initial stable result); [| |exact Steps|exact Cycle].
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - exact (rf_architectural_prepared_concrete previous old _ initial Previous Concrete Prepare).
Qed.
Theorem rf_architectural_after_formal_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ rf_architectural_relation env.
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init; [|discriminate]. intro Reset.
 destruct (rf_architectural_symbolic_initial_concrete memory inputs initial Init) as [old [Old Concrete]].
 apply (rf_architectural_real_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states Old Concrete); [|exact Reset].
 unfold force_formal_reset. cbn [formal_external_inputs]. apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Theorem rf_architectural_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\ rf_architectural_relation env.
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset; [|discriminate].
 cbn [circuit_formal_run]. intro Run. inversion Run; subst states.
 exact (rf_architectural_after_formal_reset memory (inputs 0%nat) initial Reset).
Qed.
