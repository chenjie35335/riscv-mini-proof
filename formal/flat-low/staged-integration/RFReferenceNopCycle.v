Require Import CoreSocModel ComparisonNodes RFReferenceNopHistory RFReferenceNopInputs RFWriteEffect FormalInstructionResetConstants CheckerValidBubbleValue FormalCheckerValidStability ReferencePCResetHistory.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_reference_nop_checker_enabled invalid history :
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 forall time, ((12 <= time)%coq_nat /\ (time <= 9259)%coq_nat) ->
 VM.find 1395 (history time) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Steps Resets Bubble time Bounds.
 pose proof (checker_valid_history_from_bubble invalid history false Steps Resets Bubble) as Final.
 pose proof (checker_valid_history_stable invalid history 9259 (Nat.sub time 12) 9247 false Steps Resets ltac:(lia) ltac:(vm_compute;lia)) as Same.
 replace (Nat.add (Nat.sub time 12) 12) with time in Same by lia.
 change (VM.find 1395 (history time) = VM.find 1395 (history 9259%nat)) in Same.
 rewrite Same. exact Final.
Qed.
Theorem rf_reference_nop_fullhistory_sources invalid history bank :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 forall index, (index < 32)%coq_nat -> VM.find (N.of_nat (Nat.add 1787 index)) (history 9259%nat) = Some (Gval (Fuint 32) (bank index)).
Proof.
 intros Bank Zero Instruction Steps Resets Bubble.
 exact (rf_reference_nop_from_writeback_sources invalid history 9259 12 bank Bank Zero Instruction
 (rf_reference_nop_checker_enabled invalid history Steps Resets Bubble) Steps 9259 ltac:(vm_compute;lia)).
Qed.
Theorem rf_reference_nop_fullhistory_commit invalid history bank result :
 rf_reference_bank_at (history 0%nat) bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 rf_reference_bank_at result (fun index => rf_apply_effect bank RFNoWrite index).
Proof.
 intros Bank Zero Instruction Steps Resets Bubble Commit.
 eapply (rf_reference_nop_from_writeback_commit invalid history 9259 12 bank result Bank Zero Instruction);
 [vm_compute;lia|exact (rf_reference_nop_checker_enabled invalid history Steps Resets Bubble)|exact Steps| |exact Commit].
 eapply (reference_pc_reset_after_four invalid (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) false);
 [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps];vm_compute;lia.
Qed.
Require Import FormalInstructionResetCycle FormalResetTrace ObservedLegalNoTrap StagedCircuitRegisterHold RFArchitecturalRelation StagedObservedRegister StagedRegisterHold FormalLocalHistory StagedFlatCircuitIteration StagedIterationCount FormalResetPreparation FormalInstructionWordsNormalCommit PipelineBubbleInitialization ExceptionPCSourceRegisters.
Lemma rf_reference_bank_prepared previous old external initial bank :
 SVM.find nil previous = Some old -> rf_reference_bank_at old bank ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial ->
 rf_reference_bank_at (top_environment initial) bank.
Proof.
 intros Previous Bank Prepare index Bound. destruct (Bank index Bound) as [Size Value]. split;[exact Size|].
 pose proof (rf_reference_register_member index Bound) as Member.
 destruct (rf_architectural_nonexternal _ Member) as [Nonclock Nonreset].
 destruct (rf_architectural_register_properties _ Member) as [Present [Typed Safe]].
 pose proof (staged_prepared_register_copies previous old external initial _ Nonclock Nonreset Safe Present Previous Prepare) as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy. unfold top_environment.
 destruct (SVM.find nil initial);[exact Copy|discriminate Copy].
Qed.
Theorem rf_reference_nop_settle_and_commit inputs initial stable result bank :
 rf_reference_bank_at (top_environment initial) bank -> bank 0%nat = nseq 32 false ->
 staged_register_lookup 7750 initial = Some (Gval (Fuint 32) instruction_nop) ->
 staged_register_lookup 7947 initial = Some (Gval (Fuint 1) [::false]) ->
 state_reset initial false ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_reference_bank_at env (fun index => rf_apply_effect bank RFNoWrite index).
Proof.
 intros Bank Zero Instruction Bubble Reset Iterations Commit.
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Instruction0 : VM.find 7750 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop)).
 { rewrite First. unfold staged_register_lookup in Instruction. unfold top_environment.
   destruct (SVM.find nil initial);[exact Instruction|discriminate Instruction]. }
 assert (Bubble0 : VM.find 7947 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold staged_register_lookup in Bubble. unfold top_environment.
   destruct (SVM.find nil initial);[exact Bubble|discriminate Bubble]. }
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. destruct Reset as [env [Env Value]]. unfold top_environment. rewrite Env. exact Value. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 assert (BubbleEnd : VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite (flat_register_history_same _ history 9259 7947 formal_checker_bubble_register Steps 9259 ltac:(vm_compute;lia)). exact Bubble0. }
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit) as [before [after [Before [Local After]]]].
 exists after. split;[exact After|].
 assert (BeforeEq : history 9259%nat = before).
 { rewrite Last. unfold top_environment. rewrite Before. reflexivity. }
 eapply (rf_reference_nop_fullhistory_commit (formal_invalid_policy inputs nil) history bank after);
 [rewrite First;exact Bank|exact Zero|exact Instruction0|exact Steps|exact Resets|exact BubbleEnd|].
 rewrite BeforeEq. exact Local.
Qed.
Theorem rf_reference_nop_real_cycle inputs previous old result bank :
 SVM.find nil previous = Some old -> rf_reference_bank_at old bank -> bank 0%nat = nseq 32 false ->
 VM.find 7750 old = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 7947 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::false]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_reference_bank_at env (fun index => rf_apply_effect bank RFNoWrite index).
Proof.
 intros Previous Bank Zero Instruction Bubble Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare;[|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Iterations;[|discriminate Cycle].
 eapply rf_reference_nop_settle_and_commit; [|exact Zero| | | |exact Iterations|exact Cycle].
 - exact (rf_reference_bank_prepared previous old _ initial bank Previous Bank Prepare).
 - destruct (instruction_register_shape 7750 ltac:(vm_compute;reflexivity)) as [Safe Present].
   rewrite (staged_prepared_register_copies previous old _ initial 7750 (Logic.eq_refl _) (Logic.eq_refl _) Safe Present Previous Prepare). exact Instruction.
 - rewrite (staged_prepared_register_copies previous old _ initial 7947 (Logic.eq_refl _) (Logic.eq_refl _) bubble7947_initial_safe bubble7947_present Previous Prepare). exact Bubble.
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
Qed.
Require Import RFArchitecturalNormalRelation FlatRegFileX0.
Definition rf_architectural_bank env (index:nat) : bits :=
 match VM.find (N.of_nat (851+index)%nat) env with Some (Gval _ word) => word | _ => nseq 32 false end.
Lemma rf_architectural_pair_member (index:nat) : (index < 32)%coq_nat ->
 List.In ((851+index)%nat,(7299+index)%nat) rf_architectural_register_pairs.
Proof.
 intros Bound. apply (List.nth_error_In rf_architectural_register_pairs index).
 do 32 (destruct index as [|index]; [vm_compute;reflexivity|]). lia.
Qed.
Lemma rf_architectural_relation_banks env : rf_architectural_relation env ->
 rf_dut_bank_at env (rf_architectural_bank env) /\ rf_reference_bank_at env (rf_architectural_bank env).
Proof.
 intro Relation. unfold rf_architectural_relation in Relation. rewrite List.Forall_forall in Relation.
 assert (Both : forall index, (index < 32)%coq_nat ->
 size (rf_architectural_bank env index) = 32%nat /\
 VM.find (N.of_nat (851+index)%nat) env = Some (Gval (Fuint 32) (rf_architectural_bank env index)) /\
 VM.find (N.of_nat (7299+index)%nat) env = Some (Gval (Fuint 32) (rf_architectural_bank env index))).
 { intros index Bound. destruct (Relation _ (rf_architectural_pair_member index Bound)) as [word [Size [Dut Ref]]].
   cbn [fst snd] in Dut,Ref. unfold rf_architectural_bank. rewrite Dut. exact (conj Size (conj (Logic.eq_refl _) Ref)). }
 split;intros index Bound;destruct (Both index Bound) as [Size [Dut Ref]];split;assumption.
Qed.
Lemma rf_architectural_pairs_indexed pair : List.In pair rf_architectural_register_pairs ->
 exists index, (index < 32)%coq_nat /\ pair = ((851+index)%nat,(7299+index)%nat).
Proof.
 intro Member. cbn [rf_architectural_register_pairs] in Member.
 destruct Member as [Equal|Member].
 - exists 0%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 1%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 2%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 3%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 4%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 5%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 6%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 7%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 8%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 9%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 10%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 11%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 12%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 13%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 14%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 15%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 16%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 17%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 18%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 19%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 20%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 21%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 22%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 23%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 24%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 25%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 26%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 27%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 28%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 29%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 30%nat. split;[lia|symmetry;exact Equal].
 destruct Member as [Equal|Member].
 - exists 31%nat. split;[lia|symmetry;exact Equal].
 contradiction.
Qed.
Lemma rf_architectural_banks_relation env bank :
 rf_dut_bank_at env bank -> rf_reference_bank_at env bank -> rf_architectural_relation env.
Proof.
 intros Dut Ref. unfold rf_architectural_relation. apply List.Forall_forall. intros pair Member.
 destruct (rf_architectural_pairs_indexed pair Member) as [index [Bound Pair]]. subst pair.
 destruct (Dut index Bound) as [Size D]. destruct (Ref index Bound) as [_ R].
 exists (bank index). exact (conj Size (conj D R)).
Qed.
Theorem rf_architectural_nop_real_cycle inputs previous old result :
 SVM.find nil previous = Some old -> rf_architectural_relation old ->
 VM.find 851 old = Some rf_zero32 ->
 VM.find 7750 old = Some (Gval (Fuint 32) instruction_nop) ->
 VM.find 7947 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::false]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_architectural_relation env.
Proof.
 intros Previous Relation X0 Instruction Bubble Reset Cycle.
 destruct (rf_architectural_relation_banks old Relation) as [Dut Ref].
 assert (Zero : rf_architectural_bank old 0%nat = nseq 32 false).
 { unfold rf_architectural_bank. change (match VM.find 851 old with Some (Gval _ word) => word | _ => nseq 32 false end = nseq 32 false).
   rewrite X0. reflexivity. }
 destruct (rf_dut_nop_real_cycle_effect inputs previous old result _ Previous Dut Zero Instruction Reset Cycle) as [denv [Denv Dbank]].
 destruct (rf_reference_nop_real_cycle inputs previous old result _ Previous Ref Zero Instruction Bubble Reset Cycle) as [renv [Renv Rbank]].
 rewrite Denv in Renv. inversion Renv;subst renv.
 exists denv. split;[exact Denv|]. eapply rf_architectural_banks_relation;[exact Dbank|exact Rbank].
Qed.
