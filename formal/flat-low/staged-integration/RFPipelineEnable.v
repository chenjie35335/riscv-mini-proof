Require Import RFNonAluBubbleHazard RFScalarControl CoreSocModel ComparisonNodes ControlWritebackKill JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization EarlyBubbleNopFullHistory ExceptionSourceNoTrap FormalStallHistory FormalCheckerResetConnections FormalPipelineControlHistory InstructionNormalTransfer ExceptionPCSourceRegisters FormalInstructionResetConstants.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Definition rf_instruction_nonzero instruction :=negb(N.eqb(to_N(rf_instruction_rd instruction))0).
Definition rf_pipeline_enable_invariant env :=forall instruction enabled,
 VM.find 7750 env=Some(Gval(Fuint 32)instruction) ->VM.find 7757 env=Some(Gval(Fuint 1)[::enabled]) ->
 enabled && rf_instruction_nonzero instruction=wbkill_enable(wbkill_decode 49 instruction) && rf_instruction_nonzero instruction.
Lemma rf_pipeline_enable_instruction_member :List.In(7750%nat,32%nat)joint_boundary_registers.
Proof. apply(List.nth_error_In joint_boundary_registers 55%nat). vm_compute;reflexivity. Qed.
Lemma rf_pipeline_enable_reset env :VM.find 7750 env=Some(Gval(Fuint 32)instruction_nop) ->rf_pipeline_enable_invariant env.
Proof.
 intros Nop instruction enabled Instruction Enable. rewrite Nop in Instruction. inversion Instruction;subst instruction.
 change(enabled && false=wbkill_enable(wbkill_decode 49 instruction_nop)&&false). rewrite !andbF. reflexivity.
Qed.
Theorem rf_pipeline_enable_normal_fullhistory inputs path history result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time < 9259)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 (forall time, (time <= 9259)%coq_nat -> VM.find 1 (history time) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 45 (history 9254%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 rf_pipeline_enable_invariant result.
Proof.
 intros Boundary Steps Resets NoTrap Commit.
 destruct (Boundary 7748%nat 32%nat early_bubble_front_instruction_member) as [instruction [Size Initial]].
 pose proof (control_writeback_decode_history _ history 9259 instruction Size Initial Steps) as Decode.
 destruct (Decode 9257%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as [_ [Mode Enabled]].
 pose proof (proj1 (Decode 9254%nat ltac:(vm_compute;lia) ltac:(vm_compute;lia))) as Kill.
 pose proof (wbkill_decode_safe 49 instruction ltac:(lia)) as Safe.
 destruct (wbkill_decode 49 instruction) as [kill low high enabled] eqn:Decoded.
 cbn [wbkill_kill wbkill_low wbkill_high wbkill_enable wbkill_safe] in Mode,Enabled,Kill,Safe.
 assert (Stall : forall time, ((6 <= time)%coq_nat /\ (time <= 9259)%coq_nat) -> VM.find 7765 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time Bounds. do 6 (destruct time as [|time];[lia|]).
   eapply (stall_after_six _ (history time) (history (S time)) (history (S (S time))) (history (S (S (S time)))) (history (S (S (S (S time))))) (history (S (S (S (S (S time)))))) (history (S (S (S (S (S (S time))))))) false);
   [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps];lia. }
 assert (Reset65 : forall time, ((2 <= time)%coq_nat /\ (time <= 9259)%coq_nat) -> VM.find 65 (history time) = Some (Gval (Fuint 1) [::false])).
 { intros time Bounds. do 2 (destruct time as [|time];[lia|]).
   eapply (reset_connection_65_transfer _ (history (S time)) (history (S time)) (history (S (S time))) false);[|apply Steps;lia].
   eapply (reset_connection_24_transfer _ (history time) (history time) (history (S time)) false);[apply Resets;lia|apply Steps;lia]. }
 pose proof (exception_source_false_after_settling inputs path history Boundary Steps NoTrap) as Exception.
 assert (Advance : VM.find 7855 (history 9257%nat) = Some (Gval (Fuint 1) [::true])).
 { eapply (pipeline_advance_after_two _ (history 9255%nat) (history 9256%nat) (history 9257%nat) false false);
   [apply Stall|apply Exception|apply Steps|apply Steps];vm_compute;lia. }
 assert (Flush : VM.find 7852 (history 9258%nat) = Some (Gval (Fuint 1) [::false])).
 { eapply (pipeline_flush_after_three _ (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) false false false);
   [apply Stall|apply Exception|apply Reset65|apply Steps|apply Steps|apply Steps];vm_compute;lia. }
 destruct (joint_update_register_history_concrete _ history 9259 7756 2 rf_nonalu_mode_member (Boundary _ _ rf_nonalu_mode_member) Steps 9257 ltac:(vm_compute;lia)) as [old_mode [OldModeSize OldMode]].
 destruct old_mode as [|old_low [|old_high [|extra rest]]];try discriminate OldModeSize.
 destruct (joint_update_register_history_concrete _ history 9259 7757 1 rf_nonalu_enable_member (Boundary _ _ rf_nonalu_enable_member) Steps 9257 ltac:(vm_compute;lia)) as [old_enable [OldEnableSize OldEnable]].
 destruct old_enable as [|old_enabled [|extra rest]];try discriminate OldEnableSize.
 destruct (rf_writeback_controls_advance _ (history 9257%nat) (history 9258%nat) (history 9259%nat) result old_low old_high old_enabled low high enabled OldMode OldEnable Mode Enabled Advance Flush (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia)) Commit) as [NextMode NextEnable].

 destruct(Boundary 7750%nat 32%nat rf_pipeline_enable_instruction_member)as[old_word[OldSize OldInitial]].
 assert(FrontFinal:VM.find 7748(history 9259%nat)=Some(Gval(Fuint 32)instruction)).
 { rewrite(flat_register_history_same _ history 9259 7748 (proj2(joint_boundary_register_properties 7748 32 early_bubble_front_instruction_member)) Steps 9259 ltac:(vm_compute;lia)). exact Initial. }
 assert(OldFinal:VM.find 7750(history 9259%nat)=Some(Gval(Fuint 32)old_word)).
 { rewrite(flat_register_history_same _ history 9259 7750 (proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member)) Steps 9259 ltac:(vm_compute;lia)). exact OldInitial. }
 pose proof(instruction_transfer_normal_full_history inputs path history result instruction old_word Boundary Steps Resets NoTrap Size FrontFinal OldFinal Commit)as NextInstruction.
 intros next_instruction next_enabled Instruction Enable.
 rewrite NextInstruction in Instruction. inversion Instruction;subst next_instruction.
 rewrite NextEnable in Enable. inversion Enable;subst next_enabled.
 rewrite Decoded. reflexivity.
Qed.

Require Import FormalLocalHistory FormalObservationCommit StagedFlatCircuitIteration ObservedLegalNoTrap JointBoundaryReachable JointBoundaryInitialization JointBoundaryPreparation FormalFetchType FormalResetPreparation.
Theorem rf_pipeline_enable_normal_successor memory inputs k observed next :
 generated_observe memory inputs k = Some observed -> generated_legal_trace memory inputs k ->
 generated_run memory inputs (S k) = Some next ->
 VM.find 1 (formal_external_inputs (generated_observation_input inputs k)) = Some (Gval (Fuint 1) [::false]) ->
 rf_pipeline_enable_invariant (top_environment next).
Proof.
 intros Observe Legal Next Reset.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width Member (Registers node width Member) Env Prepare). }
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [initial_env [InitialEnv InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite InitialEnv. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.
 rewrite (observation_then_commit memory inputs k observed Observe) in Next.
 destruct (flat_iteration_projection _ observed true next Next) as [before [after [Before [Step After]]]].
 assert (Top : top_environment observed = before) by (unfold top_environment;rewrite Before;reflexivity).
 unfold top_environment. rewrite After. rewrite <- Top in Step. rewrite <- Last in Step.
 exact (rf_pipeline_enable_normal_fullhistory (generated_observation_input inputs k) nil history after Boundary Steps Resets NoTrap Step).
Qed.
Require Import StagedRegisterHold StagedCircuitRegisterHold RegisterPreparationFrames StagedObservedRegister.
Lemma rf_pipeline_enable_comb_hold invalid old current result :rf_pipeline_enable_invariant old ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->rf_pipeline_enable_invariant result.
Proof.
 intros Invariant Step instruction enabled Instruction Enable.
 rewrite(staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Step)in Instruction.
 rewrite(staged_combinational_holds_registers invalid flat_memories old current result flat_statements 7757(proj2(joint_boundary_register_properties 7757 1 rf_nonalu_enable_member))Step)in Enable.
 exact(Invariant instruction enabled Instruction Enable).
Qed.
Lemma rf_pipeline_enable_history_hold invalid history limit :rf_pipeline_enable_invariant(history 0%nat) ->
 (forall time,(time<limit)%coq_nat ->formal_value_iter invalid flat_memories(history time)false(history time)flat_statements=Some(history(S time))) ->
 forall time,(time<=limit)%coq_nat ->rf_pipeline_enable_invariant(history time).
Proof.
 intros Initial Steps time. induction time as[|time IH];intro Bound;[exact Initial|].
 exact(rf_pipeline_enable_comb_hold invalid(history time)(history time)(history(S time))(IH ltac:(lia))(Steps time ltac:(lia))).
Qed.
Lemma rf_pipeline_enable_prepared previous old external initial :SVM.find nil previous=Some old ->rf_pipeline_enable_invariant old ->
 circuit_initial_map_with_memory generated_modules generated_top(Some previous)external=Some initial ->rf_pipeline_enable_invariant(top_environment initial).
Proof.
 intros Previous Invariant Prepare.
 assert(Copy:forall node width,List.In(node,width)joint_boundary_registers ->staged_register_lookup(N.of_nat node)initial=VM.find(N.of_nat node)old).
 { intros node width Member. pose proof joint_boundary_preparation_check as Check.
 rewrite List.forallb_forall in Check. specialize(Check(node,width)Member). cbn[fst snd]in Check.
 move/andP:Check=>[/andP[Safe NotClock]NotReset].
 exact(staged_prepared_register_copies previous old external initial _ NotClock NotReset Safe(proj2(joint_boundary_register_properties node width Member))Previous Prepare). }
 pose proof(Copy 7750%nat 32%nat rf_pipeline_enable_instruction_member)as InstructionCopy.
 pose proof(Copy 7757%nat 1%nat rf_nonalu_enable_member)as EnableCopy.
 intros instruction enabled Instruction Enable.
 unfold staged_register_lookup in InstructionCopy,EnableCopy. unfold top_environment in *.
 destruct(SVM.find nil initial)as[env|];[|discriminate Instruction].
 rewrite InstructionCopy in Instruction. rewrite EnableCopy in Enable. exact(Invariant instruction enabled Instruction Enable).
Qed.
Require Import FormalInstructionResetBase FormalInstructionResetCycle JointBoundaryInduction ExternalReset.
From firrtl Require Import FormalInitialization.
Theorem rf_pipeline_enable_run memory inputs k states :generated_run memory inputs k=Some states ->generated_legal_trace memory inputs k ->rf_pipeline_enable_invariant(top_environment states).
Proof.
 destruct k as[|k];intros Run Legal.
 - destruct(instruction_run_zero memory inputs states Run)as[env[Env[Front Instruction]]].
 unfold top_environment. rewrite Env. exact(rf_pipeline_enable_reset env Instruction).
 - assert(PriorLegal:generated_legal_trace memory inputs k)by(apply(joint_legal_trace_prefix memory inputs(S k)k Legal);lia).
 destruct(legal_observation_reset memory inputs k PriorLegal)as[reset Reset]. destruct reset.
 + pose proof Run as Next. rewrite generated_run_successor in Next.
 destruct(generated_run memory inputs k)as[previous|]eqn:Previous;[|discriminate Next].
 destruct(fetch9220_run_type memory inputs k previous Previous)as[old[value[Old Rest]]].
 destruct(joint_boundary_reachable memory inputs k previous Previous PriorLegal)as[Registers Storage].
 unfold top_environment in Registers. rewrite Old in Registers.
 destruct(Registers 7748%nat 32%nat early_bubble_front_instruction_member)as[front[FrontSize Front]].
 destruct(Registers 7750%nat 32%nat rf_pipeline_enable_instruction_member)as[instruction[Size Instruction]].
 destruct(instruction_real_reset_cycle(generated_observation_input inputs k)previous old states(Gval(Fuint 32)front)(Gval(Fuint 32)instruction)Old Front(Logic.eq_refl _)Instruction(Logic.eq_refl _)Reset Next)as[env[Env[NewFront NewInstruction]]].
 unfold top_environment. rewrite Env. exact(rf_pipeline_enable_reset env NewInstruction).
 + destruct(generated_successful_commit memory inputs k states Run)as[observed[Observe Commit]].
 exact(rf_pipeline_enable_normal_successor memory inputs k observed states Observe PriorLegal Run Reset).
Qed.
Require Import StagedIterationCount.
Theorem rf_pipeline_enable_observed memory inputs k observed :generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->rf_pipeline_enable_invariant(top_environment observed).
Proof.
 intros Observe Legal. pose proof Observe as Expanded. unfold generated_observe,generated_observe_cycle in Expanded.
 destruct(generated_run memory inputs k)as[previous|]eqn:Run;[|discriminate Expanded].
 destruct(circuit_initial_map_with_memory generated_modules generated_top(Some previous)(formal_external_inputs(generated_observation_input inputs k)))as[initial|]eqn:Prepare;[|discriminate Expanded].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Expanded.
 destruct(local_iteration_history(generated_observation_input inputs k)9259 initial observed Expanded)as[history[First[Last Steps]]].
 pose proof(rf_pipeline_enable_run memory inputs k previous Run Legal)as Invariant.
 destruct(fetch9220_run_type memory inputs k previous Run)as[old[value[Old Rest]]].
 unfold top_environment in Invariant. rewrite Old in Invariant.
 rewrite <-Last. eapply(rf_pipeline_enable_history_hold _ history 9259);[rewrite First;exact(rf_pipeline_enable_prepared previous old _ initial Old Invariant Prepare)|exact Steps|vm_compute;lia].
Qed.


Require Import ReferenceInstructionDecode ReferenceRedirectSpine.
From Coq Require Import NArith.
Definition rf_wb_class_indices :seq nat :=[::30%nat;29%nat;28%nat;25%nat;26%nat;27%nat;24%nat;23%nat;22%nat;48%nat;47%nat;21%nat;18%nat;17%nat;12%nat;13%nat;16%nat;19%nat;15%nat;20%nat;14%nat;46%nat;45%nat;44%nat;43%nat;42%nat;40%nat;41%nat;39%nat;38%nat;37%nat;36%nat;35%nat;34%nat;33%nat;32%nat;31%nat].
Definition rf_wb_class_index row :=nth 0%nat rf_wb_class_indices row.
Definition rf_wb_row stage :=nth wbkill_default_row wbkill_rows stage.
Lemma rf_wb_class_certificate row :(row<37)%coq_nat ->
 (rf_wb_class_index row<49)%coq_nat /\to_N(wbkill_mask(rf_wb_row(rf_wb_class_index row)))=reference_instruction_mask row /\to_N(wbkill_code(rf_wb_row(rf_wb_class_index row)))=reference_instruction_code row /\wbkill_enable(wbkill_row_value(rf_wb_row(rf_wb_class_index row)))=rf_isa_writes row.
Proof. intro Bound. do 37(destruct row as[|row];[vm_compute;repeat split;lia|]);lia. Qed.
Definition rf_wb_disjoint_check :=List.forallb(fun row=>List.forallb(fun stage=>Nat.eqb stage(rf_wb_class_index row) || negb(N.eqb(N.land(reference_instruction_code row)(to_N(wbkill_mask(rf_wb_row stage))))(N.land(to_N(wbkill_code(rf_wb_row stage)))(reference_instruction_mask row))))(List.seq 0 49))(List.seq 0 37).
Lemma rf_wb_disjoint_checked :rf_wb_disjoint_check=true.
Proof. vm_compute;reflexivity. Qed.
Lemma rf_wb_disjoint row stage :(row<37)%coq_nat ->(stage<49)%coq_nat ->stage<>rf_wb_class_index row ->
 N.land(reference_instruction_code row)(to_N(wbkill_mask(rf_wb_row stage)))<>N.land(to_N(wbkill_code(rf_wb_row stage)))(reference_instruction_mask row).
Proof.
 intros Row Stage Different. pose proof rf_wb_disjoint_checked as Check. unfold rf_wb_disjoint_check in Check.
 rewrite List.forallb_forall in Check. specialize(Check row ltac:(apply List.in_seq;lia)).
 rewrite List.forallb_forall in Check. specialize(Check stage ltac:(apply List.in_seq;lia)).
 rewrite(proj2(Nat.eqb_neq stage(rf_wb_class_index row))Different)in Check. cbn[orb]in Check.
 apply N.eqb_neq. apply Bool.negb_true_iff in Check. exact Check.
Qed.
Lemma rf_wb_choice_onehot instruction row stage :(row<37)%coq_nat ->(stage<49)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 wbkill_choice instruction(rf_wb_row stage)=Nat.eqb stage(rf_wb_class_index row).
Proof.
 intros Row Stage Match. unfold wbkill_choice. rewrite redirect_to_N_and redirect_N_eqb.
 destruct(Nat.eq_dec stage(rf_wb_class_index row))as[Same|Different].
 - subst stage. destruct(rf_wb_class_certificate row Row)as[Bound[Mask[Code Enable]]].
 rewrite Mask Code Match Nat.eqb_refl N.eqb_refl. reflexivity.
 - rewrite(proj2(Nat.eqb_neq stage(rf_wb_class_index row))Different). apply N.eqb_neq. intro Other.
 apply(rf_wb_disjoint row stage Row Stage Different).
 rewrite -Match Other -!N.land_assoc (N.land_comm(reference_instruction_mask row)(to_N(wbkill_mask(rf_wb_row stage)))). reflexivity.
Qed.
Lemma rf_wb_decode_selected instruction target count :(target<count)%coq_nat ->
 (forall stage,(stage<count)%coq_nat ->wbkill_choice instruction(rf_wb_row stage)=Nat.eqb stage target) ->
 wbkill_decode count instruction=wbkill_row_value(rf_wb_row target).
Proof.
 induction count as[|count IH];intros Bound Choices;[lia|].
 change((if wbkill_choice instruction(rf_wb_row count)then wbkill_row_value(rf_wb_row count)else wbkill_decode count instruction)=wbkill_row_value(rf_wb_row target)).
 rewrite(Choices count ltac:(lia)). destruct(Nat.eq_dec count target)as[Same|Different].
 - subst count. rewrite Nat.eqb_refl. reflexivity.
 - rewrite(proj2(Nat.eqb_neq count target)Different). apply IH;[lia|intros stage Stage;apply Choices;lia].
Qed.
Theorem rf_wb_legal_write_enable instruction row :(row<37)%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->wbkill_enable(wbkill_decode 49 instruction)=rf_isa_writes row.
Proof.
 intros Row Match. destruct(rf_wb_class_certificate row Row)as[Bound[Mask[Code Enable]]].
 rewrite(rf_wb_decode_selected instruction(rf_wb_class_index row)49 Bound).
 - exact Enable.
 - intros stage Stage. exact(rf_wb_choice_onehot instruction row stage Row Stage Match).
Qed.
Theorem rf_pipeline_isa_write_enable_observed memory inputs k observed instruction enabled row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->VM.find 7757(top_environment observed)=Some(Gval(Fuint 1)[::enabled]) ->
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 enabled && rf_instruction_nonzero instruction=rf_isa_writes row && rf_instruction_nonzero instruction.
Proof.
 intros Observe Legal Instruction Enabled Row Match.
 pose proof(rf_pipeline_enable_observed memory inputs k observed Observe Legal instruction enabled Instruction Enabled)as Agree.
 rewrite(rf_wb_legal_write_enable instruction row Row Match)in Agree. exact Agree.
Qed.
Require Import X0ConcreteExpressionCertificates X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine FormalRFInputConnections FormalRFWriteEnable FormalRFDestination FormalX0AddressStability.
Lemma rf_pipeline_wen_after_four invalid s0 s1 s2 s3 s4 enabled :
 VM.find 7765 s0=Some(Gval(Fuint 1)[::false]) ->VM.find 7757 s1=Some(Gval(Fuint 1)[::enabled]) ->VM.find 128 s1=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 formal_value_iter invalid flat_memories s2 false s2 flat_statements=Some s3 ->
 formal_value_iter invalid flat_memories s3 false s3 flat_statements=Some s4 ->
 VM.find 784 s4=Some(Gval(Fuint 1)[::enabled]).
Proof.
 intros Stall Enable Exception S1 S2 S3 S4.
 assert(A:VM.find 7938 s1=Some(Gval(Fuint 1)[::true])).
 { eapply(reference_redirect_ground_step x0_node_offsets x0_expected_nodes 7938 x0_concrete_expr_7938);[exact x0_actual_node_expressions|exact x0_actual_nodes_safe|apply(List.nth_error_In x0_expected_nodes 153);reflexivity| |exact S1].
 intros site. cbn[x0_concrete_expr_7938 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Stall. reflexivity. }
 assert(B:VM.find 7939 s2=Some(Gval(Fuint 1)[::enabled])).
 { eapply(reference_redirect_ground_step x0_node_offsets x0_expected_nodes 7939 x0_concrete_expr_7939);[exact x0_actual_node_expressions|exact x0_actual_nodes_safe|apply(List.nth_error_In x0_expected_nodes 154);reflexivity| |exact S2].
 intros site. cbn[x0_concrete_expr_7939 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enable A. destruct enabled;reflexivity. }
 assert(C:VM.find 7940 s2=Some(Gval(Fuint 1)[::true])).
 { eapply(reference_redirect_ground_step x0_node_offsets x0_expected_nodes 7940 x0_concrete_expr_7940);[exact x0_actual_node_expressions|exact x0_actual_nodes_safe|apply(List.nth_error_In x0_expected_nodes 155);reflexivity| |exact S2].
 intros site. cbn[x0_concrete_expr_7940 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Exception. reflexivity. }
 assert(D:VM.find 7941 s3=Some(Gval(Fuint 1)[::enabled])).
 { eapply(reference_redirect_ground_step x0_node_offsets x0_expected_nodes 7941 x0_concrete_expr_7941);[exact x0_actual_node_expressions|exact x0_actual_nodes_safe|apply(List.nth_error_In x0_expected_nodes 156);reflexivity| |exact S3].
 intros site. cbn[x0_concrete_expr_7941 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite B C. destruct enabled;reflexivity. }
 eapply rf_input_connection_784;[exact D| |exact S4]. destruct enabled;reflexivity.
Qed.
Lemma rf_nonzero_five word :size word=5%nat ->foldr orb false word=negb(N.eqb(to_N word)0).
Proof.
 intro Size. destruct(five_bits_decompose word Size)as[a[b[c[d[e Same]]]]]. subst word.
 destruct a,b,c,d,e;reflexivity.
Qed.
Theorem rf_pipeline_gate_fullhistory inputs path history instruction enabled :
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall time,(time<9259)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history time)false(history time)flat_statements=Some(history(S time))) ->
 (forall time,(time<=9259)%coq_nat ->VM.find 1(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 45(history 9254%nat)=Some(Gval(Fuint 1)[::false]) ->size instruction=32%nat ->
 VM.find 7750(history 9259%nat)=Some(Gval(Fuint 32)instruction) ->VM.find 7757(history 9259%nat)=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 954(history 9259%nat)=Some(Gval(Fuint 1)[::enabled && rf_instruction_nonzero instruction]).
Proof.
 intros Boundary Steps Resets NoTrap Size Instruction Enable.
 assert(Inst:VM.find 7750(history 9255%nat)=Some(Gval(Fuint 32)instruction)).
 { rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9255 ltac:(vm_compute;lia)).
 rewrite(flat_register_history_same _ history 9259 7750(proj2(joint_boundary_register_properties 7750 32 rf_pipeline_enable_instruction_member))Steps 9259 ltac:(vm_compute;lia))in Instruction. exact Instruction. }
 assert(En:VM.find 7757(history 9255%nat)=Some(Gval(Fuint 1)[::enabled])).
 { rewrite(flat_register_history_same _ history 9259 7757(proj2(joint_boundary_register_properties 7757 1 rf_nonalu_enable_member))Steps 9255 ltac:(vm_compute;lia)).
 rewrite(flat_register_history_same _ history 9259 7757(proj2(joint_boundary_register_properties 7757 1 rf_nonalu_enable_member))Steps 9259 ltac:(vm_compute;lia))in Enable. exact Enable. }
 assert(Stall:VM.find 7765(history 9254%nat)=Some(Gval(Fuint 1)[::false])).
 { exact(stall_after_six _ (history 9248%nat)(history 9249%nat)(history 9250%nat)(history 9251%nat)(history 9252%nat)(history 9253%nat)(history 9254%nat)false(Resets 9248 ltac:(vm_compute;lia))(Steps 9248 ltac:(vm_compute;lia))(Steps 9249 ltac:(vm_compute;lia))(Steps 9250 ltac:(vm_compute;lia))(Steps 9251 ltac:(vm_compute;lia))(Steps 9252 ltac:(vm_compute;lia))(Steps 9253 ltac:(vm_compute;lia))). }
 pose proof(exception_source_false_after_settling inputs path history Boundary Steps NoTrap 9255 ltac:(vm_compute;lia)ltac:(vm_compute;lia))as Exception.
 pose proof(rf_pipeline_wen_after_four _ (history 9254%nat)(history 9255%nat)(history 9256%nat)(history 9257%nat)(history 9258%nat)enabled Stall En Exception(Steps 9254 ltac:(vm_compute;lia))(Steps 9255 ltac:(vm_compute;lia))(Steps 9256 ltac:(vm_compute;lia))(Steps 9257 ltac:(vm_compute;lia)))as Wen.
 pose proof(rf_destination_port_after_two _ (history 9255%nat)(history 9256%nat)(history 9257%nat)instruction Size Inst(Steps 9255 ltac:(vm_compute;lia))(Steps 9256 ltac:(vm_compute;lia)))as RD.
 pose proof(rf_address_nonzero_node _ (history 9257%nat)(history 9257%nat)(history 9258%nat)(rf_instruction_rd instruction)RD(Steps 9257 ltac:(vm_compute;lia)))as Nonzero.
 rewrite(rf_nonzero_five _ (rf_instruction_rd_size instruction Size))in Nonzero.
 exact(rf_write_enable_node _ (history 9258%nat)(history 9258%nat)(history 9259%nat)enabled(rf_instruction_nonzero instruction)Wen Nonzero(Steps 9258 ltac:(vm_compute;lia))).
Qed.

Require Import ObservedLegalNoTrap JointBoundaryReachable JointBoundaryPreparation FormalFetchType FormalResetPreparation ObservedJointRegisterConcrete.
Theorem rf_pipeline_gate_observed memory inputs k observed instruction enabled :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->VM.find 7757(top_environment observed)=Some(Gval(Fuint 1)[::enabled]) ->
 VM.find 954(top_environment observed)=Some(Gval(Fuint 1)[::enabled && rf_instruction_nonzero instruction]).
Proof.
 intros Observe Legal Reset Instruction Enabled.
 destruct(observed_joint_register_concrete memory inputs k observed 7750%nat 32%nat Observe Legal rf_pipeline_enable_instruction_member)as[word[Size Word]].
 rewrite Instruction in Word. inversion Word;subst word.
 destruct (observed_legal_no_trap_history memory inputs k observed Observe Legal Reset)
 as [committed [initial [history [Run [Prepare [First [Last [Steps NoTrap]]]]]]]].
 destruct (fetch9220_run_type memory inputs k committed Run) as [env [value [Env Rest]]].
 destruct (joint_boundary_reachable memory inputs k committed Run Legal) as [Registers Storage].
 unfold top_environment in Registers. rewrite Env in Registers.
 assert (Boundary : forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)).
 { intros node width Member. rewrite First.
   exact (joint_boundary_prepared_concrete committed env _ initial node width Member (Registers node width Member) Env Prepare). }
 destruct (top_reset_prepared (Some committed) _ initial _ Reset Prepare) as [initial_env [InitialEnv InitialReset]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::false])).
 { rewrite First. unfold top_environment. rewrite InitialEnv. exact InitialReset. }
 pose proof (legal_local_reset_history _ history 9259 false Steps Reset0) as Resets.

 rewrite <-Last. apply(rf_pipeline_gate_fullhistory(generated_observation_input inputs k)nil history instruction enabled Boundary Steps Resets NoTrap Size);rewrite Last;assumption.
Qed.
Theorem rf_isa_gate_observed memory inputs k observed instruction row :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (row<37)%coq_nat ->N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 VM.find 954(top_environment observed)=Some(Gval(Fuint 1)[::rf_isa_writes row && rf_instruction_nonzero instruction]).
Proof.
 intros Observe Legal Reset Instruction Row Match.
 destruct(observed_joint_register_concrete memory inputs k observed 7757%nat 1%nat Observe Legal rf_nonalu_enable_member)as[bits[Size Enabled]].
 destruct bits as[|enabled[|extra rest]];try discriminate Size.
 pose proof(rf_pipeline_gate_observed memory inputs k observed instruction enabled Observe Legal Reset Instruction Enabled)as Gate.
 rewrite(rf_pipeline_isa_write_enable_observed memory inputs k observed instruction enabled row Observe Legal Instruction Enabled Row Match)in Gate. exact Gate.
Qed.
Require Import ReferenceControlStabilityHistory FormalObservedHistory ReferenceValidNormalizedLink NormalizedBit.
Theorem rf_paired_control_observed memory inputs k observed instruction :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 VM.find 1395(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 exists row,(row<37)%coq_nat /\N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row /\
 VM.find 785(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_rd instruction)) /\
 VM.find 3221(top_environment observed)=Some(Gval(Fuint 5)(if rf_isa_writes row then rf_instruction_rd instruction else[::false;false;false;false;false])) /\
 VM.find 954(top_environment observed)=Some(Gval(Fuint 1)[::rf_isa_writes row && rf_instruction_nonzero instruction]).
Proof.
 intros Observe Legal Reset Instruction Active.
 assert(ReferenceActive:VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Source:VM.find 1395(history 9257%nat)=Some(Gval(Fuint 1)[::true])).
 { rewrite(reference_control_stable_1395_history(generated_observation_input inputs k)nil history 9259 reset Resets Steps 9257%nat 9259%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last. exact Active. }
 rewrite <-Last. exact(reference_valid_normalized_after_two _ (history 9257%nat)(history 9258%nat)(history 9259%nat)_(normalized_known _)Source(Steps 9257%nat ltac:(vm_compute;lia))(Steps 9258%nat ltac:(vm_compute;lia))). }
 destruct(rf_scalar_destination_observed memory inputs k observed instruction Observe Legal Reset Instruction ReferenceActive)as[row[Row[Match[Dut Reference]]]].
 exists row. repeat split;try assumption.
 exact(rf_isa_gate_observed memory inputs k observed instruction row Observe Legal Reset Instruction Row Match).
Qed.
