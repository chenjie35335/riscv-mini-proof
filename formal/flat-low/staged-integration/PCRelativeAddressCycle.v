Require Import CoreSocModel ComparisonNodes CycleView MemoryCycleStep ReferenceConditionalBranchImmediate ReferenceBranchImmediate DUTImmediateModes RFALUData RFPipelineEnable ReferenceInstructionDecode LoadExecuteControl DUTRedirectDecode ALUOperandTransfer ALUInputStability ALUOutputTransfer LoadEffectiveAddress ReferenceLoadSemantics FormalObservedHistory FormalLocalHistory ObservedJointRegisterConcrete JointBoundaryRegisters RFReadPorts ReferenceBankObservation.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition pc_relative_class lane :=if Nat.eqb lane 6 then 21%nat else Nat.sub 28 lane.
Definition pc_relative_mode lane :=if Nat.eqb lane 6 then 3%nat else 2%nat.
Definition pc_relative_match (instruction:bits) lane :=N.land(to_N instruction)(reference_instruction_mask(pc_relative_class lane))=reference_instruction_code(pc_relative_class lane).
Definition pc_relative_immediate lane instruction :=dut_imm_result(pc_relative_mode lane)instruction.
Definition pc_relative_control lane which :N :=if Nat.eqb which 2 then if Nat.eqb lane 6 then 4 else 5 else 0.
Lemma pc_relative_bounds lane : (lane<7)%coq_nat ->(pc_relative_class lane<37)%coq_nat /\(pc_relative_mode lane<4)%coq_nat.
Proof. do 7(destruct lane as[|lane];[vm_compute;intuition lia|]);lia. Qed.
Lemma pc_relative_decode_control instruction lane which : (lane<7)%coq_nat ->(which<4)%coq_nat ->pc_relative_match instruction lane ->
 load_execute_decode which(to_N instruction)49=from_N(load_execute_width which)(pc_relative_control lane which).
Proof.
 intros Lane Which Match. pose proof(proj1(pc_relative_bounds lane Lane))as Row.
 cbn[load_execute_decode].
 repeat match goal with |-context[dut_decode_test(to_N instruction)?stage]=>rewrite(rf_dut_decode_wb_choice instruction stage ltac:(vm_compute;lia))(rf_wb_choice_onehot instruction(pc_relative_class lane)(Nat.sub 48 stage)Row ltac:(vm_compute;lia)Match)end.
 do 7(destruct lane as[|lane];[do 4(destruct which as[|which];[reflexivity|]);lia|]);lia.
Qed.
Theorem pc_relative_control_observed memory inputs k observed instruction lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->(lane<7)%coq_nat ->
 VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->size instruction=32%nat ->pc_relative_match instruction lane ->
 VM.find 86(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 88(top_environment observed)=Some(Gval(Fuint 3)(dut_imm_selector(pc_relative_mode lane))) /\
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)[::false;false;false;false]).
Proof.
 intros Observe Legal Lane Front Size Match.
 destruct(observed_history memory inputs k observed Observe Legal)as[reset[history[Last[Steps Resets]]]].
 assert(Control:forall which,(which<4)%coq_nat ->VM.find(load_execute_wire_target which true)(top_environment observed)=Some(Gval(Fuint(load_execute_width which))(from_N(load_execute_width which)(pc_relative_control lane which)))).
 { intros which Which. rewrite <-Last.
 rewrite(load_execute_decode_history (generated_observation_input inputs k)nil history 9259 instruction which Which Steps ltac:(rewrite Last;exact Front)Size 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia))(pc_relative_decode_control instruction lane which Lane Which Match);reflexivity. }
 split;[exact(Control 0%nat ltac:(lia))|]. split;[exact(Control 1%nat ltac:(lia))|]. split;[|exact(Control 3%nat ltac:(lia))].
 pose proof(Control 2%nat ltac:(lia))as Imm. do 7(destruct lane as[|lane];[exact Imm|]);lia.
Qed.
Theorem pc_relative_operand_history invalid history limit start pc immediate :
 size pc=32%nat ->size immediate=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 86(history t)=Some(Gval(Fuint 1)[::false]) /\VM.find 87(history t)=Some(Gval(Fuint 1)[::false]) /\
 VM.find 89(history t)=Some(Gval(Fuint 4)[::false;false;false;false]) /\
 VM.find 7749(history t)=Some(Gval(Fuint 32)pc) /\VM.find 1308(history t)=Some(Gval(Fuint 32)immediate)) ->
 (forall second t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find(alu_operand_yes second)(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)) ->
 forall time,(Nat.add start 3<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1151(history time)=Some(Gval(Fuint 32)pc) /\VM.find 1152(history time)=Some(Gval(Fuint 32)immediate) /\VM.find 1153(history time)=Some(Gval(Fuint 4)[::false;false;false;false]).
Proof.
 intros PcSize ImmSize Steps Inputs Other time Lower Upper. split.
 - eapply(alu_operand_selected_history invalid history limit start false pc PcSize Steps false);[| |exact(Other false)|exact Lower|exact Upper].
 + intros t L U;exact(proj1(Inputs t L U)).
 + intros t L U;exact(proj1(proj2(proj2(proj2(Inputs t L U))))).
 - split.
 + eapply(alu_operand_selected_history invalid history limit start false immediate ImmSize Steps true);[| |exact(Other true)|exact Lower|exact Upper].
 * intros t L U;exact(proj1(proj2(Inputs t L U))).
 * intros t L U;exact(proj2(proj2(proj2(proj2(Inputs t L U))))).
 + destruct time as[|time];[lia|]. exact(load_operand_wire_value 2%nat invalid(history time)(history time)(history(S time))[::false;false;false;false]ltac:(lia)(Logic.eq_refl _)(proj1(proj2(proj2(Inputs time ltac:(lia)ltac:(lia)))))(Steps time ltac:(lia))).
Qed.
Theorem pc_relative_address_commit_observed memory inputs k observed next pc immediate left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 size pc=32%nat ->size immediate=32%nat ->
 VM.find 86(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->VM.find 87(top_environment observed)=Some(Gval(Fuint 1)[::false]) ->
 VM.find 89(top_environment observed)=Some(Gval(Fuint 4)[::false;false;false;false]) ->
 VM.find 7749(top_environment observed)=Some(Gval(Fuint 32)pc) ->VM.find 1308(top_environment observed)=Some(Gval(Fuint 32)immediate) ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(reference_load_address pc immediate)).
Proof.
 intros Observe Legal Next Reset PcSize ImmSize A B Mode Pc Imm Left Right.
 destruct(alu_output_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(Root:forall node value t,List.In node alu_stability_roots ->VM.find(N.of_nat node)(top_environment observed)=Some value ->(128<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find(N.of_nat node)(history t)=Some value).
 { intros node value t Member Value Lower Upper.
 rewrite(proj2(alu_stability_roots_history (generated_observation_input inputs k)nil history 9259 Boundary Steps node Member t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia)))Last;exact Value. }
 assert(Inputs:forall t,(128<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 86(history t)=Some(Gval(Fuint 1)[::false]) /\VM.find 87(history t)=Some(Gval(Fuint 1)[::false]) /\VM.find 89(history t)=Some(Gval(Fuint 4)[::false;false;false;false]) /\VM.find 7749(history t)=Some(Gval(Fuint 32)pc) /\VM.find 1308(history t)=Some(Gval(Fuint 32)immediate)).
 { intros t Lower Upper. split;[exact(Root 86%nat _ t ltac:(left;reflexivity)A Lower Upper)|].
 split;[exact(Root 87%nat _ t ltac:(right;left;reflexivity)B Lower Upper)|].
 split;[exact(Root 89%nat _ t ltac:(right;right;right;left;reflexivity)Mode Lower Upper)|].
 split;[exact(Root 7749%nat _ t ltac:(right;right;right;right;right;left;reflexivity)Pc Lower Upper)|].
 exact(alu_stable_value_at (generated_observation_input inputs k)nil history 1308 _ t Boundary Steps ltac:(right;right;right;right;right;left;reflexivity)Lower Upper ltac:(rewrite Last;exact Imm)). }
 assert(Other:forall second t,(128<=t)%coq_nat ->(t<=9259)%coq_nat ->exists value,VM.find(alu_operand_yes second)(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)).
 { intros second t Lower Upper;destruct second.
 - exists(Gval(Fuint 32)right);split;[exact(Root 7819%nat _ t ltac:(right;right;right;right;right;right;right;left;reflexivity)Right Lower Upper)|reflexivity].
 - exists(Gval(Fuint 32)left);split;[exact(Root 7816%nat _ t ltac:(right;right;right;right;right;right;left;reflexivity)Left Lower Upper)|reflexivity]. }
 pose proof(pc_relative_operand_history _ history 9259 128 pc immediate PcSize ImmSize Steps Inputs Other)as Values.
 apply(Transfer pc immediate ImmSize).
 - exact(proj1(proj2(Values 9250%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj2(proj2(Values 9251%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(proj2(Values 9252%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
 - exact(proj1(Values 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia))).
 - exact(proj2(proj2(Values 9253%nat ltac:(vm_compute;lia)ltac:(vm_compute;lia)))).
Qed.
Theorem cycle_pc_relative_address_step lane memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (lane<7)%coq_nat ->pc_relative_match(cv_front_instruction before)lane ->
 cv_commit_instruction after=cv_front_instruction before /\
 cv_pending_alu after=reference_load_address(cv_front_pc before)(pc_relative_immediate lane(cv_front_instruction before)).
Proof.
 intros Transition Reset Before After Lane Match. split;[exact(cycle_front_to_commit memory inputs k current next before after Transition Reset Before After)|].
 destruct Transition as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 destruct(observed_joint_register_concrete memory inputs k current 7748%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 53%nat);vm_compute;reflexivity))as[instruction[InstSize Inst]].
 rewrite(cva_front_instruction _ _ Before)in Inst;inversion Inst;subst instruction.
 destruct(observed_joint_register_concrete memory inputs k current 7749%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity))as[pc[PcSize Pc]].
 rewrite(cva_front_pc _ _ Before)in Pc;inversion Pc;subst pc.
 destruct(pc_relative_control_observed memory inputs k current(cv_front_instruction before)lane Observe Legal Lane(cva_front_instruction _ _ Before)InstSize Match)as[A[B[ImmControl Mode]]].
 pose proof(dut_imm_observed(pc_relative_mode lane)memory inputs k current(cv_front_instruction before)(proj2(pc_relative_bounds lane Lane))Observe Legal(cva_front_instruction _ _ Before)InstSize ImmControl)as Imm.
 pose proof(pc_relative_address_commit_observed memory inputs k current committed(cv_front_pc before)(pc_relative_immediate lane(cv_front_instruction before))(cv_left before)(cv_right before)
 Observe Legal Run Reset PcSize(dut_imm_result_size(pc_relative_mode lane)(cv_front_instruction before)(proj2(pc_relative_bounds lane Lane))InstSize)A B Mode(cva_front_pc _ _ Before)Imm(cva_left _ _ Before)(cva_right _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 rf_read_alu_member Run NextObserve)as Copy.
 rewrite(cva_pending_alu _ _ After)Value in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Require Import ReferenceIllegalObserved LoadPipelineClassification ObservedCommitPCTransfer FormalInstructionResetConstants.
Lemma pc_relative_match_not_nop lane : (lane<7)%coq_nat ->~pc_relative_match FormalInstructionResetConstants.instruction_nop lane.
Proof. do 7(destruct lane as[|lane];[vm_compute;discriminate|]);lia. Qed.
Theorem pc_relative_reference_immediate_observed lane memory inputs k observed instruction :
 (lane<7)%coq_nat ->generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->pc_relative_match instruction lane ->
 VM.find 2552(top_environment observed)=Some(Gval(Fuint 32)(pc_relative_immediate lane instruction)).
Proof.
 intros Lane Observe Legal Reset Instruction Match.
 destruct lane as[|lane];[exact(reference_branch_immediate_observed 0 memory inputs k observed instruction ltac:(lia) Observe Legal Reset Instruction Match)|].
 destruct lane as[|lane];[exact(reference_branch_immediate_observed 1 memory inputs k observed instruction ltac:(lia) Observe Legal Reset Instruction Match)|].
 destruct lane as[|lane];[exact(reference_branch_immediate_observed 2 memory inputs k observed instruction ltac:(lia) Observe Legal Reset Instruction Match)|].
 destruct lane as[|lane];[exact(reference_branch_immediate_observed 3 memory inputs k observed instruction ltac:(lia) Observe Legal Reset Instruction Match)|].
 destruct lane as[|lane];[exact(reference_branch_immediate_observed 4 memory inputs k observed instruction ltac:(lia) Observe Legal Reset Instruction Match)|].
 destruct lane as[|lane];[exact(reference_branch_immediate_observed 5 memory inputs k observed instruction ltac:(lia) Observe Legal Reset Instruction Match)|].
 destruct lane as[|lane];[exact(reference_jal_immediate_observed memory inputs k observed instruction Observe Legal Reset Instruction Match)|lia].
Qed.
Theorem cycle_pc_front_to_commit memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 cv_commit_pc after=cv_front_pc before.
Proof.
 intros[Observe[Legal[NextObserve[NextLegal[committed Run]]]]]Reset Before After.
 destruct(observed_joint_register_concrete memory inputs k current 7749%nat 32%nat Observe Legal ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity))as[pc[Size Word]].
 rewrite(cva_front_pc _ _ Before)in Word;inversion Word;subst pc.
 pose proof(observed_commit_pc_transfer memory inputs k current committed(cv_front_pc before)Observe Legal Run Reset Size(cva_front_pc _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7751 32 ltac:(apply(List.nth_error_In joint_boundary_registers 56%nat);vm_compute;reflexivity)Run NextObserve)as Copy.
 rewrite(cva_commit_pc _ _ After)Value in Copy;exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
Theorem cycle_pc_relative_pending_step lane memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (lane<7)%coq_nat ->pc_relative_match(cv_front_instruction before)lane ->cycle_pc_aligned after ->
 cv_late_bubble after=false /\
 cv_pending_alu after=reference_load_address(cv_reference_pc after)(pc_relative_immediate lane(cv_commit_instruction after)).
Proof.
 intros Transition Reset Before After Lane Match [Aligned Phase].
 destruct(cycle_pc_relative_address_step lane memory inputs k current next before after Transition Reset Before After Lane Match)as[Instruction Value].
 pose proof(cycle_pc_front_to_commit memory inputs k current next before after Transition Reset Before After)as Pc.
 destruct Transition as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 assert(Late:cv_late_bubble after=false).
 { destruct(load_pipeline_late_observed memory inputs(S k)next NextObserve NextLegal)as[bit[Late Nop]].
 rewrite(cva_late_bubble _ _ After)in Late.
 assert(Equal:cv_late_bubble after=bit)by(exact(f_equal(fun value=>match value with Some(Gval _ (b::_))=>b|_=>false end)Late)).
 rewrite Equal. destruct bit;[|reflexivity]. specialize(Nop(Logic.eq_refl _)). rewrite(cva_commit_instruction _ _ After)in Nop.
 pose proof(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Nop)as NopWord.
 change(cv_commit_instruction after=FormalInstructionResetConstants.instruction_nop)in NopWord.
 rewrite -Instruction NopWord in Match. exfalso;exact(pc_relative_match_not_nop lane Lane Match). }
 split;[exact Late|]. destruct Phase as[[Other Equal]|[[Other Rest]|[Other Rest]]];congruence.
Qed.
Require Import ReferenceRedirectSemantics ReferenceRedirectSpine DUTRedirectReachability.
Lemma pc_relative_immediate_low_zero lane instruction :
 N.testbit(to_N(pc_relative_immediate lane instruction))0=false.
Proof.
 unfold pc_relative_immediate,pc_relative_mode. destruct(Nat.eqb lane 6);
 rewrite (redirect_to_N_testbit _ 0%nat);reflexivity.
Qed.
Lemma pc_relative_address_low_zero pc immediate :
 N.testbit(to_N pc)0=false ->N.testbit(to_N immediate)0=false ->
 N.testbit(to_N(reference_load_address pc immediate))0=false.
Proof.
 intros Pc Imm. rewrite (redirect_to_N_testbit _ 0%nat).
 change(N.odd(to_N pc+to_N immediate)=false).
 rewrite N.odd_add -!N.bit0_odd Pc Imm;reflexivity.
Qed.
Lemma pc_relative_aligned_low_zero pc :take 2 pc=[::false;false] ->N.testbit(to_N pc)0=false.
Proof.
 intro Aligned. rewrite (redirect_to_N_testbit _ 0%nat). destruct pc as[|b[|c pc]];try reflexivity;inversion Aligned;reflexivity.
Qed.
Theorem cycle_pc_relative_taken_target_aligned lane memory inputs k current next before after :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->cycle_reset inputs(S k)false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (lane<7)%coq_nat ->pc_relative_match(cv_front_instruction before)lane ->cycle_pc_aligned after ->
 cv_delayed_redirect after=true ->
 reference_redirect_aligned false(to_N(reference_load_address(cv_reference_pc after)(pc_relative_immediate lane(cv_commit_instruction after))))=true.
Proof.
 intros Transition Reset NextReset Before After Lane Match Aligned Taken.
 destruct(cycle_pc_relative_pending_step lane memory inputs k current next before after Transition Reset Before After Lane Match Aligned)as[Late Target].
 assert(Low0:N.testbit(to_N(cv_pending_alu after))0=false).
 { rewrite Target. apply pc_relative_address_low_zero;[apply pc_relative_aligned_low_zero;exact(proj1 Aligned)|apply pc_relative_immediate_low_zero]. }
 destruct Transition as[Observe[Legal[NextObserve[NextLegal[committed Run]]]]].
 pose proof(dut_no_trap_target_bit_observed memory inputs(S k)next(cv_pending_alu after)NextObserve NextLegal NextReset ltac:(rewrite(cva_delayed_redirect _ _ After)Taken;reflexivity)(cva_pending_alu _ _ After)(cva_pending_width _ _ After))as Low1.
 rewrite -Target reference_redirect_aligned_bits Low0 Low1;reflexivity.
Qed.
Theorem cycle_pc_relative_taken_sum_aligned lane memory inputs k current next before after compressed :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->cycle_reset inputs(S k)false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->
 (lane<7)%coq_nat ->pc_relative_match(cv_front_instruction before)lane ->cycle_pc_aligned after ->
 cv_delayed_redirect after=true ->
 reference_redirect_aligned compressed(to_N(cv_reference_pc after)+to_N(pc_relative_immediate lane(cv_commit_instruction after)))=true.
Proof.
 intros Transition Reset NextReset Before After Lane Match Aligned Taken.
 pose proof(cycle_pc_relative_taken_target_aligned lane memory inputs k current next before after Transition Reset NextReset Before After Lane Match Aligned Taken)as Result.
 unfold reference_load_address in Result;rewrite reference_redirect_aligned_take32_from33 in Result.
 rewrite reference_redirect_aligned_bits in Result. rewrite reference_redirect_aligned_bits.
 destruct(N.testbit(to_N(cv_reference_pc after)+to_N(pc_relative_immediate lane(cv_commit_instruction after)))0);
 destruct(N.testbit(to_N(cv_reference_pc after)+to_N(pc_relative_immediate lane(cv_commit_instruction after)))1);destruct compressed;cbn in *;congruence.
Qed.
