Require Import RFShiftALUHistory RFShiftOutput RFShiftImmediateOperands RFRegisterOperands RFInstructionControl RFALUData RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ControlWritebackKill ReferenceInstructionDecode CoreSocModel ComparisonNodes JointBoundaryRegisters JointUpdateBoundaryHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ConcreteRegisterInitialization ALUOperandTransfer LoadEffectiveAddress LoadImmediateSemantics RFReadPorts ReferenceLoadSemantics FormalLocalHistory ALUInputStability ALUOutputTransfer ObservedJointRegisterConcrete EarlyControlStabilityHistory CycleView ReferenceBankObservation.
Definition rf_shift_class immediate lane :=if immediate then Nat.add 6 lane else nth 0%nat[::17%nat;18%nat;20%nat]lane.
Definition rf_shift_right immediate instruction right:=if immediate then load_i_immediate instruction else right.
Definition rf_shift_result immediate lane instruction left right:=rf_shift_word (negb(Nat.eqb lane 0))(Nat.eqb lane 2)left(rf_shift_right immediate instruction right).
Lemma rf_shift_control immediate lane :(lane<3)%coq_nat ->from_N 4(rf_isa_execute_control(rf_shift_class immediate lane)3)=rf_shift_mode(negb(Nat.eqb lane 0))(Nat.eqb lane 2).
Proof. intro Lane. destruct immediate;do 3(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Lemma rf_shift_class_bound immediate lane :(lane<3)%coq_nat ->(rf_shift_class immediate lane<37)%coq_nat.
Proof. intro Lane. destruct immediate;do 3(destruct lane as[|lane];[vm_compute;lia|]);lia. Qed.
Lemma rf_shift_result_size immediate lane instruction left right :size left=32%nat ->size(rf_shift_result immediate lane instruction left right)=32%nat.
Proof. apply rf_shift_word_size. Qed.
Theorem rf_shift_observed_commit memory inputs k observed next instruction immediate lane left right :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 generated_run memory inputs(S k)=Some next ->
 VM.find 1(formal_external_inputs(generated_observation_input inputs k))=Some(Gval(Fuint 1)[::false]) ->
 (lane<3)%coq_nat ->VM.find 7748(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 size left=32%nat ->size right=32%nat ->
 VM.find 7816(top_environment observed)=Some(Gval(Fuint 32)left) ->VM.find 7819(top_environment observed)=Some(Gval(Fuint 32)right) ->
 VM.find 7752(top_environment next)=Some(Gval(Fuint 32)(rf_shift_result immediate lane instruction left right)).
Proof.
 intros Observe Legal Next Reset Lane Instruction Match LeftSize RightSize Left Right.
 destruct(observed_joint_register_concrete memory inputs k observed 7748%nat 32%nat Observe Legal load_imm_front_member)as[word[Size Word]]. rewrite Instruction in Word;inversion Word;subst word.
 destruct(rf_alu_observed_transfer_context memory inputs k observed next Observe Legal Next Reset)as[history[Last[Boundary[Steps[Resets Transfer]]]]].
 assert(L:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)).
 { intros t Lower Upper. rewrite(early_control_stable_7816_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Left. }
 assert(R:forall t,(55<=t)%coq_nat ->(t<=9259)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)).
 { intros t Lower Upper. rewrite(early_control_stable_7819_history (generated_observation_input inputs k)nil history 9259 Boundary Steps t 9259 ltac:(lia)ltac:(vm_compute;lia)Upper ltac:(vm_compute;lia))Last;exact Right. }
 assert(Inputs:forall t,(100<=t)%coq_nat ->(t<=9259)%coq_nat ->
 VM.find 1151(history t)=Some(Gval(Fuint 32)left) /\VM.find 1152(history t)=Some(Gval(Fuint 32)(rf_shift_right immediate instruction right)) /\
 VM.find 1153(history t)=Some(Gval(Fuint 4)(from_N 4(rf_isa_execute_control(rf_shift_class immediate lane)3)))).
 { destruct immediate.
 - exact(rf_shift_immediate_operand_history (generated_observation_input inputs k)nil history 9259 instruction(rf_shift_class true lane)left right ltac:(unfold rf_shift_class;lia)Size LeftSize RightSize Match Boundary Steps ltac:(rewrite Last;exact Instruction)L R).
 - exact(rf_register_operand_history (generated_observation_input inputs k)nil history 9259 instruction(rf_shift_class false lane)left right ltac:(do 3(destruct lane as[|lane];[vm_compute;lia|]);lia)ltac:(do 3(destruct lane as[|lane];[vm_compute;lia|]);lia)Size LeftSize RightSize Match Boundary Steps ltac:(rewrite Last;exact Instruction)L R). }
 apply(Transfer _ (rf_shift_result_size immediate lane instruction left right LeftSize)).
 pose proof(rf_shift_alu_history (formal_invalid_policy(generated_observation_input inputs k)nil)(fun i=>history(Nat.add 100 i))9159(negb(Nat.eqb lane 0))(Nat.eqb lane 2)left(rf_shift_right immediate instruction right)LeftSize ltac:(vm_compute;lia))as H.
 assert(Bound:forall i,(i<=9159)%coq_nat ->(100<=Nat.add 100 i)%coq_nat /\(Nat.add 100 i<=9259)%coq_nat)by(intros i U;split;[apply Nat.le_add_r|change(Nat.add 100 i<=Nat.add 100 9159)%coq_nat;apply Nat.add_le_mono_l;exact U]).
 assert(M:forall i,(i<=9159)%coq_nat ->VM.find 1153(history(Nat.add 100 i))=Some(Gval(Fuint 4)(rf_shift_mode(negb(Nat.eqb lane 0))(Nat.eqb lane 2)))).
 { intros i U. rewrite<-(rf_shift_control immediate lane Lane). exact(proj2(proj2(Inputs _ (proj1(Bound i U))(proj2(Bound i U))))). }
 assert(S:forall i,(i<9159)%coq_nat ->formal_value_iter(formal_invalid_policy(generated_observation_input inputs k)nil)flat_memories(history(Nat.add 100 i))false(history(Nat.add 100 i))flat_statements=Some(history(Nat.add 100(S i)))).
 { intros i U. replace(Nat.add 100(S i))with(S(Nat.add 100 i))by lia. apply Steps. change(Nat.add 100 i<Nat.add 100 9159)%coq_nat. apply Nat.add_lt_mono_l;exact U. }
 exact(H M(fun i U=>proj1(Inputs _ (proj1(Bound i U))(proj2(Bound i U))))(fun i U=>proj1(proj2(Inputs _ (proj1(Bound i U))(proj2(Bound i U)))))S 9157 ltac:(vm_compute;lia)ltac:(vm_compute;lia)).
Qed.
Theorem cycle_shift_step memory inputs k current next before after immediate lane :
 cycle_transition memory inputs k current next ->cycle_reset inputs k false ->
 cycle_view_at(top_environment current)before ->cycle_view_at(top_environment next)after ->(lane<3)%coq_nat ->
 N.land(to_N(cv_front_instruction before))(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 cv_pending_alu after=rf_shift_result immediate lane(cv_front_instruction before)(cv_left before)(cv_right before).
Proof.
 intros [Observe[Legal[NextObserve[NextLegal[committed Run]]]]] Reset Before After Lane Match.
 pose proof(rf_shift_observed_commit memory inputs k current committed(cv_front_instruction before)immediate lane(cv_left before)(cv_right before)Observe Legal Run Reset Lane(cva_front_instruction _ _ Before)Match(cva_left_width _ _ Before)(cva_right_width _ _ Before)(cva_left _ _ Before)(cva_right _ _ Before))as Value.
 pose proof(joint_register_run_observed memory inputs(S k)committed next 7752 32 rf_read_alu_member Run NextObserve)as Copy.
 rewrite Value(cva_pending_alu _ _ After)in Copy.
 exact(f_equal(fun value=>match value with Some(Gval _ word)=>word|_=>[::]end)Copy).
Qed.
