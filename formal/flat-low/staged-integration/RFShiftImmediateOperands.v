Require Import DUTRedirectSemantics RFSubtractArithmetic RFInstructionControl RFALUData RFPipelineEnable RFScalarControl LoadExecuteControl DUTRedirectDecode ControlWritebackKill ReferenceInstructionDecode CoreSocModel ComparisonNodes JointBoundaryRegisters JointUpdateBoundaryHistory.
From Coq Require Import NArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Require Import ConcreteRegisterInitialization ALUOperandTransfer LoadEffectiveAddress LoadImmediateSemantics RFReadPorts.
Lemma rf_shift_immediate_controls (row:nat) :((6<=row)%coq_nat /\ (row<9)%coq_nat) ->
 rf_isa_execute_control row 0=1 /\rf_isa_execute_control row 1=0 /\rf_isa_execute_control row 2=1.
Proof. intro Bound. do 6(destruct row as[|row];[lia|]). do 3(destruct row as[|row];[split;[reflexivity|split;reflexivity]|]);lia. Qed.
Theorem rf_shift_immediate_operand_history inputs path history limit instruction row left right :
 ((6<=row)%coq_nat /\ (row<9)%coq_nat) ->
 size instruction=32%nat ->size left=32%nat ->size right=32%nat ->
 N.land(to_N instruction)(reference_instruction_mask row)=reference_instruction_code row ->
 (forall node width,List.In(node,width)joint_boundary_registers ->map_uint_concrete(N.of_nat node)width(history 0%nat)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 VM.find 7748(history limit)=Some(Gval(Fuint 32)instruction) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7816(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(55<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7819(history t)=Some(Gval(Fuint 32)right)) ->
 forall time,(100<=time)%coq_nat ->(time<=limit)%coq_nat ->
 VM.find 1151(history time)=Some(Gval(Fuint 32)left) /\
 VM.find 1152(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction)) /\
 VM.find 1153(history time)=Some(Gval(Fuint 4)(from_N 4(rf_isa_execute_control row 3))).
Proof.
 intros Row Size LeftSize RightSize Match Boundary Steps Front Left Right.
 pose proof(rf_isa_execute_control_history inputs path history limit instruction row)as Control.
 assert(Imm:forall t,(68<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1308(history t)=Some(Gval(Fuint 32)(load_i_immediate instruction))).
 { intros t Lower Upper. eapply(load_imm_front_register_history _ history limit 55 instruction Size);[| |exact Steps|exact Lower|exact Upper].
 - pose proof(joint_update_register_history_same _ history limit 7748 32 load_imm_front_member Steps limit (Nat.le_refl _))as Hold. change(VM.find 7748(history limit)=VM.find 7748(history 0%nat))in Hold. rewrite<-Hold;exact Front.
 - intros u L U. pose proof(Control 2%nat ltac:(lia)ltac:(lia)Size Match Steps Front u L U)as C. rewrite(proj2(proj2(rf_shift_immediate_controls row Row)))in C. exact C. }
 assert(A:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1151(history time)=Some(Gval(Fuint 32)left)).
 { apply(alu_operand_selected_history _ history limit 68 true left LeftSize Steps false).
 - intros t L U. pose proof(Control 0%nat ltac:(lia) ltac:(lia)Size Match Steps Front t ltac:(lia)U)as C. rewrite(proj1(rf_shift_immediate_controls row Row))in C. exact C.
 - intros t L U. apply Left;lia.
 - intros t L U. destruct(joint_update_register_history_concrete _ history limit 7749 32 ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity) (Boundary 7749%nat 32%nat ltac:(apply(List.nth_error_In joint_boundary_registers 54%nat);vm_compute;reflexivity)) Steps t U)as[word[W V]]. exists(Gval(Fuint 32)word);split;[exact V|reflexivity]. }
 assert(B:forall time,(71<=time)%coq_nat ->(time<=limit)%coq_nat ->VM.find 1152(history time)=Some(Gval(Fuint 32)(load_i_immediate instruction))).
 { apply(alu_operand_selected_history _ history limit 68 false (load_i_immediate instruction)(load_i_immediate_size instruction Size) Steps true).
 - intros t L U. pose proof(Control 1%nat ltac:(lia)ltac:(lia)Size Match Steps Front t ltac:(lia)U)as C. rewrite(proj1(proj2(rf_shift_immediate_controls row Row)))in C. exact C.
 - intros t L U. apply Imm;assumption.
 - intros t L U. exists(Gval(Fuint 32)right);split;[apply Right;lia|reflexivity]. }
 intros [|time] Lower Upper;try lia. split;[apply A;lia|]. split;[apply B;lia|].
 exact(load_operand_wire_value 2%nat _ (history time)(history time)(history(S time))(from_N 4(rf_isa_execute_control row 3))ltac:(lia)(size_from_N _ _)(Control 3%nat ltac:(lia) ltac:(lia)Size Match Steps Front time ltac:(lia)ltac:(lia))(Steps time ltac:(lia))).
Qed.

