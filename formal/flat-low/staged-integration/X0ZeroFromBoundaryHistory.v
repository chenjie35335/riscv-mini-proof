Require Import CoreSocModel ComparisonNodes FlatRegFileX0 X0ConcreteGraphPropagation X0BoundaryHistory X0BoundaryRegisters ConcreteRegisterInitialization FormalConcreteX0Enable FormalX0InstructionPath.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem x0_zero_from_boundary_history inputs path history limit :
 (forall node width, List.In (node,width) x0_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall time, (time <= limit)%coq_nat -> exists bit,
 VM.find (N.of_nat 1) (history time) = Some (Gval (Fuint 1) [::bit])) ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (Nat.le 51 time /\ Nat.le time limit) -> VM.find (N.of_nat 1399) (history time) = Some rf_zero32.
Proof.
 intros Initial Reset Steps time Bounds.
 set (start := Nat.sub time 10).
 assert (End : (start + 10)%coq_nat = time) by (unfold start; lia).
 assert (TenSteps : forall j, (j < 10)%coq_nat ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history (start+j)%coq_nat) false (history (start+j)%coq_nat) flat_statements = Some (history (start+S j)%coq_nat)).
 { intros j Small. replace (start + S j)%coq_nat with (S (Nat.add start j)) by lia.
   apply Steps. lia. }
 assert (Boundary := x0_rank_zero_history_concrete (formal_invalid_policy inputs path) history limit Initial Reset Steps).
 destruct (x0_concrete_history_targets inputs path history limit Boundary Steps (start+3)%coq_nat ltac:(lia) ltac:(lia)) as [Enable _].
 destruct (concrete_x0_enable_is_bit (formal_invalid_policy inputs path)
 (history (start+2)%coq_nat) (history (start+2)%coq_nat) (history (start+3)%coq_nat)
 (TenSteps 2%nat ltac:(lia)) Enable) as [bit EnableBit].
 assert (Member : List.In (7750%nat,32%nat) x0_boundary_registers).
 { unfold x0_boundary_registers. right. left. reflexivity. }
 destruct (x0_register_history_concrete (formal_invalid_policy inputs path) history limit 7750%nat 32%nat Member
 (Initial 7750%nat 32%nat Member) Steps (start+0)%coq_nat ltac:(lia)) as [instruction [Size Instruction]].
 rewrite <- End.
 exact (x0_output_from_instruction (formal_invalid_policy inputs path)
 (history (start+0)%coq_nat) (history (start+1)%coq_nat) (history (start+2)%coq_nat)
 (history (start+3)%coq_nat) (history (start+4)%coq_nat) (history (start+5)%coq_nat)
 (history (start+6)%coq_nat) (history (start+7)%coq_nat) (history (start+8)%coq_nat)
 (history (start+9)%coq_nat) (history (start+10)%coq_nat) instruction bit Size Instruction EnableBit
 (TenSteps 0%nat ltac:(lia)) (TenSteps 1%nat ltac:(lia)) (TenSteps 2%nat ltac:(lia))
 (TenSteps 3%nat ltac:(lia)) (TenSteps 4%nat ltac:(lia)) (TenSteps 5%nat ltac:(lia))
 (TenSteps 6%nat ltac:(lia)) (TenSteps 7%nat ltac:(lia)) (TenSteps 8%nat ltac:(lia))
 (TenSteps 9%nat ltac:(lia))).
Qed.
Print Assumptions x0_zero_from_boundary_history.
