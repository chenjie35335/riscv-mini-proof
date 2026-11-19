Require Import CoreSocModel ComparisonNodes RegisterInvariants UIntRegisterCertificate ConcreteRegisterInitialization StagedRegisterHold.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Definition data_address_boundary_registers : list (nat * nat) :=
 [:: (851,32);(852,32);(853,32);(854,32);(855,32);(856,32);(857,32);(858,32);(859,32);(860,32);(861,32);(862,32);(863,32);(864,32);(865,32);(866,32);(867,32);(868,32);(869,32);(870,32);(871,32);(872,32);(873,32);(874,32);(875,32);(876,32);(877,32);(878,32);(879,32);(880,32);(881,32);(882,32);(7748,32);(7749,32);(7750,32);(7752,32);(7756,2);(7757,1)].
Lemma data_address_boundary_register_check :
 List.forallb (fun entry =>
 uint_register_declarations_b (N.of_nat (fst entry)) (snd entry) flat_statements &&
 has_register (N.of_nat (fst entry)) flat_statements) data_address_boundary_registers = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma data_address_boundary_register_properties node width :
 List.In (node,width) data_address_boundary_registers ->
 uint_register_declarations (N.of_nat node) width flat_statements /\
 has_register (N.of_nat node) flat_statements = true.
Proof.
 intro Member. pose proof data_address_boundary_register_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
 cbn [fst snd] in Check. move/andP: Check => [Declarations Present].
 split; [apply uint_register_declarations_b_sound; exact Declarations|exact Present].
Qed.
Theorem data_address_boundary_registers_symbolic inputs path state node width :
 List.In (node,width) data_address_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (initialize_symbolic_registers inputs path flat_statements state).
Proof.
 intro Member. destruct (data_address_boundary_register_properties node width Member) as [Declarations Present].
 apply initialize_establishes_uint_concrete; assumption.
Qed.
Theorem data_address_boundary_registers_comb_hold invalid old current result node width :
 List.In (node,width) data_address_boundary_registers ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (N.of_nat node) result = VM.find (N.of_nat node) old.
Proof.
 intros Member Step. destruct (data_address_boundary_register_properties node width Member) as [_ Present].
 exact (staged_combinational_holds_registers invalid flat_memories old current result flat_statements (N.of_nat node) Present Step).
Qed.
Print Assumptions data_address_boundary_registers_symbolic.
Print Assumptions data_address_boundary_registers_comb_hold.
