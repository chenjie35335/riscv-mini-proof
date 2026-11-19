Require Import CoreSocModel ComparisonNodes RegisterInvariants UIntRegisterCertificate ConcreteRegisterInitialization StagedRegisterHold.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Definition x0_boundary_registers : list (nat * nat) :=
 [:: (150,2);(7750,32);(7752,32);(7754,2);(7755,3);(7757,1);(7758,3);(7759,1);(7760,1)].
Lemma x0_boundary_register_check :
 List.forallb (fun entry =>
 uint_register_declarations_b (N.of_nat (fst entry)) (snd entry) flat_statements &&
 has_register (N.of_nat (fst entry)) flat_statements) x0_boundary_registers = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma x0_boundary_register_properties node width :
 List.In (node,width) x0_boundary_registers ->
 uint_register_declarations (N.of_nat node) width flat_statements /\
 has_register (N.of_nat node) flat_statements = true.
Proof.
 intro Member. pose proof x0_boundary_register_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check (node,width) Member).
 cbn [fst snd] in Check. move/andP: Check => [Declarations Present].
 split; [apply uint_register_declarations_b_sound; exact Declarations|exact Present].
Qed.
Theorem x0_boundary_registers_symbolic inputs path state node width :
 List.In (node,width) x0_boundary_registers ->
 map_uint_concrete (N.of_nat node) width (initialize_symbolic_registers inputs path flat_statements state).
Proof.
 intro Member. destruct (x0_boundary_register_properties node width Member) as [Declarations Present].
 apply initialize_establishes_uint_concrete; assumption.
Qed.
Theorem x0_boundary_registers_comb_hold invalid old current result node width :
 List.In (node,width) x0_boundary_registers ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find (N.of_nat node) result = VM.find (N.of_nat node) old.
Proof.
 intros Member Step. destruct (x0_boundary_register_properties node width Member) as [_ Present].
 exact (staged_combinational_holds_registers invalid flat_memories old current result flat_statements (N.of_nat node) Present Step).
Qed.
Print Assumptions x0_boundary_registers_symbolic.
Print Assumptions x0_boundary_registers_comb_hold.
