Require Import JointBoundaryRegisters DataWriterBoundaryRegisters X0BoundaryRegisters.
From Coq Require Import List Arith Bool.
Lemma joint_includes_writer_check :
 forallb (fun entry => existsb (fun candidate =>
   Nat.eqb (fst entry) (fst candidate) && Nat.eqb (snd entry) (snd candidate))
   joint_boundary_registers) data_writer_boundary_registers = true.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_includes_writer node width :
 In (node,width) data_writer_boundary_registers -> In (node,width) joint_boundary_registers.
Proof.
 intro Member. pose proof joint_includes_writer_check as Check.
 rewrite forallb_forall in Check. specialize (Check (node,width) Member).
 apply existsb_exists in Check. destruct Check as [[other size] [Inside Equal]].
 apply andb_true_iff in Equal. destruct Equal as [Node Width].
 cbn in Node, Width. apply Nat.eqb_eq in Node. apply Nat.eqb_eq in Width.
 subst other size. exact Inside.
Qed.
Print Assumptions joint_includes_writer.
Lemma joint_includes_x0_check :
 forallb (fun entry => existsb (fun candidate =>
   Nat.eqb (fst entry) (fst candidate) && Nat.eqb (snd entry) (snd candidate))
   joint_boundary_registers) x0_boundary_registers = true.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_includes_x0 node width :
 In (node,width) x0_boundary_registers -> In (node,width) joint_boundary_registers.
Proof.
 intro Member. pose proof joint_includes_x0_check as Check.
 rewrite forallb_forall in Check. specialize (Check (node,width) Member).
 apply existsb_exists in Check. destruct Check as [[other size] [Inside Equal]].
 apply andb_true_iff in Equal. destruct Equal as [Node Width].
 cbn in Node, Width. apply Nat.eqb_eq in Node. apply Nat.eqb_eq in Width.
 subst other size. exact Inside.
Qed.
Print Assumptions joint_includes_x0.
