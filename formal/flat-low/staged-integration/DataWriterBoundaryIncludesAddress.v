Require Import DataAddressBoundaryRegisters DataWriterBoundaryRegisters.
From Coq Require Import List Arith Bool.
Lemma data_writer_includes_address_check :
 forallb (fun entry => existsb (fun candidate =>
   Nat.eqb (fst entry) (fst candidate) && Nat.eqb (snd entry) (snd candidate))
   data_writer_boundary_registers) data_address_boundary_registers = true.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_includes_address node width :
 In (node,width) data_address_boundary_registers -> In (node,width) data_writer_boundary_registers.
Proof.
 intro Member. pose proof data_writer_includes_address_check as Check.
 rewrite forallb_forall in Check. specialize (Check (node,width) Member).
 apply existsb_exists in Check. destruct Check as [[other size] [Inside Equal]].
 apply andb_true_iff in Equal. destruct Equal as [Node Width].
 cbn in Node, Width. apply Nat.eqb_eq in Node. apply Nat.eqb_eq in Width.
 subst other size. exact Inside.
Qed.
Print Assumptions data_writer_includes_address.
