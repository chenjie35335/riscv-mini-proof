Require Import DataWriterDependencyRanks.
From Coq Require Import List Arith Bool.
Import ListNotations.
Definition data_writer_boundary_ids : list nat := [1;851;852;853;854;855;856;857;858;859;860;861;862;863;864;865;866;867;868;869;870;871;872;873;874;875;876;877;878;879;880;881;882;7748;7749;7750;7752;7754;7756;7757].
Lemma data_writer_boundary_check :
 forallb (fun entry => if Nat.eqb (fst (snd entry)) 0 then
 existsb (Nat.eqb (fst entry)) data_writer_boundary_ids else true) data_writer_dependency_ranks = true.
Proof. vm_compute. reflexivity. Qed.
Theorem data_writer_zero_rank_is_boundary node dependencies :
 In (node, (0, dependencies)) data_writer_dependency_ranks -> In node data_writer_boundary_ids.
Proof.
 intro Member. pose proof data_writer_boundary_check as Checked.
 rewrite forallb_forall in Checked.
 specialize (Checked (node, (0, dependencies)) Member). cbn in Checked.
 change (existsb (Nat.eqb node) data_writer_boundary_ids = true) in Checked.
 apply existsb_exists in Checked.
 destruct Checked as [id [Inside Equal]]. apply Nat.eqb_eq in Equal. subst id. exact Inside.
Qed.
Print Assumptions data_writer_zero_rank_is_boundary.
