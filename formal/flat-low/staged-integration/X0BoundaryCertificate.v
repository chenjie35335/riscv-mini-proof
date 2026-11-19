Require Import X0DependencyRanks.
From Coq Require Import List Arith Bool.
Import ListNotations.
Definition x0_boundary_ids : list nat := [1;150;7750;7752;7754;7755;7757;7758;7759;7760].
Lemma x0_boundary_check :
 forallb (fun entry => if Nat.eqb (fst (snd entry)) 0 then
 existsb (Nat.eqb (fst entry)) x0_boundary_ids else true) x0_dependency_ranks = true.
Proof. vm_compute. reflexivity. Qed.
Theorem x0_zero_rank_is_boundary node dependencies :
 In (node, (0, dependencies)) x0_dependency_ranks -> In node x0_boundary_ids.
Proof.
 intro Member. pose proof x0_boundary_check as Checked.
 rewrite forallb_forall in Checked.
 specialize (Checked (node, (0, dependencies)) Member). cbn in Checked.
 change (existsb (Nat.eqb node) x0_boundary_ids = true) in Checked.
 apply existsb_exists in Checked.
 destruct Checked as [id [Inside Equal]]. apply Nat.eqb_eq in Equal. subst id. exact Inside.
Qed.
Print Assumptions x0_zero_rank_is_boundary.
