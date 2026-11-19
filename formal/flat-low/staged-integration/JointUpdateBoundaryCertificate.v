Require Import JointUpdateDependencyRanks.
From Coq Require Import List Arith Bool.
Import ListNotations.
Definition joint_update_boundary_ids : list nat := [1;142;143;144;145;146;147;150;151;152;153;167;168;169;170;187;188;189;190;191;192;193;851;852;853;854;855;856;857;858;859;860;861;862;863;864;865;866;867;868;869;870;871;872;873;874;875;876;877;878;879;880;881;882;7748;7749;7750;7751;7752;7753;7754;7755;7756;7757;7758;7759;7760;7762;7768;9220;9222].
Lemma joint_update_boundary_check :
 forallb (fun entry => if Nat.eqb (fst (snd entry)) 0 then
 existsb (Nat.eqb (fst entry)) joint_update_boundary_ids else true) joint_update_dependency_ranks = true.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_zero_rank_is_boundary node dependencies :
 In (node, (0, dependencies)) joint_update_dependency_ranks -> In node joint_update_boundary_ids.
Proof.
 intro Member. pose proof joint_update_boundary_check as Checked.
 rewrite forallb_forall in Checked.
 specialize (Checked (node, (0, dependencies)) Member). cbn in Checked.
 change (existsb (Nat.eqb node) joint_update_boundary_ids = true) in Checked.
 apply existsb_exists in Checked.
 destruct Checked as [id [Inside Equal]]. apply Nat.eqb_eq in Equal. subst id. exact Inside.
Qed.
Print Assumptions joint_update_zero_rank_is_boundary.
