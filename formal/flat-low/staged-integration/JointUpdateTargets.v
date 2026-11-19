Require Import JointUpdateDependencyRanks.
From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Definition joint_update_targets : list nat := [65;116;750;751;752;753;754;755;756;757;758;759;760;761;762;763;764;765;766;767;768;769;770;779;1021;1022;1023;1024;1025;1026;1027;1028;1029;1030;1031;1032;1033;1034;1035;1036;1037;1038;1039;1040;1041;1042;1043;1044;1045;1046;1047;1048;1049;1050;1051;1052;1085;1086;1087;1088;1089;1090;1091;1092;1093;1094;1095;1096;1097;1098;1099;1100;1101;1102;1103;1104;1105;1106;1107;1108;1109;1110;1111;1112;1113;1114;1115;1116;7761;7767;7781;7800;7801;7871;7872;7873;7874;7875;7876;7877;7878;7879;7880;7881;8158;8159;8160;8161;8162;8163].
Lemma joint_update_targets_checked :
 forallb (fun node => existsb (fun entry =>
 Nat.eqb node (fst entry) && Nat.leb (fst (snd entry)) 112)
 joint_update_dependency_ranks) joint_update_targets = true.
Proof. vm_compute. reflexivity. Qed.
Theorem joint_update_target_entry node : In node joint_update_targets ->
 exists rank deps, rank <= 112 /\ In (node,(rank,deps)) joint_update_dependency_ranks.
Proof.
 intro Member. pose proof joint_update_targets_checked as Check.
 rewrite forallb_forall in Check. specialize (Check node Member).
 apply existsb_exists in Check. destruct Check as [[other [rank deps]] [Inside Match]].
 apply andb_true_iff in Match. destruct Match as [Equal Bound].
 cbn in Equal, Bound. apply Nat.eqb_eq in Equal. apply Nat.leb_le in Bound.
 subst other. exists rank, deps. split; assumption.
Qed.
Print Assumptions joint_update_target_entry.
