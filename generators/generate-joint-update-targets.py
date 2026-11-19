"""Certify update-source target coverage and maximum dependency depth."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
r=json.loads((root/'formal/flat-low/joint-update-dependency-ranks.json').read_text());targets=sorted(map(int,r['targets']))
s='''Require Import JointUpdateDependencyRanks.
From Coq Require Import List Arith Bool Lia.
Import ListNotations.
Definition joint_update_targets : list nat := ['''+';'.join(map(str,targets))+'''].
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
'''
f=p/'JointUpdateTargets.v'
if not f.exists() or f.read_text()!=s:f.write_text(s)
