Require Import PipelinePCAdjacentTransfer FetchPCArithmetic.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Theorem pc_adjacent_successor older younger :
 pc_adjacent older younger -> younger = from_N 32 (to_N older + 4).
Proof.
 intros [OldSize [YoungSize Adjacent]].
 rewrite <- (from_N_to_N younger), YoungSize, Adjacent.
 exact (fetch_pc_from_N_mod 32 (to_N older + 4)).
Qed.
Theorem pc_adjacent_from_successor older younger :
 size older = 32%nat -> younger = from_N 32 (to_N older + 4) ->
 pc_adjacent older younger.
Proof.
 intros Size Next. subst younger. split; [exact Size|].
 split; [apply size_from_N|]. apply to_N_from_N.
Qed.
Theorem pc_adjacent_sequential_result older younger :
 pc_adjacent older younger ->
 take 32 (from_N 33 (to_N older + 4)) = younger.
Proof.
 intro Adjacent. rewrite (fetch_pc_take_from_N 33 32 (to_N older + 4) (Logic.eq_refl true)).
 symmetry. exact (pc_adjacent_successor older younger Adjacent).
Qed.
Print Assumptions pc_adjacent_successor.
Print Assumptions pc_adjacent_sequential_result.
Theorem pc_adjacent_preserves_alignment older younger :
 pc_adjacent older younger -> take 2 older = [::false;false] ->
 take 2 younger = [::false;false].
Proof.
 intros Adjacent Aligned. pose proof Adjacent as [Size Rest].
 rewrite (pc_adjacent_successor older younger Adjacent).
 rewrite (fetch_pc_take_from_N 32 2 _ (leqnn 2)).
 change (from_N 2 (to_N older + 2 ^ N.of_nat 2) = [::false;false]).
 rewrite <- from_N_wrap.
 rewrite <- (from_N_to_N older) in Aligned. rewrite Size in Aligned.
 rewrite (fetch_pc_take_from_N 32 2 _ (leqnn 2)) in Aligned. exact Aligned.
Qed.
Print Assumptions pc_adjacent_preserves_alignment.
