Require Import FetchPCSequentialExact FetchPCResetValue ReferencePCResetValue.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Local Open Scope N_scope.
Lemma fetch_pc_take_from_N width count value :
 (count <= width)%nat -> take count (from_N width value) = from_N count value.
Proof.
 revert width value. induction count as [|count IH]; intros width value Bound; [rewrite take0;reflexivity|].
 destruct width as [|width]; [discriminate Bound|].
 cbn [from_N]. unfold joinlsb. cbn [take]. rewrite (IH width (value / 2) Bound). reflexivity.
Qed.
Lemma fetch_pc_from_N_mod width value :
 from_N width (value mod 2 ^ N.of_nat width) = from_N width value.
Proof.
 rewrite <- (to_N_from_N width value) at 1.
 pose proof (from_N_to_N (from_N width value)) as Roundtrip.
 rewrite size_from_N in Roundtrip. exact Roundtrip.
Qed.
Lemma fetch_pc_low32_plus_four pc :
 take 32 (fetch_pc_plus_four pc) = from_N 32 (to_N pc + 4).
Proof.
 unfold fetch_pc_plus_four. rewrite <- take_min.
 change (take 32 (from_N 34 (to_N pc + 4)) = from_N 32 (to_N pc + 4)).
 apply fetch_pc_take_from_N. reflexivity.
Qed.
Theorem fetch_pc_plus_four_matches_reference pc reference :
 size reference = 32%nat ->
 N.of_nat (to_nat reference) = (N.of_nat (to_nat pc) + 4) mod 2 ^ 32 ->
 take 32 (fetch_pc_plus_four pc) = reference.
Proof.
 intros Size Relation. rewrite <- !to_N_nat in Relation.
 rewrite fetch_pc_low32_plus_four.
 rewrite <- (from_N_to_N reference) at 1. rewrite Size Relation.
 apply Logic.eq_sym. exact (fetch_pc_from_N_mod 32 (to_N pc + 4)).
Qed.
Theorem fetch_pc_plus_four_reference_aligned pc reference :
 size reference = 32%nat -> take 2 reference = [::false;false] ->
 N.of_nat (to_nat reference) = (N.of_nat (to_nat pc) + 4) mod 2 ^ 32 ->
 take 32 (fetch_pc_plus_four pc) = reference /\
 take 2 (fetch_pc_plus_four pc) = [::false;false].
Proof.
 intros Size Aligned Relation.
 pose proof (fetch_pc_plus_four_matches_reference pc reference Size Relation) as Equal.
 split; [exact Equal|]. rewrite <- Equal in Aligned. rewrite <- take_min in Aligned. exact Aligned.
Qed.
Theorem fetch_pc_plus_four_preserves_alignment pc :
 size pc = 33%nat -> take 2 pc = [::false;false] ->
 take 2 (fetch_pc_plus_four pc) = [::false;false].
Proof.
 intros Size Aligned.
 unfold fetch_pc_plus_four. rewrite <- take_min.
 change (take 2 (from_N 34 (to_N pc + 4)) = [::false;false]).
 rewrite (fetch_pc_take_from_N 34 2 _ (leqnn 2)).
 change (from_N 2 (to_N pc + 2 ^ N.of_nat 2) = [::false;false]).
 rewrite <- from_N_wrap.
 rewrite <- (from_N_to_N pc) in Aligned. rewrite Size in Aligned.
 rewrite (fetch_pc_take_from_N 33 2 _ (leqnn 2)) in Aligned.
 exact Aligned.
Qed.
Theorem fetch_pc_reset_plus_four_reference :
 take 32 (fetch_pc_plus_four fetch_pc_reset_word33) = reference_pc_reset_bits /\
 take 2 (fetch_pc_plus_four fetch_pc_reset_word33) = [::false;false].
Proof. vm_compute. split;reflexivity. Qed.
Print Assumptions fetch_pc_plus_four_matches_reference.
Print Assumptions fetch_pc_plus_four_preserves_alignment.
Print Assumptions fetch_pc_reset_plus_four_reference.
