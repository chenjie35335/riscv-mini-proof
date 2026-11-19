Require Import StoreMaskArithmetic.
From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From firrtl Require Import Semantics_with_implicit_widths.
Lemma store_zero_extend_padding (prefix:bits) padding :
 (size prefix+padding<=32)%nat ->
 zext_to 32(prefix++zeros padding)=zext_to 32 prefix.
Proof.
 intro Bound. unfold zext_to,zext.
 rewrite size_cat size_zeros -catA zeros_cats.
 assert(E:(padding+(32-(size prefix+padding)))%nat=(32-size prefix)%nat).
 { move/leP:Bound=>Bound. rewrite /addn /addn_rec /subn /subn_rec. change (Nat.add (size prefix) padding <=32)%coq_nat in Bound. lia. }
 rewrite E. reflexivity.
Qed.
Theorem store_masked_request_result (word:bits) offset width :
 size word=32%nat ->(offset<=32)%nat ->(width<=32-offset)%nat ->
 zext_to 32(drop offset(andB(take 32(zeros offset++word))
   (zeros offset++ones width++zeros(32-offset-width))))=
 zext_to 32(take width word).
Proof.
 intros Size Offset Width.
 assert(Total:(offset+(32-offset))%nat=32%nat)by exact(subnKC Offset).
 pose proof(store_mask_shift_truncated word offset (32-offset) width ltac:(rewrite Size;exact(leq_subr _ _)) Width) as Mask.
 rewrite Total in Mask. rewrite Mask.
 apply store_zero_extend_padding.
 assert(W:(width<=size word)%nat).
 { rewrite Size. exact(leq_trans Width (leq_subr _ _)). }
 assert(TakeSize:size(take width word)=width).
 { rewrite size_take. case:ifP=>B;[reflexivity|]. apply/eqP. rewrite eqn_leq W andbT leqNgt B. reflexivity. }
 rewrite TakeSize (subnKC Width). exact(leq_subr _ _).
Qed.
