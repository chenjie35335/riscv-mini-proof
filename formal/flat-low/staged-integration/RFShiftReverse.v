From Coq Require Import Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Definition rf_reverse_stage (word mask:bits) amount :=
 orB(andB(drop amount word)mask)
 (andB(zeros amount++take(32-amount)word)(invB mask)).
Definition rf_reverse32 word :=
 let m16:=ones 16++zeros 16 in
 let m8:=xorB m16 (zeros 8++take 24 m16) in
 let m4:=xorB m8 (zeros 4++take 28 m8) in
 let m2:=xorB m4 (zeros 2++take 30 m4) in
 let m1:=xorB m2 (zeros 1++take 31 m2) in
 rf_reverse_stage (rf_reverse_stage (rf_reverse_stage (rf_reverse_stage (rf_reverse_stage word m16 16) m8 8) m4 4) m2 2) m1 1.
Lemma rf_reverse32_correct word :size word=32%nat ->rf_reverse32 word=rev word.
Proof.
 intro Size.
 do 32 (destruct word as[|? word];[discriminate Size|]).
 destruct word;[|discriminate Size].
 cbv [rf_reverse32 rf_reverse_stage zeros ones copy take drop invB xorB andB orB lift0 lift].
 cbn. repeat rewrite ?andbT ?andbF ?orbT ?orbF ?xorbT ?xorbF. reflexivity.
Qed.
