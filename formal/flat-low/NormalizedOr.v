Require Import NormalizedBit BooleanControlFacts.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Definition normalized_or_value left right :=
 match eval_binop Bor left right with
 | Some value => value | None => Needtobedefined (Gtyp (Fuint 1)) end.
Lemma normalized_or_total left right :
 normalized_bit left -> normalized_bit right ->
 eval_binop Bor left right = Some (normalized_or_value left right).
Proof.
 intros Left Right. destruct Left as [a| | |]; destruct Right as [b| | |];
 try destruct a; try destruct b; reflexivity.
Qed.
Lemma normalized_or_normal left right :
 normalized_bit left -> normalized_bit right -> normalized_bit (normalized_or_value left right).
Proof.
 intros Left Right. destruct Left as [a| | |]; destruct Right as [b| | |];
 try destruct a; try destruct b; vm_compute; constructor.
Qed.
Lemma normalized_or_value_false left right :
 normalized_bit left -> normalized_bit right ->
 normalized_or_value left right = Gval (Fuint 1) [::false] ->
 left = Gval (Fuint 1) [::false] /\ right = Gval (Fuint 1) [::false].
Proof.
 intros Left Right Value. eapply normalized_or_false_sources; [exact Left|exact Right|].
 rewrite (normalized_or_total left right Left Right) Value. reflexivity.
Qed.
