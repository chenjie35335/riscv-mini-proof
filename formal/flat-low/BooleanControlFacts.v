Require Import NormalizedBit.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Lemma normalized_or_false_sources left right :
 normalized_bit left -> normalized_bit right ->
 eval_binop Bor left right = Some (Gval (Fuint 1) [::false]) ->
 left = Gval (Fuint 1) [::false] /\ right = Gval (Fuint 1) [::false].
Proof.
 intros Left Right. destruct Left as [a| | |]; destruct Right as [b| | |];
 try destruct a; try destruct b; vm_compute; intro Result; try discriminate Result;
 split; reflexivity.
Qed.
Lemma normalized_and_true_sources left right :
 normalized_bit left -> normalized_bit right ->
 eval_binop Band left right = Some (Gval (Fuint 1) [::true]) ->
 left = Gval (Fuint 1) [::true] /\ right = Gval (Fuint 1) [::true].
Proof.
 intros Left Right. destruct Left as [a| | |]; destruct Right as [b| | |];
 try destruct a; try destruct b; vm_compute; intro Result; try discriminate Result;
 split; reflexivity.
Qed.
Lemma normalized_adaptation_recovers_bit value bit :
 normalized_bit value ->
 adapt_hvalue_as_type value (Gtyp (Fuint 1)) = Some (Gval (Fuint 1) [::bit]) ->
 value = Gval (Fuint 1) [::bit].
Proof.
 intro Normal. destruct Normal as [b| | |]; try destruct b; destruct bit;
 vm_compute; intro Result; try discriminate Result; reflexivity.
Qed.
Print Assumptions normalized_or_false_sources.
