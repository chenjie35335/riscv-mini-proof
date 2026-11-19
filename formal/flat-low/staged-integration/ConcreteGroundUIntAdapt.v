From nbits Require Import NBits.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
Lemma concrete_uint_normalized_width width (bits : seq bool) :
 size (zext_to width (take width bits)) = width.
Proof.
 unfold zext_to. rewrite size_zext addnC subnK; [reflexivity|].
 rewrite size_take. exact (geq_minl width (size bits)).
Qed.
Theorem concrete_ground_uint_adapt ground bits width result :
 adapt_hvalue_as_type (Gval ground bits) (Gtyp (Fuint width)) = Some result ->
 exists word, size word = width /\ result = Gval (Fuint width) word.
Proof.
 destruct ground; cbn [adapt_hvalue_as_type]; intro Adapt; try discriminate Adapt.
 inversion Adapt; subst result. eexists. split; [apply concrete_uint_normalized_width|reflexivity].
Qed.
Print Assumptions concrete_ground_uint_adapt.
