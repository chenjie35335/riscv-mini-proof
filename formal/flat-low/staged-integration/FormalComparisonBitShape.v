Require Import NormalizedBit.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Lemma comparison_false_normalized value result :
 eval_binop (Bcomp Beq) value (Gval (Fuint 1) [::false]) = Some result ->
 normalized_bit result.
Proof.
 destruct value as [ground bits|element array|bundle|t|t|t];
 unfold eval_binop, absorbing_bit, refine_boolean_result, eval_binop_basic;
 try (intro H; discriminate H).
 all: try destruct ground; try destruct t.
 all: try match goal with x : fgtyp |- _ => destruct x end.
 all: cbn; intro H.
 all: repeat match type of H with context [if ?b then _ else _] => destruct b end.
 all: cbn in H; try discriminate H; inversion H; subst; constructor.
Qed.
Print Assumptions comparison_false_normalized.
