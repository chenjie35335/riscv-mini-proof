Require Import ConcreteUIntOperations.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths Semantics_with_implicit_widths.
Lemma ground_or_uint left lb right rb result :
 eval_binop Bor (Gval left lb) (Gval right rb) = Some result ->
 concrete_uint_value result.
Proof.
 unfold eval_binop.
 destruct (absorbing_bit Bor (Gval left lb) (Gval right rb)) as [known|];
 destruct left; destruct right;
 cbn [eval_binop_basic refine_boolean_result]; intro Eval;
 try discriminate Eval; inversion Eval; subst; do 2 eexists; reflexivity.
Qed.
Print Assumptions ground_or_uint.
