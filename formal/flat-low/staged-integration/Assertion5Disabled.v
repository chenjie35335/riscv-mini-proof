Require Import CoreSocModel NormalizedBit.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths.
Local Open Scope N_scope.
Lemma assertion5_disabled_by_guard env value :
 VM.find 7582 env=Some value ->normalized_bit value ->
 VM.find 7589 env=Some(Gval(Fuint 1)[::false]) ->generated_assert_m0_5_local env.
Proof.
 intros Value Normal Guard.
 unfold generated_assert_m0_5_local,generated_expr_true.
 cbn[eval_hfexpr eval_href]. rewrite Value Guard.
 destruct Normal as[bit| | |];try destruct bit;vm_compute;intro Impossible;discriminate Impossible.
Qed.
