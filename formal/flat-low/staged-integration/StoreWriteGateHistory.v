Require Import StoreWriteGateNodes StoreWriteValidHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.

Lemma store_write_gate_true_step invalid old current result :
 VM.find 128 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 8029 result=Some(Gval(Fuint 1)[::true]).
Proof.
 intros Source Step.
 eapply(store_write_gate_node_step 8029 store_write_gate_expr_8029 invalid old current result).
 - unfold store_write_gate_nodes. left;reflexivity.
 - intro site. cbn[store_write_gate_expr_8029 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source. reflexivity.
 - exact Step.
Qed.

Theorem store_write_valid_false_no_exception_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8028(history t)=Some(Gval(Fuint 1)[::false])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 128(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1478(history t)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Steps Valid NoException t Lower Upper.
 eapply(store_write_valid_false_history invalid history limit (S start) Steps).
 - intros u Low High. apply Valid;lia.
 - intros [|u] Low High;[lia|]. exists true.
   exact(store_write_gate_true_step invalid (history u) (history u) (history(S u))
     (NoException u ltac:(lia) ltac:(lia)) (Steps u ltac:(lia))).
 - lia.
 - exact Upper.
Qed.
