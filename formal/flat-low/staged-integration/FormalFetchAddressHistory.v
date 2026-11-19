Require Import CoreSocModel ComparisonNodes FormalFetchAddressNodes FormalLocalHistory.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma fetch_divide_concrete old bits :
 VM.find 30 old = Some (Gval (Fuint 32) bits) ->
 exists divided, eval_hfexpr_with_memory flat_memories fetch_address_expr_9181 old old = Some (Gval (Fuint 32) divided).
Proof.
 intro Value. cbn [fetch_address_expr_9181 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Value. eexists. reflexivity.
Qed.
Lemma fetch_extract_concrete old bits :
 VM.find 9181 old = Some (Gval (Fuint 32) bits) ->
 exists address, eval_hfexpr_with_memory flat_memories fetch_address_expr_9219 old old = Some (Gval (Fuint 4) address).
Proof.
 intro Value. cbn [fetch_address_expr_9219 eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Value. eexists. reflexivity.
Qed.
Theorem fetch_address_after_two invalid s0 s1 s2 pc :
 VM.find 30 s0 = Some (Gval (Fuint 32) pc) ->
 formal_flat_local_step invalid s0 s1 -> formal_flat_local_step invalid s1 s2 ->
 exists address, VM.find 9219 s2 = Some (Gval (Fuint 4) address).
Proof.
 intros PC First Second.
 destruct (fetch_divide_concrete s0 pc PC) as [divided Divided].
 assert (Middle : VM.find 9181 s1 = Some (Gval (Fuint 32) divided)).
 { eapply fetch_address_node_9181; [exact Divided|reflexivity|exact First]. }
 destruct (fetch_extract_concrete s1 divided Middle) as [address Address].
 exists address. eapply fetch_address_node_9219; [exact Address|reflexivity|exact Second].
Qed.
Print Assumptions fetch_address_after_two.
