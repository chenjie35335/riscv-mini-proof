Require Import StoreWriteValidFalse WriteEnableNormalized FormalDeclaredWireCheck DUTRedirectDecode CoreSocModel ComparisonNodes.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_write_valid_port_false invalid old current result :
 VM.find 8202 old=Some(Gval(Fuint 1)[::false]) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find 1478 result=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Source Step. eapply declared_wire_checked_value;
 [exact write_valid_certificate_1478|exact Source|reflexivity|exact Step].
Qed.
Theorem store_write_valid_false_history invalid history limit start :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8028(history t)=Some(Gval(Fuint 1)[::false])) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->exists bit,VM.find 8029(history t)=Some(Gval(Fuint 1)[::bit])) ->
 forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1478(history t)=Some(Gval(Fuint 1)[::false]).
Proof.
 intros Steps Valid Gate [|[|[|[|[|t]]]]] Lower Upper;try lia.
 eapply(store_write_valid_port_false invalid (history(S(S(S(S t)))))(history(S(S(S(S t)))))(history(S(S(S(S(S t)))))));[|apply Steps;lia].
 eapply(store_write_valid_false_8202 invalid (history(S(S(S t))))(history(S(S(S t))))(history(S(S(S(S t))))));[|apply Steps;lia].
 eapply(store_write_valid_false_8082 invalid (history(S(S t)))(history(S(S t)))(history(S(S(S t)))));[|apply Steps;lia].
 eapply(store_write_valid_false_8081 invalid (history(S t))(history(S t))(history(S(S t))));[|apply Steps;lia].
 destruct(Gate t ltac:(lia)ltac:(lia))as[bit Bit].
 exact(store_write_valid_false_8030 invalid (history t)(history t)(history(S t))bit(Valid t ltac:(lia)ltac:(lia))Bit(Steps t ltac:(lia))).
Qed.
