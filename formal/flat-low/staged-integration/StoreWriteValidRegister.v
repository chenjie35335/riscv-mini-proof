Require Import CoreSocModel ComparisonNodes RegisterInvariants StagedRegisterHold.
From Coq Require Import NArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma store_write_valid_register : has_register 8028 flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_write_valid_register_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(t<=limit)%coq_nat ->VM.find 8028(history t)=VM.find 8028(history 0%nat).
Proof.
 intros Steps t. induction t as[|t IH];intro Bound;[reflexivity|].
 rewrite(staged_combinational_holds_registers invalid flat_memories(history t)(history t)(history(S t))flat_statements 8028 store_write_valid_register(Steps t ltac:(lia))).
 apply IH;lia.
Qed.
