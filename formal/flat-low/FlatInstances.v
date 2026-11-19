Require Import CoreSocModel.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Semantics_with_implicit_widths.
From simplssrlib Require Import Var.

Lemma flat_instances_exact :
 (match find_circuit_instances generated_modules generated_top with
 | Some im => SVM.elements im | None => nil end) = [:: ([::], N.of_nat 0)].
Proof. vm_compute. reflexivity. Qed.

Lemma flat_assertion_reduce p states :
 (match find_circuit_instances generated_modules generated_top with
 | Some im => generated_assert_instances (N.of_nat 0) p states (SVM.elements im)
 | None => False end) <->
 (match SVM.find [::] states with Some env => p env | None => False end).
Proof.
 remember (find_circuit_instances generated_modules generated_top) as im eqn:E.
 pose proof flat_instances_exact as H. rewrite <- E in H.
 destruct im as [im|]; [|discriminate H].
 rewrite H. cbn [generated_assert_instances].
 clear E H im.
 destruct (SVM.find nil states); simpl; intuition discriminate.
Qed.
Print Assumptions flat_assertion_reduce.
