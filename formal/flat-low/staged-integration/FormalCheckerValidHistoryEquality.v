Require Import CoreSocModel ComparisonNodes FormalCheckerValidFullCongruence.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem checker_valid_history_equal invalid (history : nat -> VM.t hvalue) (n j k : nat) :
 (forall i, (i < n)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (Nat.add j 6 <= n)%coq_nat -> (Nat.add k 6 <= n)%coq_nat ->
 VM.find 7947 (history j) = VM.find 7947 (history k) ->
 VM.find 7765 (history j) = VM.find 7765 (history k) ->
 VM.find 65 (history j) = VM.find 65 (history k) ->
 VM.find 1395 (history (Nat.add j 6)) = VM.find 1395 (history (Nat.add k 6)).
Proof.
 intros Steps J K Reg Stall Reset.
 replace (Nat.add j 6) with (S (S (S (S (S (S j)))))) by lia.
 replace (Nat.add k 6) with (S (S (S (S (S (S k)))))) by lia.
 eapply (checker_valid_congruent_after_six invalid (history j) (history (S j)) (history (S (S j))) (history (S (S (S j)))) (history (S (S (S (S j))))) (history (S (S (S (S (S j)))))) (history (S (S (S (S (S (S j))))))) (history k) (history (S k)) (history (S (S k))) (history (S (S (S k)))) (history (S (S (S (S k))))) (history (S (S (S (S (S k)))))) (history (S (S (S (S (S (S k))))))));
 [exact Reg|exact Stall|exact Reset| | | | | | | | | | | |]; apply Steps; lia.
Qed.
Print Assumptions checker_valid_history_equal.
