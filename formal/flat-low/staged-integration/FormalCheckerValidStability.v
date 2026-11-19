Require Import CoreSocModel ComparisonNodes FormalCheckerValidHistoryEquality StagedRegisterHold FormalStallHistory FormalCheckerResetConnections RegisterInvariants.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma formal_checker_bubble_register : has_register 7947 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem checker_valid_history_stable invalid (history : nat -> VM.t hvalue) (n j k : nat) bit :
 (forall i, (i < n)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= n)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::bit])) ->
 (Nat.add j 12 <= n)%coq_nat -> (Nat.add k 12 <= n)%coq_nat ->
 VM.find 1395 (history (Nat.add j 12)) = VM.find 1395 (history (Nat.add k 12)).
Proof.
 intros Steps Resets J K.
 assert (Hold : forall i, (i <= n)%coq_nat -> VM.find 7947 (history i) = VM.find 7947 (history 0%nat)).
 { intros i. induction i as [|i IH]; intro Bound; [reflexivity|].
   rewrite (staged_combinational_holds_registers invalid flat_memories (history i) (history i) (history (S i)) flat_statements 7947 formal_checker_bubble_register (Steps i ltac:(lia))).
   apply IH. lia. }
 assert (Stall : forall i, (Nat.add i 6 <= n)%coq_nat -> VM.find 7765 (history (Nat.add i 6)) = Some (Gval (Fuint 1) [::bit])).
 { intros i Bound. replace (Nat.add i 6) with (S (S (S (S (S (S i)))))) by lia.
   eapply (stall_after_six invalid (history i) (history (S i)) (history (S (S i))) (history (S (S (S i)))) (history (S (S (S (S i))))) (history (S (S (S (S (S i)))))) (history (S (S (S (S (S (S i))))))) bit);
   [apply Resets; lia| | | | | |]; apply Steps; lia. }
 assert (Reset : forall i, (Nat.add i 2 <= n)%coq_nat -> VM.find 65 (history (Nat.add i 2)) = Some (Gval (Fuint 1) [::bit])).
 { intros i Bound. replace (Nat.add i 2) with (S (S i)) by lia.
   eapply (reset_connection_65_transfer invalid (history (S i)) (history (S i)) (history (S (S i))) bit).
   - eapply (reset_connection_24_transfer invalid (history i) (history i) (history (S i)) bit); [apply Resets; lia|apply Steps; lia].
   - apply Steps. lia. }
 replace (Nat.add j 12) with (Nat.add (Nat.add j 6) 6) by lia.
 replace (Nat.add k 12) with (Nat.add (Nat.add k 6) 6) by lia.
 eapply checker_valid_history_equal; [exact Steps|lia|lia| | |].
 - rewrite (Hold (Nat.add j 6) ltac:(lia)) (Hold (Nat.add k 6) ltac:(lia)). reflexivity.
 - rewrite (Stall j ltac:(lia)) (Stall k ltac:(lia)). reflexivity.
 - replace (Nat.add j 6) with (Nat.add (Nat.add j 4) 2) by lia.
   replace (Nat.add k 6) with (Nat.add (Nat.add k 4) 2) by lia.
   rewrite (Reset (Nat.add j 4) ltac:(lia)) (Reset (Nat.add k 4) ltac:(lia)). reflexivity.
Qed.
Print Assumptions checker_valid_history_stable.
