Require Import CoreSocModel ComparisonNodes CheckerValidBitValues FormalStallHistory FormalCheckerResetConnections FormalCheckerValidStability ExceptionPCSourceRegisters.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories.
Theorem checker_valid_history_from_bubble invalid (history : nat -> VM.t hvalue) bubble :
 (forall i, (i < 9259)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 VM.find 7947 (history 9259%nat) = Some (Gval (Fuint 1) [::bubble]) ->
 VM.find 1395 (history 9259%nat) = Some (Gval (Fuint 1) [::~~ bubble]).
Proof.
 intros Steps Resets Bubble.
 assert (B6 : VM.find 7947 (history 6%nat) = Some (Gval (Fuint 1) [::bubble])).
 { rewrite (flat_register_history_same invalid history 9259 7947 formal_checker_bubble_register Steps 6 ltac:(vm_compute;lia)).
   rewrite (flat_register_history_same invalid history 9259 7947 formal_checker_bubble_register Steps 9259 ltac:(vm_compute;lia)) in Bubble.
   exact Bubble. }
 assert (Stall : VM.find 7765 (history 6%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (stall_after_six invalid (history 0%nat) (history 1%nat) (history 2%nat) (history 3%nat)
   (history 4%nat) (history 5%nat) (history 6%nat) false);
   [apply Resets|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps|apply Steps]; vm_compute;lia. }
 assert (Reset : VM.find 65 (history 6%nat) = Some (Gval (Fuint 1) [::false])).
 { apply (reset_connection_65_transfer invalid (history 5%nat) (history 5%nat) (history 6%nat) false).
   - apply (reset_connection_24_transfer invalid (history 4%nat) (history 4%nat) (history 5%nat) false);
     [apply Resets|apply Steps]; vm_compute;lia.
   - apply Steps. vm_compute;lia. }
 pose proof (checker_valid_history_stable invalid history 9259 0 9247 false Steps Resets
 ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Same.
 change (VM.find 1395 (history 12%nat) = VM.find 1395 (history 9259%nat)) in Same.
 pose proof (checker_valid_bits_after_six invalid (history 6%nat) (history 7%nat) (history 8%nat)
 (history 9%nat) (history 10%nat) (history 11%nat) (history 12%nat) bubble false false
 B6 Stall Reset (Steps 6%nat ltac:(vm_compute;lia)) (Steps 7%nat ltac:(vm_compute;lia))
 (Steps 8%nat ltac:(vm_compute;lia)) (Steps 9%nat ltac:(vm_compute;lia))
 (Steps 10%nat ltac:(vm_compute;lia)) (Steps 11%nat ltac:(vm_compute;lia))) as Value.
 rewrite !orbF in Value. rewrite <- Same. exact Value.
Qed.
Print Assumptions checker_valid_history_from_bubble.
