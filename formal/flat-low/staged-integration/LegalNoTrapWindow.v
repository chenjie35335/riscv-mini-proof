Require Import CoreSocModel ComparisonNodes FormalLocalHistory LegalBooleanHistory LegalWireNormalization LegalAssumptionActivation LegalNoTrapHistory.
From Coq Require Import ZArith Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem legal_no_trap_history_window invalid history limit start :
 (forall i, (i < limit)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (14 <= start)%coq_nat -> (Nat.add start 5 <= limit)%coq_nat ->
 VM.find 1 (history (Nat.add start 3)) = Some (Gval (Fuint 1) [::false]) ->
 generated_assume_m0_0_local (history (Nat.add start 5)) ->
 VM.find 45 (history start) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Steps Lower Upper Reset Assume.
 set (h := fun j => history (Nat.add start j)).
 assert (LocalSteps : forall j, (j < 5)%coq_nat -> formal_flat_local_step invalid (h j) (h (S j))).
 { intros j Small. unfold h. rewrite Nat.add_succ_r. apply Steps. lia. }
 destruct (legal_bool_9139_history invalid history limit Steps (Nat.add start 1) ltac:(lia) ltac:(lia))
 as [left [Left NL]].
 pose proof (Steps (Nat.pred start) ltac:(lia)) as Previous.
 assert (Next : S (Nat.pred start) = start) by lia. rewrite Next in Previous.
 destruct (legal_wire_45_normalized invalid (history (Nat.pred start)) (history (Nat.pred start)) (history start) Previous)
 as [trap [Trap NT]].
 assert (Trap0 : VM.find 45 (h 0%nat) = Some trap).
 { unfold h. rewrite Nat.add_0_r. exact Trap. }
 assert (Enabled : VM.find 9238 (h 5%nat) = Some (Gval (Fuint 1) [::true])).
 { exact (assumption_reset_enable_after_two invalid (h 3%nat) (h 4%nat) (h 5%nat)
   Reset (LocalSteps 3%nat ltac:(lia)) (LocalSteps 4%nat ltac:(lia))). }
 pose proof (active_assumption_no_trap_after_five invalid
 (h 0%nat) (h 1%nat) (h 2%nat) (h 3%nat) (h 4%nat) (h 5%nat) left trap
 Left NL Trap0 NT
 (LocalSteps 0%nat ltac:(lia)) (LocalSteps 1%nat ltac:(lia)) (LocalSteps 2%nat ltac:(lia))
 (LocalSteps 3%nat ltac:(lia)) (LocalSteps 4%nat ltac:(lia)) Assume Enabled) as NoTrap.
 unfold h in NoTrap. rewrite Nat.add_0_r in NoTrap. exact NoTrap.
Qed.
Print Assumptions legal_no_trap_history_window.
