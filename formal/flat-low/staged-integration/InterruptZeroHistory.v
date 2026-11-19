Require Import CoreSocModel ComparisonNodes InterruptZeroNodes InterruptZeroConnections FormalLocalHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem interrupt_zero_history invalid history limit :
 (forall time, (time < limit)%coq_nat -> formal_flat_local_step invalid (history time) (history (S time))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1470 (history time) = Some (Gval (Fuint 32) interrupt_zero) /\
 VM.find 1668 (history time) = Some (Gval (Fuint 32) interrupt_zero).
Proof.
 intros Steps time Depth Within.
 destruct time as [|time]; [lia|].
 destruct time as [|time]; [lia|].
 destruct time as [|time]; [lia|].
 destruct time as [|time]; [lia|].
 destruct time as [|time]; [lia|].
 pose proof (interrupt_774_zero invalid (history (time)) (history (time)) (history (S (time))) (Steps (time) ltac:(lia))) as H774.
 pose proof (interrupt_135_zero invalid (history (S (time))) (history (S (time))) (history (S (S (time)))) H774 (Steps (S (time)) ltac:(lia))) as H135.
 pose proof (interrupt_8154_zero invalid (history (S (S (time)))) (history (S (S (time)))) (history (S (S (S (time))))) H135 (Steps (S (S (time))) ltac:(lia))) as H8154.
 pose proof (interrupt_8243_zero invalid (history (S (S (S (time))))) (history (S (S (S (time))))) (history (S (S (S (S (time)))))) H8154 (Steps (S (S (S (time)))) ltac:(lia))) as H8243.
 pose proof (interrupt_1470_zero invalid (history (S (S (S (S (time)))))) (history (S (S (S (S (time)))))) (history (S (S (S (S (S (time))))))) H8243 (Steps (S (S (S (S (time))))) ltac:(lia))) as H1470.
 pose proof (interrupt_7203_zero invalid (history (S (time))) (history (S (time))) (history (S (S (time)))) (Steps (S (time)) ltac:(lia))) as H7203.
 pose proof (interrupt_7204_zero invalid (history (S (S (time)))) (history (S (S (time)))) (history (S (S (S (time))))) H7203 (Steps (S (S (time))) ltac:(lia))) as H7204.
 pose proof (interrupt_1858_zero invalid (history (S (S (S (time))))) (history (S (S (S (time))))) (history (S (S (S (S (time)))))) H7204 (Steps (S (S (S (time)))) ltac:(lia))) as H1858.
 pose proof (interrupt_1668_zero invalid (history (S (S (S (S (time)))))) (history (S (S (S (S (time)))))) (history (S (S (S (S (S (time))))))) H1858 (Steps (S (S (S (S (time))))) ltac:(lia))) as H1668.
 split; assumption.
Qed.
Print Assumptions interrupt_zero_history.
