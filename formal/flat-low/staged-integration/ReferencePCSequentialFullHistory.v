Require Import CoreSocModel ComparisonNodes FormalLocalHistory ReferencePCSequentialHistory ReferencePCSequentialValues ReferencePCResetHistory ExceptionPCSourceRegisters FormalCheckerValidStability FormalReferenceValid.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem reference_pc_sequential_full_history invalid history result pc :
 (forall i, (i < 9259)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (forall i, (i <= 9259)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::false])) ->
 size pc = 32%nat ->
 VM.find 7331 (history 9259%nat) = Some (Gval (Fuint 32) pc) ->
 VM.find 1395 (history 9259%nat) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 6507 (history 9250%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 (history 9250%nat) = Some (Gval (Fuint 1) [::false]) ->
 VM.find 6780 (history 9255%nat) = Some (Gval (Fuint 1) [::false]) ->
 formal_value_iter invalid flat_memories (history 9259%nat) true (history 9259%nat) flat_statements = Some result ->
 VM.find 7331 result = Some (Gval (Fuint 32) (reference_pc_plus_four pc)).
Proof.
 intros Steps Resets Size PC Valid Redirect Exception0 Exception5 Commit.
 assert (PC0 : VM.find 7331 (history 9250%nat) = Some (Gval (Fuint 32) pc)).
 { rewrite (proj2 (exception_pc_sources_history_stable invalid history 9259 9250 Steps ltac:(vm_compute;lia))). exact PC. }
 assert (Valid1 : VM.find 1707 (history 9251%nat) = Some (Gval (Fuint 1) [::true])).
 { apply (reference_valid_after_two invalid (history 9249%nat) (history 9250%nat) (history 9251%nat) true).
 - pose proof (checker_valid_history_stable invalid history 9259 9237 9247 false Steps Resets ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Same.
   change (VM.find 1395 (history 9249%nat) = VM.find 1395 (history 9259%nat)) in Same. rewrite Same. exact Valid.
 - apply Steps. vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 assert (Valid6 : VM.find 1707 (history 9256%nat) = Some (Gval (Fuint 1) [::true])).
 { apply (reference_valid_after_two invalid (history 9254%nat) (history 9255%nat) (history 9256%nat) true).
 - pose proof (checker_valid_history_stable invalid history 9259 9242 9247 false Steps Resets ltac:(vm_compute;lia) ltac:(vm_compute;lia)) as Same.
   change (VM.find 1395 (history 9254%nat) = VM.find 1395 (history 9259%nat)) in Same. rewrite Same. exact Valid.
 - apply Steps. vm_compute;lia.
 - apply Steps. vm_compute;lia. }
 pose proof (reference_pc_reset_after_four invalid (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) false
 (Resets 9255%nat ltac:(vm_compute;lia)) (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia))
 (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as Reset.
 apply (reference_pc_sequential_commit_after_nine invalid (history 9250%nat) (history 9251%nat) (history 9252%nat) (history 9253%nat) (history 9254%nat)
 (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) result pc Size PC0 Redirect Exception0 Valid1 Exception5 Valid6 Reset);
 try exact Commit; apply Steps; vm_compute;lia.
Qed.
