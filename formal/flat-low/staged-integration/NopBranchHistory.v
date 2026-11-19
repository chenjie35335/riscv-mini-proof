Require Import NopBranchNodeShapes NopBranchValues NopKillHistory FormalInstructionResetConstants JointUpdateBoundaryHistory JointBoundaryRegisters NopBranchShapes CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalSuccessfulNodeEvaluation JointUpdateNodePositions JointUpdateExpressionCertificates NormalizedBit.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nop_branch_normalized_history_1363 invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 1363 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_shape_1363 invalid (history time) (history time) (history (S time))).
 apply Steps; lia.
Qed.
Theorem nop_branch_normalized_history_1364 invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 1364 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_shape_1364 invalid (history time) (history time) (history (S time))).
 apply Steps; lia.
Qed.
Theorem nop_branch_normalized_history_1374 invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 1374 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_shape_1374 invalid (history time) (history time) (history (S time))).
 apply Steps; lia.
Qed.
Theorem nop_branch_normalized_history_1375 invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 1375 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_shape_1375 invalid (history time) (history time) (history (S time))).
 apply Steps; lia.
Qed.
Theorem nop_branch_normalized_history_1370 invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 1370 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper.
 destruct time as [|[|time]]; try lia.
 apply (nop_branch_shape_1370 invalid (history time) (history (S time)) (history (S (S time)))); apply Steps; lia.
Qed.
Theorem nop_branch_normalized_history_1373 invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find 1373 (history time) = Some value /\ normalized_bit value.
Proof.
 intros Steps time Lower Upper.
 destruct time as [|[|time]]; try lia.
 apply (nop_branch_shape_1373 invalid (history time) (history (S time)) (history (S (S time)))); apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1359 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1359 (history time) = Some (Gval (Fuint 3) [::false;false;false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1359 invalid (history time) (history time) (history (S time))).
 - apply (nop_br_type_zero_history invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1376 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1376 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1376 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1359 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1377 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1377 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1377 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1376 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_normalized_history_1364 invalid history limit Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1378 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1378 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1378 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1359 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1379 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1379 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1379 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1378 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_normalized_history_1363 invalid history limit Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1380 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (59 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1380 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1380 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1377 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_zero_history_1379 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1381 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1381 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1381 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1359 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1382 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1382 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1382 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1381 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_normalized_history_1370 invalid history limit Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1383 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (60 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1383 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1383 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1380 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_zero_history_1382 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1384 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1384 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1384 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1359 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1385 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1385 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1385 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1384 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_normalized_history_1374 invalid history limit Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1386 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (61 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1386 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1386 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1383 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_zero_history_1385 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1387 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1387 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1387 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1359 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1388 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1388 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1388 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1387 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_normalized_history_1373 invalid history limit Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1389 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (62 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1389 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1389 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1386 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_zero_history_1388 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1390 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (57 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1390 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1390 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1359 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1391 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (58 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1391 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1391 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1390 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_normalized_history_1375 invalid history limit Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1392 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (63 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1392 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1392 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1389 invalid history limit Initial Steps time); lia.
 - apply (nop_branch_zero_history_1391 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Theorem nop_branch_zero_history_1360 invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (64 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1360 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_1360 invalid (history time) (history time) (history (S time))).
 - apply (nop_branch_zero_history_1392 invalid history limit Initial Steps time); lia.
 - apply Steps; lia.
Qed.
Definition nop_branch_false_history := nop_branch_zero_history_1360.
Theorem nop_branch_false_history_from_final invalid history limit :
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction_nop) ->
(forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (64 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1360 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Final Steps time Lower Upper.
 assert (Initial : VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop)).
 { rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps limit (Nat.le_refl limit)) in Final. exact Final. }
 exact (nop_branch_false_history invalid history limit Initial Steps time Lower Upper).
Qed.
