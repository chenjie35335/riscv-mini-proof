Require Import NopKillHistory NopPCSelectValues.
Require Import CoreSocModel ComparisonNodes NopKillValues FormalInstructionResetConstants JointUpdateBoundaryHistory JointBoundaryRegisters.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem nop_pc_select_history_8361 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8361 (history time) = Some nop_pc_select_value_8361.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8361 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8360 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8362 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8362 (history time) = Some nop_pc_select_value_8362.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8362 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8358 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8361 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8363 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8363 (history time) = Some nop_pc_select_value_8363.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8363 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8356 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8362 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8364 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8364 (history time) = Some nop_pc_select_value_8364.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8364 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8354 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8363 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8365 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8365 (history time) = Some nop_pc_select_value_8365.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8365 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8352 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8364 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8366 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8366 (history time) = Some nop_pc_select_value_8366.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8366 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8350 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8365 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8367 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8367 (history time) = Some nop_pc_select_value_8367.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8367 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8348 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8366 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8368 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8368 (history time) = Some nop_pc_select_value_8368.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8368 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8346 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8367 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8369 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8369 (history time) = Some nop_pc_select_value_8369.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8369 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8344 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8368 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8370 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8370 (history time) = Some nop_pc_select_value_8370.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8370 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8342 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8369 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8371 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8371 (history time) = Some nop_pc_select_value_8371.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8371 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8340 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8370 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8372 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8372 (history time) = Some nop_pc_select_value_8372.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8372 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8338 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8371 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8373 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8373 (history time) = Some nop_pc_select_value_8373.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8373 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8336 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8372 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8374 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8374 (history time) = Some nop_pc_select_value_8374.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8374 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8334 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8373 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8375 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8375 (history time) = Some nop_pc_select_value_8375.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8375 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8332 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8374 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8376 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8376 (history time) = Some nop_pc_select_value_8376.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8376 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8330 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8375 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8377 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8377 (history time) = Some nop_pc_select_value_8377.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8377 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8328 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8376 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8378 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8378 (history time) = Some nop_pc_select_value_8378.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8378 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8326 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8377 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8379 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8379 (history time) = Some nop_pc_select_value_8379.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8379 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8324 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8378 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8380 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8380 (history time) = Some nop_pc_select_value_8380.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8380 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8322 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8379 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8381 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8381 (history time) = Some nop_pc_select_value_8381.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8381 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8320 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8380 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8382 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8382 (history time) = Some nop_pc_select_value_8382.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8382 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8318 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8381 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8383 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8383 (history time) = Some nop_pc_select_value_8383.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8383 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8316 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8382 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8384 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8384 (history time) = Some nop_pc_select_value_8384.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8384 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8314 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8383 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8385 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8385 (history time) = Some nop_pc_select_value_8385.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8385 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8312 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8384 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8386 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8386 (history time) = Some nop_pc_select_value_8386.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8386 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8310 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8385 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8387 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8387 (history time) = Some nop_pc_select_value_8387.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8387 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8308 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8386 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8388 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8388 (history time) = Some nop_pc_select_value_8388.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8388 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8306 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8387 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8389 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8389 (history time) = Some nop_pc_select_value_8389.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8389 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8304 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8388 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8390 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8390 (history time) = Some nop_pc_select_value_8390.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8390 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8302 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8389 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8391 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8391 (history time) = Some nop_pc_select_value_8391.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8391 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8300 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8390 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8392 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8392 (history time) = Some nop_pc_select_value_8392.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8392 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8298 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8391 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8393 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8393 (history time) = Some nop_pc_select_value_8393.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8393 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8296 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8392 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8394 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8394 (history time) = Some nop_pc_select_value_8394.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8394 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8294 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8393 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8395 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8395 (history time) = Some nop_pc_select_value_8395.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8395 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8292 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8394 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8396 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8396 (history time) = Some nop_pc_select_value_8396.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8396 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8290 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8395 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8397 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8397 (history time) = Some nop_pc_select_value_8397.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8397 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8288 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8396 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8398 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8398 (history time) = Some nop_pc_select_value_8398.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8398 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8286 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8397 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8399 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8399 (history time) = Some nop_pc_select_value_8399.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8399 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8284 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8398 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8400 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8400 (history time) = Some nop_pc_select_value_8400.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8400 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8282 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8399 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8401 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (45 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8401 (history time) = Some nop_pc_select_value_8401.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8401 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8280 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8400 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8402 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (46 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8402 (history time) = Some nop_pc_select_value_8402.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8402 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8278 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8401 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8403 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (47 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8403 (history time) = Some nop_pc_select_value_8403.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8403 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8276 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8402 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8404 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (48 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8404 (history time) = Some nop_pc_select_value_8404.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8404 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8274 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8403 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8405 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (49 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8405 (history time) = Some nop_pc_select_value_8405.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8405 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8272 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8404 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8406 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (50 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8406 (history time) = Some nop_pc_select_value_8406.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8406 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8270 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8405 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8407 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (51 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8407 (history time) = Some nop_pc_select_value_8407.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8407 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8268 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8406 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8408 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (52 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8408 (history time) = Some nop_pc_select_value_8408.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8408 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8266 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8407 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8409 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (53 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8409 (history time) = Some nop_pc_select_value_8409.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8409 invalid (history time) (history time) (history (S time))).
 - apply (nop_kill_history_8264 invalid history limit Initial Steps time); lia.
 - apply (nop_pc_select_history_8408 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_8250 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (54 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 8250 (history time) = Some nop_pc_select_value_8250.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_8250 invalid (history time) (history time) (history (S time))).
 - apply (nop_pc_select_history_8409 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_84 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 84 (history time) = Some nop_pc_select_value_84.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_84 invalid (history time) (history time) (history (S time))).
 - apply (nop_pc_select_history_8250 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_7771 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7771 (history time) = Some nop_pc_select_value_7771.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_7771 invalid (history time) (history time) (history (S time))).
 - apply (nop_pc_select_history_84 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_7772 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7772 (history time) = Some nop_pc_select_value_7772.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_7772 invalid (history time) (history time) (history (S time))).
 - apply (nop_pc_select_history_84 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_history_7776 invalid history limit :
 VM.find 7748 (history 0%nat) = Some nop_kill_value_7748 ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7776 (history time) = Some nop_pc_select_value_7776.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_pc_select_step_7776 invalid (history time) (history time) (history (S time))).
 - apply (nop_pc_select_history_84 invalid history limit Initial Steps time); lia.
 - apply Steps. lia.
Qed.
Theorem nop_pc_select_zero_history invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 84 (history time) = Some (Gval (Fuint 2) [::false;false]).
Proof.
 intros Initial Steps time Lower Upper.
 exact (nop_pc_select_history_84 invalid history limit Initial Steps time Lower Upper).
Qed.
Theorem nop_pc_select_zero_history_from_final invalid history limit :
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 84 (history time) = Some (Gval (Fuint 2) [::false;false]).
Proof.
 intros Final Steps.
 rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps limit (Nat.le_refl _)) in Final.
 exact (nop_pc_select_zero_history invalid history limit Final Steps).
Qed.
Print Assumptions nop_pc_select_zero_history.
Theorem nop_pc_select_7771_false_history invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7771 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 exact (nop_pc_select_history_7771 invalid history limit Initial Steps time Lower Upper).
Qed.
Theorem nop_pc_select_7771_false_history_from_final invalid history limit :
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7771 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Final Steps.
 rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps limit (Nat.le_refl _)) in Final.
 exact (nop_pc_select_7771_false_history invalid history limit Final Steps).
Qed.
Print Assumptions nop_pc_select_7771_false_history.
Theorem nop_pc_select_7772_false_history invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7772 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 exact (nop_pc_select_history_7772 invalid history limit Initial Steps time Lower Upper).
Qed.
Theorem nop_pc_select_7772_false_history_from_final invalid history limit :
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7772 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Final Steps.
 rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps limit (Nat.le_refl _)) in Final.
 exact (nop_pc_select_7772_false_history invalid history limit Final Steps).
Qed.
Print Assumptions nop_pc_select_7772_false_history.
Theorem nop_pc_select_7776_false_history invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7776 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Initial Steps time Lower Upper.
 exact (nop_pc_select_history_7776 invalid history limit Initial Steps time Lower Upper).
Qed.
Theorem nop_pc_select_7776_false_history_from_final invalid history limit :
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction_nop) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 7776 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Final Steps.
 rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps limit (Nat.le_refl _)) in Final.
 exact (nop_pc_select_7776_false_history invalid history limit Final Steps).
Qed.
Print Assumptions nop_pc_select_7776_false_history.
