Require Import CoreSocModel ComparisonNodes RegisterInvariants StagedRegisterHold.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma exception_pc_implementation_register : has_register 7751 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exception_pc_reference_register : has_register 7331 flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem flat_register_history_same invalid history limit id :
 has_register id flat_statements = true ->
 (forall time, (time < limit)%coq_nat ->
 formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat ->
 VM.find id (history time) = VM.find id (history 0%nat).
Proof.
 intros Register Steps time. induction time as [|time IH]; intro Within; [reflexivity|].
 rewrite (staged_combinational_holds_registers invalid flat_memories (history time) (history time)
 (history (S time)) flat_statements id Register (Steps time ltac:(lia))).
 apply IH. lia.
Qed.
Theorem exception_pc_sources_history_stable invalid history limit time :
 (forall i, (i < limit)%coq_nat ->
 formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (time <= limit)%coq_nat ->
 VM.find 7751 (history time) = VM.find 7751 (history limit) /\
 VM.find 7331 (history time) = VM.find 7331 (history limit).
Proof.
 intros Steps Bound. split.
 - rewrite (flat_register_history_same invalid history limit 7751 exception_pc_implementation_register Steps time Bound).
   symmetry. exact (flat_register_history_same invalid history limit 7751 exception_pc_implementation_register Steps limit (Nat.le_refl _)).
 - rewrite (flat_register_history_same invalid history limit 7331 exception_pc_reference_register Steps time Bound).
   symmetry. exact (flat_register_history_same invalid history limit 7331 exception_pc_reference_register Steps limit (Nat.le_refl _)).
Qed.
Print Assumptions exception_pc_sources_history_stable.
