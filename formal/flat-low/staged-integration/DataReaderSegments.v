Require Import CoreSocModel ComparisonNodes FormalDataPortPreparation DataAllReaderUpdates FormalStatementSegments FormalDeclaredConnection ScalarNodeFrames MemoryWriteFrames MemorySuffixCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
Local Open Scope N_scope.
Definition data_port_decl_tail := match straight_drop 10009 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition data_before_readers := take_statements 94 data_port_decl_tail.
Definition data_after_readers := match straight_drop 10118 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma data_port_decl_position : straight_drop 10008 flat_statements = Some
 (@Qcons VarOrder.T (@Smem VarOrder.T 9178 data_port_memory) data_port_decl_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma data_before_readers_split : data_port_decl_tail = statement_append data_before_readers
 (statement_append data_all_reader_updates data_after_readers).
Proof. vm_compute. reflexivity. Qed.
Lemma data_before_readers_straight : straight_statements data_before_readers.
Proof. vm_compute. exact I. Qed.
Lemma data_before_readers_safe : memory_suffix_safe flat_memories 9178 data_before_readers.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma data_all_readers_straight : straight_statements data_all_reader_updates.
Proof. exact I. Qed.
Print Assumptions data_before_readers_safe.
