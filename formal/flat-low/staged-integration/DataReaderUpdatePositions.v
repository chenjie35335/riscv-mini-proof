Require Import DataReaderUpdateBlocks FormalStatementSegments FormalDeclaredConnection ScalarNodeFrames ComparisonNodes.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import HiFirrtl_with_implicit_widths.
Lemma data_reader_block_straight_2 : straight_statements data_reader_updates_2.
Proof. exact I. Qed.
Lemma data_reader_block_count_2 : statement_count data_reader_updates_2 = 3.
Proof. reflexivity. Qed.
Lemma data_reader_block_position_2 :
 match straight_drop 10103 flat_statements with
 | Some tail => take_statements 3 tail
 | None => @Qnil VarOrder.T end = data_reader_updates_2.
Proof. vm_compute. reflexivity. Qed.
Lemma data_reader_block_straight_3 : straight_statements data_reader_updates_3.
Proof. exact I. Qed.
Lemma data_reader_block_count_3 : statement_count data_reader_updates_3 = 3.
Proof. reflexivity. Qed.
Lemma data_reader_block_position_3 :
 match straight_drop 10106 flat_statements with
 | Some tail => take_statements 3 tail
 | None => @Qnil VarOrder.T end = data_reader_updates_3.
Proof. vm_compute. reflexivity. Qed.
Lemma data_reader_block_straight_4 : straight_statements data_reader_updates_4.
Proof. exact I. Qed.
Lemma data_reader_block_count_4 : statement_count data_reader_updates_4 = 3.
Proof. reflexivity. Qed.
Lemma data_reader_block_position_4 :
 match straight_drop 10109 flat_statements with
 | Some tail => take_statements 3 tail
 | None => @Qnil VarOrder.T end = data_reader_updates_4.
Proof. vm_compute. reflexivity. Qed.
Lemma data_reader_block_straight_5 : straight_statements data_reader_updates_5.
Proof. exact I. Qed.
Lemma data_reader_block_count_5 : statement_count data_reader_updates_5 = 3.
Proof. reflexivity. Qed.
Lemma data_reader_block_position_5 :
 match straight_drop 10112 flat_statements with
 | Some tail => take_statements 3 tail
 | None => @Qnil VarOrder.T end = data_reader_updates_5.
Proof. vm_compute. reflexivity. Qed.
Lemma data_reader_block_straight_1 : straight_statements data_reader_updates_1.
Proof. exact I. Qed.
Lemma data_reader_block_count_1 : statement_count data_reader_updates_1 = 3.
Proof. reflexivity. Qed.
Lemma data_reader_block_position_1 :
 match straight_drop 10115 flat_statements with
 | Some tail => take_statements 3 tail
 | None => @Qnil VarOrder.T end = data_reader_updates_1.
Proof. vm_compute. reflexivity. Qed.
