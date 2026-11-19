Require Import CycleView CoreSocModel FormalLocalHistory ReferenceIllegalObserved ReferenceInstructionDecode RFScalarControl.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
Inductive cycle_instruction_group :=
 | CycleAddSub | CycleCompare | CycleBitwise | CycleShift | CycleUpper
 | CycleJump | CycleBranch | CycleLoad | CycleStore.
Definition cycle_group_rows group : list nat := match group with
 | CycleAddSub => [::0;11;19]
 | CycleCompare => [::1;2;12;13]
 | CycleBitwise => [::3;4;5;14;15;16]
 | CycleShift => [::6;7;8;17;18;20]
 | CycleUpper => [::9;10]
 | CycleJump => [::21;22]
 | CycleBranch => [::23;24;25;26;27;28]
 | CycleLoad => [::29;30;31;32;33]
 | CycleStore => [::34;35;36]
 end.
Lemma cycle_groups_cover row : (row<37)%coq_nat ->
 exists group,List.In row(cycle_group_rows group).
Proof. intro Bound.
 destruct row as[|row];[exists CycleAddSub;apply(List.nth_error_In(cycle_group_rows CycleAddSub)0);reflexivity|].
 destruct row as[|row];[exists CycleCompare;apply(List.nth_error_In(cycle_group_rows CycleCompare)0);reflexivity|].
 destruct row as[|row];[exists CycleCompare;apply(List.nth_error_In(cycle_group_rows CycleCompare)1);reflexivity|].
 destruct row as[|row];[exists CycleBitwise;apply(List.nth_error_In(cycle_group_rows CycleBitwise)0);reflexivity|].
 destruct row as[|row];[exists CycleBitwise;apply(List.nth_error_In(cycle_group_rows CycleBitwise)1);reflexivity|].
 destruct row as[|row];[exists CycleBitwise;apply(List.nth_error_In(cycle_group_rows CycleBitwise)2);reflexivity|].
 destruct row as[|row];[exists CycleShift;apply(List.nth_error_In(cycle_group_rows CycleShift)0);reflexivity|].
 destruct row as[|row];[exists CycleShift;apply(List.nth_error_In(cycle_group_rows CycleShift)1);reflexivity|].
 destruct row as[|row];[exists CycleShift;apply(List.nth_error_In(cycle_group_rows CycleShift)2);reflexivity|].
 destruct row as[|row];[exists CycleUpper;apply(List.nth_error_In(cycle_group_rows CycleUpper)0);reflexivity|].
 destruct row as[|row];[exists CycleUpper;apply(List.nth_error_In(cycle_group_rows CycleUpper)1);reflexivity|].
 destruct row as[|row];[exists CycleAddSub;apply(List.nth_error_In(cycle_group_rows CycleAddSub)1);reflexivity|].
 destruct row as[|row];[exists CycleCompare;apply(List.nth_error_In(cycle_group_rows CycleCompare)2);reflexivity|].
 destruct row as[|row];[exists CycleCompare;apply(List.nth_error_In(cycle_group_rows CycleCompare)3);reflexivity|].
 destruct row as[|row];[exists CycleBitwise;apply(List.nth_error_In(cycle_group_rows CycleBitwise)3);reflexivity|].
 destruct row as[|row];[exists CycleBitwise;apply(List.nth_error_In(cycle_group_rows CycleBitwise)4);reflexivity|].
 destruct row as[|row];[exists CycleBitwise;apply(List.nth_error_In(cycle_group_rows CycleBitwise)5);reflexivity|].
 destruct row as[|row];[exists CycleShift;apply(List.nth_error_In(cycle_group_rows CycleShift)3);reflexivity|].
 destruct row as[|row];[exists CycleShift;apply(List.nth_error_In(cycle_group_rows CycleShift)4);reflexivity|].
 destruct row as[|row];[exists CycleAddSub;apply(List.nth_error_In(cycle_group_rows CycleAddSub)2);reflexivity|].
 destruct row as[|row];[exists CycleShift;apply(List.nth_error_In(cycle_group_rows CycleShift)5);reflexivity|].
 destruct row as[|row];[exists CycleJump;apply(List.nth_error_In(cycle_group_rows CycleJump)0);reflexivity|].
 destruct row as[|row];[exists CycleJump;apply(List.nth_error_In(cycle_group_rows CycleJump)1);reflexivity|].
 destruct row as[|row];[exists CycleBranch;apply(List.nth_error_In(cycle_group_rows CycleBranch)0);reflexivity|].
 destruct row as[|row];[exists CycleBranch;apply(List.nth_error_In(cycle_group_rows CycleBranch)1);reflexivity|].
 destruct row as[|row];[exists CycleBranch;apply(List.nth_error_In(cycle_group_rows CycleBranch)2);reflexivity|].
 destruct row as[|row];[exists CycleBranch;apply(List.nth_error_In(cycle_group_rows CycleBranch)3);reflexivity|].
 destruct row as[|row];[exists CycleBranch;apply(List.nth_error_In(cycle_group_rows CycleBranch)4);reflexivity|].
 destruct row as[|row];[exists CycleBranch;apply(List.nth_error_In(cycle_group_rows CycleBranch)5);reflexivity|].
 destruct row as[|row];[exists CycleLoad;apply(List.nth_error_In(cycle_group_rows CycleLoad)0);reflexivity|].
 destruct row as[|row];[exists CycleLoad;apply(List.nth_error_In(cycle_group_rows CycleLoad)1);reflexivity|].
 destruct row as[|row];[exists CycleLoad;apply(List.nth_error_In(cycle_group_rows CycleLoad)2);reflexivity|].
 destruct row as[|row];[exists CycleLoad;apply(List.nth_error_In(cycle_group_rows CycleLoad)3);reflexivity|].
 destruct row as[|row];[exists CycleLoad;apply(List.nth_error_In(cycle_group_rows CycleLoad)4);reflexivity|].
 destruct row as[|row];[exists CycleStore;apply(List.nth_error_In(cycle_group_rows CycleStore)0);reflexivity|].
 destruct row as[|row];[exists CycleStore;apply(List.nth_error_In(cycle_group_rows CycleStore)1);reflexivity|].
 destruct row as[|row];[exists CycleStore;apply(List.nth_error_In(cycle_group_rows CycleStore)2);reflexivity|].
 lia. Qed.
(* This is dispatch coverage, not a theorem that execution is already correct. *)
Theorem cycle_commit_instruction_coverage memory inputs k observed view :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 cycle_reset inputs k false ->cycle_view_at(top_environment observed)view ->
 exists row group,(row<37)%coq_nat /\List.In row(cycle_group_rows group) /\
 N.land(to_N(cv_commit_instruction view))(reference_instruction_mask row)=reference_instruction_code row.
Proof.
 intros Observe Legal Reset View.
 pose proof(legal_observed_instruction_classified memory inputs k observed (cv_commit_instruction view)
 Observe Legal Reset (cva_commit_instruction _ _ View))as Classified.
 destruct(rf_legal_class_row _ Classified)as[row[Bound Match]].
 destruct(cycle_groups_cover row Bound)as[group Group].
 exists row,group;split;[exact Bound|];split;assumption.
Qed.
