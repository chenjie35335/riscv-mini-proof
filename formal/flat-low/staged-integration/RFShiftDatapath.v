Require Import RFShiftCenter RFShiftCenterSize RFShiftInputSelection RFShiftReverseHistory CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem rf_shift_datapath_history invalid history limit arithmetic b1 b2 direction left right :
 size left=32%nat ->(49<=limit)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)[::arithmetic;b1;b2;direction])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1151(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 let shifted:=rf_shift_center_word arithmetic(if direction then left else rev left)right in
 (forall t,(28<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1229(history t)=Some(Gval(Fuint 32)shifted)) /\
 (forall t,(49<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1278(history t)=Some(Gval(Fuint 32)(rev shifted))).
Proof.
 intros Size Limit Modes Lefts Rights Steps shifted.
 pose proof(rf_shift_selected_history invalid history limit arithmetic b1 b2 direction left Size Modes Lefts Steps)as Selected.
 assert(Center:forall t,(28<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1229(history t)=Some(Gval(Fuint 32)shifted)).
 { intros t Lower Upper.
 pose proof(rf_shift_center_history invalid(fun i=>history(Nat.add 22 i))(Nat.sub limit 22)arithmetic b1 b2 direction(if direction then left else rev left)right)as H.
 assert(S:forall i,(i<Nat.sub limit 22)%coq_nat ->formal_value_iter invalid flat_memories(history(Nat.add 22 i))false(history(Nat.add 22 i))flat_statements=Some(history(Nat.add 22(S i)))).
 { intros i Bound. replace(Nat.add 22(S i))with(S(Nat.add 22 i))by lia. apply Steps;lia. }
 specialize(H(fun i Bound=>Modes (Nat.add 22 i) ltac:(lia))(fun i Bound=>Rights (Nat.add 22 i) ltac:(lia))(fun i Bound=>Selected (Nat.add 22 i) ltac:(lia)ltac:(lia))S(Nat.sub t 22)ltac:(lia)ltac:(lia)).
 cbn beta in H. replace(Nat.add 22(Nat.sub t 22))with t in H by lia. exact H. }
 split;[exact Center|]. intros t Lower Upper.
 assert(ShiftSize:size shifted=32%nat).
 { unfold shifted. apply rf_shift_center_size. destruct direction;[exact Size|rewrite size_rev;exact Size]. }
 pose proof(rf_shift_reverse_history_1278 invalid(fun i=>history(Nat.add 28 i))(Nat.sub limit 28)shifted ShiftSize)as H.
 assert(S:forall i,(i<Nat.sub limit 28)%coq_nat ->formal_value_iter invalid flat_memories(history(Nat.add 28 i))false(history(Nat.add 28 i))flat_statements=Some(history(Nat.add 28(S i)))).
 { intros i Bound. replace(Nat.add 28(S i))with(S(Nat.add 28 i))by lia. apply Steps;lia. }
 specialize(H(fun i Bound=>Center (Nat.add 28 i) ltac:(lia)ltac:(lia))S(Nat.sub t 28)ltac:(lia)ltac:(lia)).
 cbn beta in H. replace(Nat.add 28(Nat.sub t 28))with t in H by lia. exact H.
Qed.
