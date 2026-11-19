Require Import RFShiftDatapath RFShiftOutput RFShiftCenter RFShiftCenterSize CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_shift_word direction arithmetic left right :=
 let selected:=if direction then left else rev left in
 let shifted:=rf_shift_center_word (direction && arithmetic) selected right in
 if direction then shifted else rev shifted.
Lemma rf_shift_word_size direction arithmetic left right :size left=32%nat ->size(rf_shift_word direction arithmetic left right)=32%nat.
Proof. intro Size. unfold rf_shift_word. destruct direction;cbn;rewrite ?size_rev;apply rf_shift_center_size;rewrite ?size_rev;exact Size. Qed.
Theorem rf_shift_alu_history invalid history limit direction arithmetic left right :
 size left=32%nat ->(54<=limit)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)(rf_shift_mode direction arithmetic))) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1151(history t)=Some(Gval(Fuint 32)left)) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1152(history t)=Some(Gval(Fuint 32)right)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,(54<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1154(history t)=Some(Gval(Fuint 32)(rf_shift_word direction arithmetic left right)).
Proof.
 intros Size Limit Modes Lefts Rights Steps.
 pose proof(rf_shift_datapath_history invalid history limit(direction && arithmetic)(negb direction)(negb direction)direction left right Size ltac:(lia))as Data.
 assert(M:forall t,(t<=limit)%coq_nat ->VM.find 1153(history t)=Some(Gval(Fuint 4)[::direction && arithmetic;negb direction;negb direction;direction])).
 { intros t Bound. pose proof(Modes t Bound)as H. destruct direction;exact H. }
 specialize(Data M Lefts Rights Steps).
 apply(rf_shift_output_history invalid history limit direction arithmetic _ (rf_shift_word_size direction arithmetic left right Size)Modes).
 - intros t Lower Upper. destruct Data as[A B]. destruct direction;[apply A;lia|apply B;lia].
 - exact Steps.
Qed.
