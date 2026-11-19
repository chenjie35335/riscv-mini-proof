Require Import CoreSocModel ComparisonNodes FormalDeclaredWireCheck DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates JointUpdateNodePositions JointUpdateExpressionCertificates JointBoundaryRegisters JointUpdateBoundaryHistory X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalGroundNodeEquation.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Record wbkill_value := WbkillValue { wbkill_kill : bool; wbkill_low : bool; wbkill_high : bool; wbkill_enable : bool }.
Record wbkill_row := WbkillRow { wbkill_mask : bits; wbkill_code : bits; wbkill_row_value : wbkill_value }.
Definition wbkill_default_value := WbkillValue false false false false.
Definition wbkill_default_row := WbkillRow [::] [::] wbkill_default_value.
Definition wbkill_rows : seq wbkill_row := [::
WbkillRow [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;true;false;false;false;false;false;false;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue true true true false);
WbkillRow [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue false true true false);
WbkillRow [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true] [::true;true;false;false;true;true;true] (WbkillValue false true true false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;true;true;true] (WbkillValue true true true true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;false;true;true] (WbkillValue true true true true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;true;false;true] (WbkillValue true true true true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;true;true] (WbkillValue true true true true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;false;true] (WbkillValue true true true true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;true;true;false;false;false;false;false;true] (WbkillValue true true true true);
WbkillRow [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true] [::true;true;true;true;false;false;false;false;false;false;false;false;true] (WbkillValue true false false false);
WbkillRow [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;false;false;false;false;true;true;true;true] [::true;true;true;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;true;true;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;false;true;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;true;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;true;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;true;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;true;false;true;false;false;false;false;false;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;true;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;true;true;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;false;true;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;true;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true;false;false;false;false;false;false;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;false;false;false;false;false;false;false;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;false;false;false;false;false;false;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;false;false;false;false;false;false;false;true;false;true] (WbkillValue true true false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue true true false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue true true false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;false;false;false;false;false;false;false;true] (WbkillValue true true false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true] (WbkillValue true true false true);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;true;false;false;false;false;false;true;true;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;true;false;false;false;false;false;false;true;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;true;false;false;false;false;false;true;false;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;true;false;false;false;false;false;false;false;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;true;false;false;false;false;false;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;false;false;false;true;true] (WbkillValue false false false false);
WbkillRow [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true] [::true;true;true;false;false;true;true] (WbkillValue true false true true);
WbkillRow [::true;true;true;true;true;true;true] [::true;true;true;true;false;true;true] (WbkillValue true false true true);
WbkillRow [::true;true;true;true;true;true;true] [::true;true;true;false;true] (WbkillValue false false false true);
WbkillRow [::true;true;true;true;true;true;true] [::true;true;true;false;true;true] (WbkillValue false false false true)].
Definition wbkill_choice instruction row := to_N (wbkill_code row) == to_N (andB instruction (wbkill_mask row)).
Fixpoint wbkill_decode (stage : nat) instruction : wbkill_value :=
 match stage with
 | O => wbkill_default_value
 | S previous => let row := nth wbkill_default_row wbkill_rows previous in
   if wbkill_choice instruction row then wbkill_row_value row else wbkill_decode previous instruction
 end.
Definition wbkill_safe value := (wbkill_enable value && (wbkill_low value || wbkill_high value)) ==> wbkill_kill value.
Lemma wbkill_rows_safe index : (index < 49)%coq_nat -> wbkill_safe (wbkill_row_value (nth wbkill_default_row wbkill_rows index)) = true.
Proof. intro Bound.
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 destruct index as [|index]. { vm_compute; reflexivity. }
 lia. Qed.
Lemma wbkill_decode_safe stage instruction : (stage <= 49)%coq_nat -> wbkill_safe (wbkill_decode stage instruction) = true.
Proof.
 induction stage as [|stage IH]; intro Bound; [reflexivity|].
 cbn [wbkill_decode]. destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows stage)).
 - apply wbkill_rows_safe. lia.
 - apply IH. lia.
Qed.
Lemma wbkill_and_value width left right :
 eval_binop Band (Gval (Fuint 32) left) (Gval (Fuint width) right) = Some (Gval (Fuint (maxn 32 width)) (andB left right)).
Proof.
 unfold eval_binop. cbn [eval_binop_basic].
 destruct (absorbing_bit Band (Gval (Fuint 32) left) (Gval (Fuint width) right)); reflexivity.
Qed.
Lemma wbkill_eq_value width code masked :
 eval_binop (Bcomp Beq) (Gval (Fuint width) code) (Gval (Fuint 32) masked) = Some (Gval (Fuint 1) [::to_N code == to_N masked]).
Proof.
 unfold eval_binop. cbn [eval_binop_basic].
 destruct (absorbing_bit (Bcomp Beq) (Gval (Fuint width) code) (Gval (Fuint 32) masked)); reflexivity.
Qed.
Lemma wbkill_wire_83_checked : declared_wire_check flat_memories flat_statements 60%nat 8703%nat 83 7748 32%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_wire_8249_checked : declared_wire_check flat_memories flat_statements 9009%nat 995%nat 8249 83 32%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_wire_8251_checked : declared_wire_check flat_memories flat_statements 9011%nat 749%nat 8251 8998 1%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_wire_85_checked : declared_wire_check flat_memories flat_statements 62%nat 9928%nat 85 8251 1%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_wire_8259_checked : declared_wire_check flat_memories flat_statements 9019%nat 749%nat 8259 8850 2%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_wire_93_checked : declared_wire_check flat_memories flat_statements 70%nat 9928%nat 93 8259 2%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_wire_8260_checked : declared_wire_check flat_memories flat_statements 9020%nat 749%nat 8260 8999 1%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_wire_94_checked : declared_wire_check flat_memories flat_statements 71%nat 9928%nat 94 8260 1%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma wbkill_instruction_member : List.In (7748%nat,32%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers 53%nat). vm_compute. reflexivity. Qed.
Theorem control_writeback_decode_history invalid history limit instruction :
 size instruction = 32%nat ->
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 85 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49 instruction)]) /\
 VM.find 93 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49 instruction);wbkill_high (wbkill_decode 49 instruction)]) /\
 VM.find 94 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49 instruction)]).
Proof.
 intros Size Initial Steps.
 assert (H7748 : forall time, (time <= limit)%coq_nat -> VM.find 7748 (history time) = Some (Gval (Fuint 32) instruction)).
 { intros time Upper. rewrite (joint_update_register_history_same invalid history limit 7748 32 wbkill_instruction_member Steps time Upper). exact Initial. }
 assert (H83 : forall time, (1 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 83 (history time) = Some (Gval (Fuint 32) instruction)).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 60%nat 8703%nat 83 7748 32%nat (Gval (Fuint 32) instruction) (Gval (Fuint 32) instruction) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_83_checked|apply H7748;lia| |apply Steps;lia].
  cbn [adapt_hvalue_as_type]. assert (Take : take 32 instruction = instruction). { apply take_oversize. rewrite Size. reflexivity. }
  rewrite Take. unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
 }
 assert (H8249 : forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8249 (history time) = Some (Gval (Fuint 32) instruction)).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 9009%nat 995%nat 8249 83 32%nat (Gval (Fuint 32) instruction) (Gval (Fuint 32) instruction) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_8249_checked|apply H83;lia| |apply Steps;lia].
  cbn [adapt_hvalue_as_type]. assert (Take : take 32 instruction = instruction). { apply take_oversize. rewrite Size. reflexivity. }
  rewrite Take. unfold zext_to, zext. rewrite Size subnn cats0. reflexivity.
 }
 assert (H8359 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8359 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8359,address_expr_8359) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 245%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8359 address_expr_8359 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8359 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8360 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8360 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 0%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8360,address_expr_8360) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 246%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8360 address_expr_8360 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8360 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8359 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8357 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8357 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8357,address_expr_8357) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 243%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8357 address_expr_8357 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8357 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8358 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8358 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 1%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8358,address_expr_8358) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 244%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8358 address_expr_8358 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8358 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8357 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8355 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8355 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8355,address_expr_8355) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 241%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8355 address_expr_8355 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8355 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8356 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8356 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 2%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8356,address_expr_8356) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 242%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8356 address_expr_8356 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8356 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8355 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8353 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8353 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8353,address_expr_8353) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 239%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8353 address_expr_8353 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8353 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8354 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8354 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 3%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8354,address_expr_8354) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 240%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8354 address_expr_8354 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8354 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8353 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8351 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8351 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8351,address_expr_8351) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 237%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8351 address_expr_8351 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8351 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8352 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8352 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 4%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8352,address_expr_8352) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 238%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8352 address_expr_8352 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8352 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8351 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8349 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8349 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8349,address_expr_8349) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 235%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8349 address_expr_8349 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8349 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8350 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8350 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 5%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8350,address_expr_8350) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 236%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8350 address_expr_8350 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8350 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8349 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8347 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8347 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8347,address_expr_8347) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 233%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8347 address_expr_8347 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8347 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8348 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8348 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 6%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8348,address_expr_8348) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 234%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8348 address_expr_8348 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8348 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8347 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8345 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8345 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8345,address_expr_8345) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 231%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8345 address_expr_8345 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8345 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8346 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8346 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 7%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8346,address_expr_8346) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 232%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8346 address_expr_8346 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8346 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8345 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8343 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8343 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8343,address_expr_8343) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 229%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8343 address_expr_8343 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8343 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8344 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8344 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 8%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8344,address_expr_8344) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 230%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8344 address_expr_8344 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8344 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8343 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8341 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8341 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8341,address_expr_8341) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 227%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8341 address_expr_8341 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8341 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8342 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8342 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 9%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8342,address_expr_8342) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 228%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8342 address_expr_8342 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8342 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8341 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8339 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8339 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8339,address_expr_8339) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 225%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8339 address_expr_8339 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8339 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8340 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8340 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 10%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8340,address_expr_8340) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 226%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8340 address_expr_8340 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8340 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8339 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8337 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8337 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;true;false;false;false;false;false;false;false;false;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8337,address_expr_8337) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 223%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8337 address_expr_8337 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8337 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8338 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8338 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 11%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8338,address_expr_8338) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 224%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8338 address_expr_8338 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8338 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8337 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8335 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8335 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8335,address_expr_8335) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 221%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8335 address_expr_8335 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8335 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8336 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8336 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 12%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8336,address_expr_8336) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 222%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8336 address_expr_8336 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8336 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8335 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8333 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8333 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8333,address_expr_8333) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 219%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8333 address_expr_8333 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8333 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8334 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8334 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 13%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8334,address_expr_8334) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 220%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8334 address_expr_8334 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8334 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8333 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8331 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8331 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8331,address_expr_8331) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 217%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8331 address_expr_8331 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8331 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8332 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8332 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 14%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8332,address_expr_8332) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 218%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8332 address_expr_8332 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8332 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8331 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8329 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8329 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8329,address_expr_8329) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 215%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8329 address_expr_8329 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8329 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8330 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8330 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 15%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8330,address_expr_8330) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 216%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8330 address_expr_8330 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8330 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8329 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8327 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8327 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8327,address_expr_8327) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 213%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8327 address_expr_8327 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8327 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8328 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8328 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 16%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8328,address_expr_8328) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 214%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8328 address_expr_8328 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8328 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8327 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8325 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8325 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8325,address_expr_8325) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 211%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8325 address_expr_8325 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8325 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8326 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8326 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 17%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8326,address_expr_8326) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 212%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8326 address_expr_8326 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8326 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8325 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8323 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8323 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8323,address_expr_8323) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 209%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8323 address_expr_8323 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8323 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8324 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8324 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 18%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8324,address_expr_8324) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 210%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8324 address_expr_8324 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8324 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8323 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8321 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8321 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8321,address_expr_8321) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 207%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8321 address_expr_8321 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8321 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8322 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8322 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 19%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8322,address_expr_8322) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 208%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8322 address_expr_8322 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8322 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8321 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8319 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8319 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8319,address_expr_8319) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 205%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8319 address_expr_8319 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8319 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8320 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8320 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 20%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8320,address_expr_8320) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 206%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8320 address_expr_8320 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8320 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8319 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8317 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8317 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8317,address_expr_8317) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 203%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8317 address_expr_8317 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8317 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8318 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8318 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 21%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8318,address_expr_8318) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 204%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8318 address_expr_8318 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8318 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8317 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8315 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8315 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8315,address_expr_8315) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 201%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8315 address_expr_8315 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8315 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8316 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8316 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 22%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8316,address_expr_8316) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 202%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8316 address_expr_8316 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8316 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8315 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8313 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8313 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8313,address_expr_8313) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 199%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8313 address_expr_8313 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8313 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8314 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8314 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 23%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8314,address_expr_8314) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 200%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8314 address_expr_8314 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8314 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8313 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8311 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8311 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true;false;false;false;false;false;false;false;false;false;false;true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8311,address_expr_8311) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 197%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8311 address_expr_8311 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8311 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8312 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8312 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 24%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8312,address_expr_8312) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 198%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8312 address_expr_8312 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8312 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8311 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8309 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8309 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8309,address_expr_8309) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 195%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8309 address_expr_8309 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8309 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8310 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8310 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 25%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8310,address_expr_8310) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 196%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8310 address_expr_8310 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8310 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8309 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8307 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8307 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8307,address_expr_8307) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 193%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8307 address_expr_8307 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8307 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8308 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8308 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 26%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8308,address_expr_8308) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 194%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8308 address_expr_8308 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8308 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8307 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8305 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8305 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8305,address_expr_8305) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 191%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8305 address_expr_8305 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8305 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8306 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8306 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 27%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8306,address_expr_8306) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 192%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8306 address_expr_8306 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8306 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8305 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8303 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8303 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8303,address_expr_8303) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 189%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8303 address_expr_8303 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8303 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8304 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8304 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 28%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8304,address_expr_8304) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 190%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8304 address_expr_8304 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8304 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8303 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8301 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8301 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8301,address_expr_8301) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 187%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8301 address_expr_8301 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8301 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8302 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8302 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 29%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8302,address_expr_8302) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 188%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8302 address_expr_8302 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8302 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8301 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8299 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8299 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8299,address_expr_8299) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 185%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8299 address_expr_8299 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8299 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8300 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8300 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 30%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8300,address_expr_8300) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 186%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8300 address_expr_8300 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8300 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8299 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8297 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8297 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8297,address_expr_8297) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 183%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8297 address_expr_8297 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8297 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8298 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8298 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 31%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8298,address_expr_8298) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 184%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8298 address_expr_8298 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8298 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8297 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8295 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8295 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8295,address_expr_8295) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 181%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8295 address_expr_8295 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8295 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8296 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8296 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 32%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8296,address_expr_8296) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 182%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8296 address_expr_8296 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8296 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8295 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8293 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8293 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8293,address_expr_8293) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 179%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8293 address_expr_8293 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8293 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8294 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8294 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 33%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8294,address_expr_8294) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 180%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8294 address_expr_8294 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8294 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8293 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8291 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8291 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8291,address_expr_8291) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 177%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8291 address_expr_8291 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8291 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8292 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8292 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 34%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8292,address_expr_8292) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 178%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8292 address_expr_8292 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8292 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8291 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8289 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8289 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8289,address_expr_8289) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 175%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8289 address_expr_8289 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8289 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8290 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8290 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 35%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8290,address_expr_8290) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 176%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8290 address_expr_8290 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8290 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8289 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8287 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8287 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8287,address_expr_8287) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 173%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8287 address_expr_8287 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8287 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8288 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8288 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 36%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8288,address_expr_8288) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 174%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8288 address_expr_8288 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8288 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8287 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8285 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8285 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8285,address_expr_8285) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 171%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8285 address_expr_8285 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8285 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8286 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8286 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 37%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8286,address_expr_8286) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 172%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8286 address_expr_8286 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8286 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8285 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8283 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8283 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8283,address_expr_8283) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 169%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8283 address_expr_8283 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8283 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8284 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8284 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 38%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8284,address_expr_8284) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 170%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8284 address_expr_8284 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8284 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8283 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8281 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8281 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8281,address_expr_8281) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 167%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8281 address_expr_8281 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8281 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8282 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8282 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 39%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8282,address_expr_8282) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 168%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8282 address_expr_8282 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8282 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8281 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8279 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8279 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8279,address_expr_8279) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 165%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8279 address_expr_8279 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8279 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8280 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8280 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 40%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8280,address_expr_8280) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 166%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8280 address_expr_8280 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8280 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8279 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8277 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8277 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8277,address_expr_8277) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 163%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8277 address_expr_8277 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8277 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8278 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8278 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 41%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8278,address_expr_8278) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 164%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8278 address_expr_8278 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8278 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8277 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8275 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8275 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8275,address_expr_8275) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 161%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8275 address_expr_8275 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8275 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8276 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8276 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 42%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8276,address_expr_8276) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 162%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8276 address_expr_8276 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8276 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8275 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8273 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8273 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8273,address_expr_8273) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 159%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8273 address_expr_8273 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8273 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8274 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8274 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 43%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8274,address_expr_8274) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 160%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8274 address_expr_8274 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8274 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8273 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8271 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8271 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8271,address_expr_8271) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 157%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8271 address_expr_8271 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8271 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8272 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8272 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 44%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8272,address_expr_8272) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 158%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8272 address_expr_8272 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8272 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8271 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8269 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8269 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true;false;false;false;false;false;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8269,address_expr_8269) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 155%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8269 address_expr_8269 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8269 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8270 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8270 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 45%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8270,address_expr_8270) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 156%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8270 address_expr_8270 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8270 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8269 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8267 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8267 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8267,address_expr_8267) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 153%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8267 address_expr_8267 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8267 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8268 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8268 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 46%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8268,address_expr_8268) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 154%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8268 address_expr_8268 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8268 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8267 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8265 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8265 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8265,address_expr_8265) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 151%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8265 address_expr_8265 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8265 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8266 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8266 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 47%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8266,address_expr_8266) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 152%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8266 address_expr_8266 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8266 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8265 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8263 : forall time, (3 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8263 (history time) = Some (Gval (Fuint 32) (andB instruction [::true;true;true;true;true;true;true]))).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8263,address_expr_8263) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 149%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8263 address_expr_8263 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8263 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8249 time ltac:(lia) ltac:(lia)).
  apply wbkill_and_value.
 }
 assert (H8264 : forall time, (4 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8264 (history time) = Some (Gval (Fuint 1) [::wbkill_choice instruction (nth wbkill_default_row wbkill_rows 48%nat)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8264,address_expr_8264) data_address_expected_nodes).
  { apply (List.nth_error_In data_address_expected_nodes 150%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes 8264 address_expr_8264 data_address_actual_node_expressions data_address_actual_nodes_safe Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [address_expr_8264 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8263 time ltac:(lia) ltac:(lia)).
  apply wbkill_eq_value.
 }
 assert (H8655 : forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8655 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 1%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8655,joint_update_expr_8655) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1144%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8655 joint_update_expr_8655 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8655 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8360 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 1%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 0%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 0%nat) else wbkill_decode 0%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 0%nat)); reflexivity.
 }
 assert (H8802 : forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8802 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 1%nat instruction);wbkill_high (wbkill_decode 1%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8802,joint_update_expr_8802) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1193%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8802 joint_update_expr_8802 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8802 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8360 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 1%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 0%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 0%nat) else wbkill_decode 0%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 0%nat)); reflexivity.
 }
 assert (H8851 : forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8851 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 1%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8851,joint_update_expr_8851) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1242%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8851 joint_update_expr_8851 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8851 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8360 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 1%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 0%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 0%nat) else wbkill_decode 0%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 0%nat)); reflexivity.
 }
 assert (H8656 : forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8656 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 2%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8656,joint_update_expr_8656) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1145%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8656 joint_update_expr_8656 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8656 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8358 time ltac:(lia) ltac:(lia)).
  rewrite (H8655 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 2%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 1%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 1%nat) else wbkill_decode 1%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 1%nat)); reflexivity.
 }
 assert (H8803 : forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8803 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 2%nat instruction);wbkill_high (wbkill_decode 2%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8803,joint_update_expr_8803) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1194%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8803 joint_update_expr_8803 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8803 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8358 time ltac:(lia) ltac:(lia)).
  rewrite (H8802 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 2%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 1%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 1%nat) else wbkill_decode 1%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 1%nat)); reflexivity.
 }
 assert (H8852 : forall time, (6 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8852 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 2%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8852,joint_update_expr_8852) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1243%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8852 joint_update_expr_8852 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8852 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8358 time ltac:(lia) ltac:(lia)).
  rewrite (H8851 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 2%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 1%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 1%nat) else wbkill_decode 1%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 1%nat)); reflexivity.
 }
 assert (H8657 : forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8657 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 3%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8657,joint_update_expr_8657) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1146%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8657 joint_update_expr_8657 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8657 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8356 time ltac:(lia) ltac:(lia)).
  rewrite (H8656 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 3%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 2%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 2%nat) else wbkill_decode 2%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 2%nat)); reflexivity.
 }
 assert (H8804 : forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8804 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 3%nat instruction);wbkill_high (wbkill_decode 3%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8804,joint_update_expr_8804) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1195%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8804 joint_update_expr_8804 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8804 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8356 time ltac:(lia) ltac:(lia)).
  rewrite (H8803 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 3%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 2%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 2%nat) else wbkill_decode 2%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 2%nat)); reflexivity.
 }
 assert (H8853 : forall time, (7 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8853 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 3%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8853,joint_update_expr_8853) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1244%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8853 joint_update_expr_8853 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8853 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8356 time ltac:(lia) ltac:(lia)).
  rewrite (H8852 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 3%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 2%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 2%nat) else wbkill_decode 2%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 2%nat)); reflexivity.
 }
 assert (H8658 : forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8658 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 4%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8658,joint_update_expr_8658) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1147%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8658 joint_update_expr_8658 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8658 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8354 time ltac:(lia) ltac:(lia)).
  rewrite (H8657 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 4%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 3%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 3%nat) else wbkill_decode 3%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 3%nat)); reflexivity.
 }
 assert (H8805 : forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8805 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 4%nat instruction);wbkill_high (wbkill_decode 4%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8805,joint_update_expr_8805) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1196%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8805 joint_update_expr_8805 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8805 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8354 time ltac:(lia) ltac:(lia)).
  rewrite (H8804 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 4%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 3%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 3%nat) else wbkill_decode 3%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 3%nat)); reflexivity.
 }
 assert (H8854 : forall time, (8 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8854 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 4%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8854,joint_update_expr_8854) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1245%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8854 joint_update_expr_8854 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8854 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8354 time ltac:(lia) ltac:(lia)).
  rewrite (H8853 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 4%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 3%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 3%nat) else wbkill_decode 3%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 3%nat)); reflexivity.
 }
 assert (H8659 : forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8659 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 5%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8659,joint_update_expr_8659) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1148%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8659 joint_update_expr_8659 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8659 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8352 time ltac:(lia) ltac:(lia)).
  rewrite (H8658 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 5%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 4%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 4%nat) else wbkill_decode 4%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 4%nat)); reflexivity.
 }
 assert (H8806 : forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8806 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 5%nat instruction);wbkill_high (wbkill_decode 5%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8806,joint_update_expr_8806) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1197%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8806 joint_update_expr_8806 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8806 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8352 time ltac:(lia) ltac:(lia)).
  rewrite (H8805 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 5%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 4%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 4%nat) else wbkill_decode 4%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 4%nat)); reflexivity.
 }
 assert (H8855 : forall time, (9 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8855 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 5%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8855,joint_update_expr_8855) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1246%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8855 joint_update_expr_8855 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8855 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8352 time ltac:(lia) ltac:(lia)).
  rewrite (H8854 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 5%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 4%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 4%nat) else wbkill_decode 4%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 4%nat)); reflexivity.
 }
 assert (H8660 : forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8660 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 6%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8660,joint_update_expr_8660) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1149%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8660 joint_update_expr_8660 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8660 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8350 time ltac:(lia) ltac:(lia)).
  rewrite (H8659 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 6%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 5%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 5%nat) else wbkill_decode 5%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 5%nat)); reflexivity.
 }
 assert (H8807 : forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8807 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 6%nat instruction);wbkill_high (wbkill_decode 6%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8807,joint_update_expr_8807) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1198%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8807 joint_update_expr_8807 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8807 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8350 time ltac:(lia) ltac:(lia)).
  rewrite (H8806 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 6%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 5%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 5%nat) else wbkill_decode 5%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 5%nat)); reflexivity.
 }
 assert (H8856 : forall time, (10 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8856 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 6%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8856,joint_update_expr_8856) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1247%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8856 joint_update_expr_8856 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8856 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8350 time ltac:(lia) ltac:(lia)).
  rewrite (H8855 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 6%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 5%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 5%nat) else wbkill_decode 5%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 5%nat)); reflexivity.
 }
 assert (H8661 : forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8661 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 7%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8661,joint_update_expr_8661) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1150%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8661 joint_update_expr_8661 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8661 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8348 time ltac:(lia) ltac:(lia)).
  rewrite (H8660 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 7%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 6%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 6%nat) else wbkill_decode 6%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 6%nat)); reflexivity.
 }
 assert (H8808 : forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8808 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 7%nat instruction);wbkill_high (wbkill_decode 7%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8808,joint_update_expr_8808) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1199%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8808 joint_update_expr_8808 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8808 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8348 time ltac:(lia) ltac:(lia)).
  rewrite (H8807 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 7%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 6%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 6%nat) else wbkill_decode 6%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 6%nat)); reflexivity.
 }
 assert (H8857 : forall time, (11 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8857 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 7%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8857,joint_update_expr_8857) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1248%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8857 joint_update_expr_8857 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8857 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8348 time ltac:(lia) ltac:(lia)).
  rewrite (H8856 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 7%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 6%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 6%nat) else wbkill_decode 6%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 6%nat)); reflexivity.
 }
 assert (H8662 : forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8662 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 8%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8662,joint_update_expr_8662) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1151%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8662 joint_update_expr_8662 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8662 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8346 time ltac:(lia) ltac:(lia)).
  rewrite (H8661 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 8%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 7%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 7%nat) else wbkill_decode 7%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 7%nat)); reflexivity.
 }
 assert (H8809 : forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8809 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 8%nat instruction);wbkill_high (wbkill_decode 8%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8809,joint_update_expr_8809) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1200%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8809 joint_update_expr_8809 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8809 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8346 time ltac:(lia) ltac:(lia)).
  rewrite (H8808 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 8%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 7%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 7%nat) else wbkill_decode 7%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 7%nat)); reflexivity.
 }
 assert (H8858 : forall time, (12 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8858 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 8%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8858,joint_update_expr_8858) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1249%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8858 joint_update_expr_8858 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8858 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8346 time ltac:(lia) ltac:(lia)).
  rewrite (H8857 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 8%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 7%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 7%nat) else wbkill_decode 7%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 7%nat)); reflexivity.
 }
 assert (H8663 : forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8663 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 9%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8663,joint_update_expr_8663) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1152%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8663 joint_update_expr_8663 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8663 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8344 time ltac:(lia) ltac:(lia)).
  rewrite (H8662 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 9%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 8%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 8%nat) else wbkill_decode 8%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 8%nat)); reflexivity.
 }
 assert (H8810 : forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8810 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 9%nat instruction);wbkill_high (wbkill_decode 9%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8810,joint_update_expr_8810) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1201%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8810 joint_update_expr_8810 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8810 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8344 time ltac:(lia) ltac:(lia)).
  rewrite (H8809 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 9%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 8%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 8%nat) else wbkill_decode 8%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 8%nat)); reflexivity.
 }
 assert (H8859 : forall time, (13 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8859 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 9%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8859,joint_update_expr_8859) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1250%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8859 joint_update_expr_8859 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8859 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8344 time ltac:(lia) ltac:(lia)).
  rewrite (H8858 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 9%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 8%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 8%nat) else wbkill_decode 8%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 8%nat)); reflexivity.
 }
 assert (H8664 : forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8664 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 10%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8664,joint_update_expr_8664) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1153%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8664 joint_update_expr_8664 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8664 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8342 time ltac:(lia) ltac:(lia)).
  rewrite (H8663 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 10%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 9%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 9%nat) else wbkill_decode 9%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 9%nat)); reflexivity.
 }
 assert (H8811 : forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8811 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 10%nat instruction);wbkill_high (wbkill_decode 10%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8811,joint_update_expr_8811) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1202%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8811 joint_update_expr_8811 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8811 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8342 time ltac:(lia) ltac:(lia)).
  rewrite (H8810 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 10%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 9%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 9%nat) else wbkill_decode 9%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 9%nat)); reflexivity.
 }
 assert (H8860 : forall time, (14 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8860 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 10%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8860,joint_update_expr_8860) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1251%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8860 joint_update_expr_8860 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8860 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8342 time ltac:(lia) ltac:(lia)).
  rewrite (H8859 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 10%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 9%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 9%nat) else wbkill_decode 9%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 9%nat)); reflexivity.
 }
 assert (H8665 : forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8665 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 11%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8665,joint_update_expr_8665) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1154%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8665 joint_update_expr_8665 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8665 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8340 time ltac:(lia) ltac:(lia)).
  rewrite (H8664 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 11%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 10%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 10%nat) else wbkill_decode 10%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 10%nat)); reflexivity.
 }
 assert (H8812 : forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8812 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 11%nat instruction);wbkill_high (wbkill_decode 11%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8812,joint_update_expr_8812) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1203%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8812 joint_update_expr_8812 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8812 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8340 time ltac:(lia) ltac:(lia)).
  rewrite (H8811 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 11%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 10%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 10%nat) else wbkill_decode 10%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 10%nat)); reflexivity.
 }
 assert (H8861 : forall time, (15 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8861 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 11%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8861,joint_update_expr_8861) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1252%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8861 joint_update_expr_8861 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8861 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8340 time ltac:(lia) ltac:(lia)).
  rewrite (H8860 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 11%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 10%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 10%nat) else wbkill_decode 10%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 10%nat)); reflexivity.
 }
 assert (H8666 : forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8666 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 12%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8666,joint_update_expr_8666) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1155%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8666 joint_update_expr_8666 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8666 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8338 time ltac:(lia) ltac:(lia)).
  rewrite (H8665 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 12%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 11%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 11%nat) else wbkill_decode 11%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 11%nat)); reflexivity.
 }
 assert (H8813 : forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8813 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 12%nat instruction);wbkill_high (wbkill_decode 12%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8813,joint_update_expr_8813) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1204%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8813 joint_update_expr_8813 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8813 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8338 time ltac:(lia) ltac:(lia)).
  rewrite (H8812 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 12%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 11%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 11%nat) else wbkill_decode 11%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 11%nat)); reflexivity.
 }
 assert (H8862 : forall time, (16 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8862 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 12%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8862,joint_update_expr_8862) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1253%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8862 joint_update_expr_8862 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8862 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8338 time ltac:(lia) ltac:(lia)).
  rewrite (H8861 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 12%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 11%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 11%nat) else wbkill_decode 11%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 11%nat)); reflexivity.
 }
 assert (H8667 : forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8667 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 13%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8667,joint_update_expr_8667) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1156%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8667 joint_update_expr_8667 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8667 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8336 time ltac:(lia) ltac:(lia)).
  rewrite (H8666 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 13%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 12%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 12%nat) else wbkill_decode 12%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 12%nat)); reflexivity.
 }
 assert (H8814 : forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8814 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 13%nat instruction);wbkill_high (wbkill_decode 13%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8814,joint_update_expr_8814) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1205%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8814 joint_update_expr_8814 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8814 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8336 time ltac:(lia) ltac:(lia)).
  rewrite (H8813 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 13%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 12%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 12%nat) else wbkill_decode 12%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 12%nat)); reflexivity.
 }
 assert (H8863 : forall time, (17 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8863 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 13%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8863,joint_update_expr_8863) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1254%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8863 joint_update_expr_8863 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8863 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8336 time ltac:(lia) ltac:(lia)).
  rewrite (H8862 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 13%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 12%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 12%nat) else wbkill_decode 12%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 12%nat)); reflexivity.
 }
 assert (H8668 : forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8668 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 14%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8668,joint_update_expr_8668) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1157%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8668 joint_update_expr_8668 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8668 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8334 time ltac:(lia) ltac:(lia)).
  rewrite (H8667 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 14%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 13%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 13%nat) else wbkill_decode 13%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 13%nat)); reflexivity.
 }
 assert (H8815 : forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8815 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 14%nat instruction);wbkill_high (wbkill_decode 14%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8815,joint_update_expr_8815) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1206%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8815 joint_update_expr_8815 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8815 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8334 time ltac:(lia) ltac:(lia)).
  rewrite (H8814 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 14%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 13%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 13%nat) else wbkill_decode 13%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 13%nat)); reflexivity.
 }
 assert (H8864 : forall time, (18 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8864 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 14%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8864,joint_update_expr_8864) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1255%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8864 joint_update_expr_8864 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8864 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8334 time ltac:(lia) ltac:(lia)).
  rewrite (H8863 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 14%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 13%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 13%nat) else wbkill_decode 13%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 13%nat)); reflexivity.
 }
 assert (H8669 : forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8669 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 15%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8669,joint_update_expr_8669) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1158%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8669 joint_update_expr_8669 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8669 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8332 time ltac:(lia) ltac:(lia)).
  rewrite (H8668 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 15%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 14%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 14%nat) else wbkill_decode 14%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 14%nat)); reflexivity.
 }
 assert (H8816 : forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8816 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 15%nat instruction);wbkill_high (wbkill_decode 15%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8816,joint_update_expr_8816) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1207%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8816 joint_update_expr_8816 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8816 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8332 time ltac:(lia) ltac:(lia)).
  rewrite (H8815 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 15%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 14%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 14%nat) else wbkill_decode 14%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 14%nat)); reflexivity.
 }
 assert (H8865 : forall time, (19 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8865 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 15%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8865,joint_update_expr_8865) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1256%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8865 joint_update_expr_8865 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8865 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8332 time ltac:(lia) ltac:(lia)).
  rewrite (H8864 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 15%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 14%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 14%nat) else wbkill_decode 14%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 14%nat)); reflexivity.
 }
 assert (H8670 : forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8670 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 16%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8670,joint_update_expr_8670) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1159%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8670 joint_update_expr_8670 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8670 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8330 time ltac:(lia) ltac:(lia)).
  rewrite (H8669 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 16%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 15%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 15%nat) else wbkill_decode 15%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 15%nat)); reflexivity.
 }
 assert (H8817 : forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8817 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 16%nat instruction);wbkill_high (wbkill_decode 16%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8817,joint_update_expr_8817) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1208%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8817 joint_update_expr_8817 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8817 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8330 time ltac:(lia) ltac:(lia)).
  rewrite (H8816 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 16%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 15%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 15%nat) else wbkill_decode 15%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 15%nat)); reflexivity.
 }
 assert (H8866 : forall time, (20 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8866 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 16%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8866,joint_update_expr_8866) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1257%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8866 joint_update_expr_8866 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8866 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8330 time ltac:(lia) ltac:(lia)).
  rewrite (H8865 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 16%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 15%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 15%nat) else wbkill_decode 15%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 15%nat)); reflexivity.
 }
 assert (H8671 : forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8671 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 17%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8671,joint_update_expr_8671) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1160%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8671 joint_update_expr_8671 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8671 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8328 time ltac:(lia) ltac:(lia)).
  rewrite (H8670 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 17%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 16%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 16%nat) else wbkill_decode 16%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 16%nat)); reflexivity.
 }
 assert (H8818 : forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8818 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 17%nat instruction);wbkill_high (wbkill_decode 17%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8818,joint_update_expr_8818) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1209%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8818 joint_update_expr_8818 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8818 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8328 time ltac:(lia) ltac:(lia)).
  rewrite (H8817 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 17%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 16%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 16%nat) else wbkill_decode 16%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 16%nat)); reflexivity.
 }
 assert (H8867 : forall time, (21 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8867 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 17%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8867,joint_update_expr_8867) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1258%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8867 joint_update_expr_8867 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8867 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8328 time ltac:(lia) ltac:(lia)).
  rewrite (H8866 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 17%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 16%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 16%nat) else wbkill_decode 16%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 16%nat)); reflexivity.
 }
 assert (H8672 : forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8672 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 18%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8672,joint_update_expr_8672) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1161%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8672 joint_update_expr_8672 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8672 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8326 time ltac:(lia) ltac:(lia)).
  rewrite (H8671 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 18%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 17%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 17%nat) else wbkill_decode 17%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 17%nat)); reflexivity.
 }
 assert (H8819 : forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8819 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 18%nat instruction);wbkill_high (wbkill_decode 18%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8819,joint_update_expr_8819) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1210%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8819 joint_update_expr_8819 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8819 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8326 time ltac:(lia) ltac:(lia)).
  rewrite (H8818 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 18%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 17%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 17%nat) else wbkill_decode 17%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 17%nat)); reflexivity.
 }
 assert (H8868 : forall time, (22 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8868 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 18%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8868,joint_update_expr_8868) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1259%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8868 joint_update_expr_8868 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8868 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8326 time ltac:(lia) ltac:(lia)).
  rewrite (H8867 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 18%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 17%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 17%nat) else wbkill_decode 17%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 17%nat)); reflexivity.
 }
 assert (H8673 : forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8673 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 19%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8673,joint_update_expr_8673) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1162%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8673 joint_update_expr_8673 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8673 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8324 time ltac:(lia) ltac:(lia)).
  rewrite (H8672 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 19%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 18%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 18%nat) else wbkill_decode 18%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 18%nat)); reflexivity.
 }
 assert (H8820 : forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8820 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 19%nat instruction);wbkill_high (wbkill_decode 19%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8820,joint_update_expr_8820) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1211%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8820 joint_update_expr_8820 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8820 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8324 time ltac:(lia) ltac:(lia)).
  rewrite (H8819 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 19%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 18%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 18%nat) else wbkill_decode 18%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 18%nat)); reflexivity.
 }
 assert (H8869 : forall time, (23 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8869 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 19%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8869,joint_update_expr_8869) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1260%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8869 joint_update_expr_8869 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8869 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8324 time ltac:(lia) ltac:(lia)).
  rewrite (H8868 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 19%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 18%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 18%nat) else wbkill_decode 18%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 18%nat)); reflexivity.
 }
 assert (H8674 : forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8674 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 20%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8674,joint_update_expr_8674) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1163%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8674 joint_update_expr_8674 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8674 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8322 time ltac:(lia) ltac:(lia)).
  rewrite (H8673 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 20%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 19%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 19%nat) else wbkill_decode 19%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 19%nat)); reflexivity.
 }
 assert (H8821 : forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8821 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 20%nat instruction);wbkill_high (wbkill_decode 20%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8821,joint_update_expr_8821) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1212%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8821 joint_update_expr_8821 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8821 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8322 time ltac:(lia) ltac:(lia)).
  rewrite (H8820 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 20%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 19%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 19%nat) else wbkill_decode 19%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 19%nat)); reflexivity.
 }
 assert (H8870 : forall time, (24 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8870 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 20%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8870,joint_update_expr_8870) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1261%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8870 joint_update_expr_8870 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8870 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8322 time ltac:(lia) ltac:(lia)).
  rewrite (H8869 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 20%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 19%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 19%nat) else wbkill_decode 19%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 19%nat)); reflexivity.
 }
 assert (H8675 : forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8675 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 21%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8675,joint_update_expr_8675) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1164%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8675 joint_update_expr_8675 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8675 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8320 time ltac:(lia) ltac:(lia)).
  rewrite (H8674 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 21%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 20%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 20%nat) else wbkill_decode 20%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 20%nat)); reflexivity.
 }
 assert (H8822 : forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8822 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 21%nat instruction);wbkill_high (wbkill_decode 21%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8822,joint_update_expr_8822) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1213%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8822 joint_update_expr_8822 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8822 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8320 time ltac:(lia) ltac:(lia)).
  rewrite (H8821 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 21%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 20%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 20%nat) else wbkill_decode 20%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 20%nat)); reflexivity.
 }
 assert (H8871 : forall time, (25 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8871 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 21%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8871,joint_update_expr_8871) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1262%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8871 joint_update_expr_8871 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8871 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8320 time ltac:(lia) ltac:(lia)).
  rewrite (H8870 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 21%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 20%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 20%nat) else wbkill_decode 20%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 20%nat)); reflexivity.
 }
 assert (H8676 : forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8676 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 22%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8676,joint_update_expr_8676) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1165%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8676 joint_update_expr_8676 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8676 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8318 time ltac:(lia) ltac:(lia)).
  rewrite (H8675 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 22%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 21%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 21%nat) else wbkill_decode 21%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 21%nat)); reflexivity.
 }
 assert (H8823 : forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8823 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 22%nat instruction);wbkill_high (wbkill_decode 22%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8823,joint_update_expr_8823) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1214%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8823 joint_update_expr_8823 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8823 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8318 time ltac:(lia) ltac:(lia)).
  rewrite (H8822 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 22%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 21%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 21%nat) else wbkill_decode 21%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 21%nat)); reflexivity.
 }
 assert (H8872 : forall time, (26 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8872 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 22%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8872,joint_update_expr_8872) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1263%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8872 joint_update_expr_8872 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8872 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8318 time ltac:(lia) ltac:(lia)).
  rewrite (H8871 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 22%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 21%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 21%nat) else wbkill_decode 21%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 21%nat)); reflexivity.
 }
 assert (H8677 : forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8677 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 23%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8677,joint_update_expr_8677) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1166%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8677 joint_update_expr_8677 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8677 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8316 time ltac:(lia) ltac:(lia)).
  rewrite (H8676 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 23%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 22%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 22%nat) else wbkill_decode 22%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 22%nat)); reflexivity.
 }
 assert (H8824 : forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8824 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 23%nat instruction);wbkill_high (wbkill_decode 23%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8824,joint_update_expr_8824) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1215%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8824 joint_update_expr_8824 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8824 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8316 time ltac:(lia) ltac:(lia)).
  rewrite (H8823 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 23%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 22%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 22%nat) else wbkill_decode 22%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 22%nat)); reflexivity.
 }
 assert (H8873 : forall time, (27 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8873 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 23%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8873,joint_update_expr_8873) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1264%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8873 joint_update_expr_8873 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8873 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8316 time ltac:(lia) ltac:(lia)).
  rewrite (H8872 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 23%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 22%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 22%nat) else wbkill_decode 22%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 22%nat)); reflexivity.
 }
 assert (H8678 : forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8678 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 24%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8678,joint_update_expr_8678) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1167%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8678 joint_update_expr_8678 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8678 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8314 time ltac:(lia) ltac:(lia)).
  rewrite (H8677 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 24%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 23%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 23%nat) else wbkill_decode 23%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 23%nat)); reflexivity.
 }
 assert (H8825 : forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8825 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 24%nat instruction);wbkill_high (wbkill_decode 24%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8825,joint_update_expr_8825) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1216%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8825 joint_update_expr_8825 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8825 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8314 time ltac:(lia) ltac:(lia)).
  rewrite (H8824 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 24%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 23%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 23%nat) else wbkill_decode 23%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 23%nat)); reflexivity.
 }
 assert (H8874 : forall time, (28 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8874 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 24%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8874,joint_update_expr_8874) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1265%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8874 joint_update_expr_8874 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8874 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8314 time ltac:(lia) ltac:(lia)).
  rewrite (H8873 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 24%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 23%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 23%nat) else wbkill_decode 23%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 23%nat)); reflexivity.
 }
 assert (H8679 : forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8679 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 25%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8679,joint_update_expr_8679) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1168%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8679 joint_update_expr_8679 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8679 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8312 time ltac:(lia) ltac:(lia)).
  rewrite (H8678 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 25%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 24%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 24%nat) else wbkill_decode 24%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 24%nat)); reflexivity.
 }
 assert (H8826 : forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8826 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 25%nat instruction);wbkill_high (wbkill_decode 25%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8826,joint_update_expr_8826) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1217%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8826 joint_update_expr_8826 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8826 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8312 time ltac:(lia) ltac:(lia)).
  rewrite (H8825 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 25%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 24%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 24%nat) else wbkill_decode 24%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 24%nat)); reflexivity.
 }
 assert (H8875 : forall time, (29 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8875 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 25%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8875,joint_update_expr_8875) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1266%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8875 joint_update_expr_8875 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8875 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8312 time ltac:(lia) ltac:(lia)).
  rewrite (H8874 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 25%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 24%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 24%nat) else wbkill_decode 24%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 24%nat)); reflexivity.
 }
 assert (H8680 : forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8680 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 26%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8680,joint_update_expr_8680) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1169%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8680 joint_update_expr_8680 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8680 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8310 time ltac:(lia) ltac:(lia)).
  rewrite (H8679 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 26%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 25%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 25%nat) else wbkill_decode 25%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 25%nat)); reflexivity.
 }
 assert (H8827 : forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8827 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 26%nat instruction);wbkill_high (wbkill_decode 26%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8827,joint_update_expr_8827) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1218%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8827 joint_update_expr_8827 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8827 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8310 time ltac:(lia) ltac:(lia)).
  rewrite (H8826 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 26%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 25%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 25%nat) else wbkill_decode 25%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 25%nat)); reflexivity.
 }
 assert (H8876 : forall time, (30 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8876 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 26%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8876,joint_update_expr_8876) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1267%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8876 joint_update_expr_8876 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8876 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8310 time ltac:(lia) ltac:(lia)).
  rewrite (H8875 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 26%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 25%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 25%nat) else wbkill_decode 25%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 25%nat)); reflexivity.
 }
 assert (H8681 : forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8681 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 27%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8681,joint_update_expr_8681) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1170%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8681 joint_update_expr_8681 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8681 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8308 time ltac:(lia) ltac:(lia)).
  rewrite (H8680 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 27%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 26%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 26%nat) else wbkill_decode 26%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 26%nat)); reflexivity.
 }
 assert (H8828 : forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8828 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 27%nat instruction);wbkill_high (wbkill_decode 27%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8828,joint_update_expr_8828) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1219%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8828 joint_update_expr_8828 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8828 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8308 time ltac:(lia) ltac:(lia)).
  rewrite (H8827 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 27%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 26%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 26%nat) else wbkill_decode 26%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 26%nat)); reflexivity.
 }
 assert (H8877 : forall time, (31 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8877 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 27%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8877,joint_update_expr_8877) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1268%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8877 joint_update_expr_8877 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8877 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8308 time ltac:(lia) ltac:(lia)).
  rewrite (H8876 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 27%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 26%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 26%nat) else wbkill_decode 26%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 26%nat)); reflexivity.
 }
 assert (H8682 : forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8682 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 28%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8682,joint_update_expr_8682) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1171%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8682 joint_update_expr_8682 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8682 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8306 time ltac:(lia) ltac:(lia)).
  rewrite (H8681 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 28%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 27%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 27%nat) else wbkill_decode 27%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 27%nat)); reflexivity.
 }
 assert (H8829 : forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8829 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 28%nat instruction);wbkill_high (wbkill_decode 28%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8829,joint_update_expr_8829) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1220%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8829 joint_update_expr_8829 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8829 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8306 time ltac:(lia) ltac:(lia)).
  rewrite (H8828 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 28%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 27%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 27%nat) else wbkill_decode 27%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 27%nat)); reflexivity.
 }
 assert (H8878 : forall time, (32 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8878 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 28%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8878,joint_update_expr_8878) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1269%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8878 joint_update_expr_8878 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8878 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8306 time ltac:(lia) ltac:(lia)).
  rewrite (H8877 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 28%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 27%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 27%nat) else wbkill_decode 27%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 27%nat)); reflexivity.
 }
 assert (H8683 : forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8683 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 29%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8683,joint_update_expr_8683) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1172%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8683 joint_update_expr_8683 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8683 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8304 time ltac:(lia) ltac:(lia)).
  rewrite (H8682 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 29%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 28%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 28%nat) else wbkill_decode 28%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 28%nat)); reflexivity.
 }
 assert (H8830 : forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8830 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 29%nat instruction);wbkill_high (wbkill_decode 29%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8830,joint_update_expr_8830) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1221%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8830 joint_update_expr_8830 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8830 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8304 time ltac:(lia) ltac:(lia)).
  rewrite (H8829 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 29%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 28%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 28%nat) else wbkill_decode 28%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 28%nat)); reflexivity.
 }
 assert (H8879 : forall time, (33 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8879 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 29%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8879,joint_update_expr_8879) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1270%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8879 joint_update_expr_8879 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8879 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8304 time ltac:(lia) ltac:(lia)).
  rewrite (H8878 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 29%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 28%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 28%nat) else wbkill_decode 28%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 28%nat)); reflexivity.
 }
 assert (H8684 : forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8684 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 30%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8684,joint_update_expr_8684) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1173%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8684 joint_update_expr_8684 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8684 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8302 time ltac:(lia) ltac:(lia)).
  rewrite (H8683 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 30%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 29%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 29%nat) else wbkill_decode 29%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 29%nat)); reflexivity.
 }
 assert (H8831 : forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8831 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 30%nat instruction);wbkill_high (wbkill_decode 30%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8831,joint_update_expr_8831) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1222%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8831 joint_update_expr_8831 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8831 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8302 time ltac:(lia) ltac:(lia)).
  rewrite (H8830 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 30%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 29%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 29%nat) else wbkill_decode 29%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 29%nat)); reflexivity.
 }
 assert (H8880 : forall time, (34 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8880 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 30%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8880,joint_update_expr_8880) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1271%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8880 joint_update_expr_8880 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8880 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8302 time ltac:(lia) ltac:(lia)).
  rewrite (H8879 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 30%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 29%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 29%nat) else wbkill_decode 29%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 29%nat)); reflexivity.
 }
 assert (H8685 : forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8685 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 31%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8685,joint_update_expr_8685) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1174%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8685 joint_update_expr_8685 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8685 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8300 time ltac:(lia) ltac:(lia)).
  rewrite (H8684 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 31%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 30%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 30%nat) else wbkill_decode 30%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 30%nat)); reflexivity.
 }
 assert (H8832 : forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8832 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 31%nat instruction);wbkill_high (wbkill_decode 31%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8832,joint_update_expr_8832) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1223%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8832 joint_update_expr_8832 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8832 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8300 time ltac:(lia) ltac:(lia)).
  rewrite (H8831 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 31%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 30%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 30%nat) else wbkill_decode 30%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 30%nat)); reflexivity.
 }
 assert (H8881 : forall time, (35 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8881 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 31%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8881,joint_update_expr_8881) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1272%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8881 joint_update_expr_8881 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8881 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8300 time ltac:(lia) ltac:(lia)).
  rewrite (H8880 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 31%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 30%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 30%nat) else wbkill_decode 30%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 30%nat)); reflexivity.
 }
 assert (H8686 : forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8686 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 32%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8686,joint_update_expr_8686) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1175%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8686 joint_update_expr_8686 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8686 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8298 time ltac:(lia) ltac:(lia)).
  rewrite (H8685 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 32%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 31%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 31%nat) else wbkill_decode 31%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 31%nat)); reflexivity.
 }
 assert (H8833 : forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8833 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 32%nat instruction);wbkill_high (wbkill_decode 32%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8833,joint_update_expr_8833) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1224%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8833 joint_update_expr_8833 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8833 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8298 time ltac:(lia) ltac:(lia)).
  rewrite (H8832 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 32%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 31%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 31%nat) else wbkill_decode 31%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 31%nat)); reflexivity.
 }
 assert (H8882 : forall time, (36 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8882 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 32%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8882,joint_update_expr_8882) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1273%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8882 joint_update_expr_8882 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8882 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8298 time ltac:(lia) ltac:(lia)).
  rewrite (H8881 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 32%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 31%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 31%nat) else wbkill_decode 31%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 31%nat)); reflexivity.
 }
 assert (H8687 : forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8687 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 33%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8687,joint_update_expr_8687) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1176%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8687 joint_update_expr_8687 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8687 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8296 time ltac:(lia) ltac:(lia)).
  rewrite (H8686 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 33%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 32%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 32%nat) else wbkill_decode 32%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 32%nat)); reflexivity.
 }
 assert (H8834 : forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8834 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 33%nat instruction);wbkill_high (wbkill_decode 33%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8834,joint_update_expr_8834) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1225%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8834 joint_update_expr_8834 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8834 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8296 time ltac:(lia) ltac:(lia)).
  rewrite (H8833 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 33%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 32%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 32%nat) else wbkill_decode 32%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 32%nat)); reflexivity.
 }
 assert (H8883 : forall time, (37 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8883 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 33%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8883,joint_update_expr_8883) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1274%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8883 joint_update_expr_8883 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8883 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8296 time ltac:(lia) ltac:(lia)).
  rewrite (H8882 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 33%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 32%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 32%nat) else wbkill_decode 32%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 32%nat)); reflexivity.
 }
 assert (H8688 : forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8688 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 34%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8688,joint_update_expr_8688) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1177%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8688 joint_update_expr_8688 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8688 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8294 time ltac:(lia) ltac:(lia)).
  rewrite (H8687 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 34%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 33%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 33%nat) else wbkill_decode 33%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 33%nat)); reflexivity.
 }
 assert (H8835 : forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8835 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 34%nat instruction);wbkill_high (wbkill_decode 34%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8835,joint_update_expr_8835) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1226%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8835 joint_update_expr_8835 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8835 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8294 time ltac:(lia) ltac:(lia)).
  rewrite (H8834 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 34%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 33%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 33%nat) else wbkill_decode 33%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 33%nat)); reflexivity.
 }
 assert (H8884 : forall time, (38 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8884 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 34%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8884,joint_update_expr_8884) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1275%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8884 joint_update_expr_8884 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8884 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8294 time ltac:(lia) ltac:(lia)).
  rewrite (H8883 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 34%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 33%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 33%nat) else wbkill_decode 33%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 33%nat)); reflexivity.
 }
 assert (H8689 : forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8689 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 35%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8689,joint_update_expr_8689) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1178%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8689 joint_update_expr_8689 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8689 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8292 time ltac:(lia) ltac:(lia)).
  rewrite (H8688 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 35%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 34%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 34%nat) else wbkill_decode 34%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 34%nat)); reflexivity.
 }
 assert (H8836 : forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8836 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 35%nat instruction);wbkill_high (wbkill_decode 35%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8836,joint_update_expr_8836) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1227%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8836 joint_update_expr_8836 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8836 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8292 time ltac:(lia) ltac:(lia)).
  rewrite (H8835 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 35%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 34%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 34%nat) else wbkill_decode 34%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 34%nat)); reflexivity.
 }
 assert (H8885 : forall time, (39 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8885 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 35%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8885,joint_update_expr_8885) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1276%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8885 joint_update_expr_8885 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8885 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8292 time ltac:(lia) ltac:(lia)).
  rewrite (H8884 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 35%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 34%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 34%nat) else wbkill_decode 34%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 34%nat)); reflexivity.
 }
 assert (H8690 : forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8690 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 36%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8690,joint_update_expr_8690) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1179%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8690 joint_update_expr_8690 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8690 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8290 time ltac:(lia) ltac:(lia)).
  rewrite (H8689 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 36%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 35%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 35%nat) else wbkill_decode 35%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 35%nat)); reflexivity.
 }
 assert (H8837 : forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8837 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 36%nat instruction);wbkill_high (wbkill_decode 36%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8837,joint_update_expr_8837) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1228%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8837 joint_update_expr_8837 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8837 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8290 time ltac:(lia) ltac:(lia)).
  rewrite (H8836 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 36%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 35%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 35%nat) else wbkill_decode 35%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 35%nat)); reflexivity.
 }
 assert (H8886 : forall time, (40 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8886 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 36%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8886,joint_update_expr_8886) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1277%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8886 joint_update_expr_8886 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8886 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8290 time ltac:(lia) ltac:(lia)).
  rewrite (H8885 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 36%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 35%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 35%nat) else wbkill_decode 35%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 35%nat)); reflexivity.
 }
 assert (H8691 : forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8691 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 37%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8691,joint_update_expr_8691) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1180%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8691 joint_update_expr_8691 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8691 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8288 time ltac:(lia) ltac:(lia)).
  rewrite (H8690 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 37%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 36%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 36%nat) else wbkill_decode 36%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 36%nat)); reflexivity.
 }
 assert (H8838 : forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8838 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 37%nat instruction);wbkill_high (wbkill_decode 37%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8838,joint_update_expr_8838) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1229%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8838 joint_update_expr_8838 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8838 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8288 time ltac:(lia) ltac:(lia)).
  rewrite (H8837 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 37%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 36%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 36%nat) else wbkill_decode 36%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 36%nat)); reflexivity.
 }
 assert (H8887 : forall time, (41 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8887 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 37%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8887,joint_update_expr_8887) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1278%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8887 joint_update_expr_8887 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8887 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8288 time ltac:(lia) ltac:(lia)).
  rewrite (H8886 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 37%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 36%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 36%nat) else wbkill_decode 36%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 36%nat)); reflexivity.
 }
 assert (H8692 : forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8692 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 38%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8692,joint_update_expr_8692) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1181%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8692 joint_update_expr_8692 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8692 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8286 time ltac:(lia) ltac:(lia)).
  rewrite (H8691 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 38%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 37%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 37%nat) else wbkill_decode 37%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 37%nat)); reflexivity.
 }
 assert (H8839 : forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8839 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 38%nat instruction);wbkill_high (wbkill_decode 38%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8839,joint_update_expr_8839) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1230%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8839 joint_update_expr_8839 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8839 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8286 time ltac:(lia) ltac:(lia)).
  rewrite (H8838 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 38%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 37%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 37%nat) else wbkill_decode 37%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 37%nat)); reflexivity.
 }
 assert (H8888 : forall time, (42 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8888 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 38%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8888,joint_update_expr_8888) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1279%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8888 joint_update_expr_8888 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8888 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8286 time ltac:(lia) ltac:(lia)).
  rewrite (H8887 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 38%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 37%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 37%nat) else wbkill_decode 37%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 37%nat)); reflexivity.
 }
 assert (H8693 : forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8693 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 39%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8693,joint_update_expr_8693) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1182%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8693 joint_update_expr_8693 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8693 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8284 time ltac:(lia) ltac:(lia)).
  rewrite (H8692 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 39%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 38%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 38%nat) else wbkill_decode 38%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 38%nat)); reflexivity.
 }
 assert (H8840 : forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8840 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 39%nat instruction);wbkill_high (wbkill_decode 39%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8840,joint_update_expr_8840) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1231%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8840 joint_update_expr_8840 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8840 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8284 time ltac:(lia) ltac:(lia)).
  rewrite (H8839 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 39%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 38%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 38%nat) else wbkill_decode 38%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 38%nat)); reflexivity.
 }
 assert (H8889 : forall time, (43 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8889 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 39%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8889,joint_update_expr_8889) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1280%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8889 joint_update_expr_8889 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8889 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8284 time ltac:(lia) ltac:(lia)).
  rewrite (H8888 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 39%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 38%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 38%nat) else wbkill_decode 38%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 38%nat)); reflexivity.
 }
 assert (H8694 : forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8694 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 40%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8694,joint_update_expr_8694) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1183%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8694 joint_update_expr_8694 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8694 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8282 time ltac:(lia) ltac:(lia)).
  rewrite (H8693 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 40%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 39%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 39%nat) else wbkill_decode 39%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 39%nat)); reflexivity.
 }
 assert (H8841 : forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8841 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 40%nat instruction);wbkill_high (wbkill_decode 40%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8841,joint_update_expr_8841) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1232%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8841 joint_update_expr_8841 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8841 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8282 time ltac:(lia) ltac:(lia)).
  rewrite (H8840 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 40%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 39%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 39%nat) else wbkill_decode 39%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 39%nat)); reflexivity.
 }
 assert (H8890 : forall time, (44 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8890 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 40%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8890,joint_update_expr_8890) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1281%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8890 joint_update_expr_8890 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8890 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8282 time ltac:(lia) ltac:(lia)).
  rewrite (H8889 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 40%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 39%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 39%nat) else wbkill_decode 39%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 39%nat)); reflexivity.
 }
 assert (H8695 : forall time, (45 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8695 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 41%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8695,joint_update_expr_8695) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1184%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8695 joint_update_expr_8695 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8695 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8280 time ltac:(lia) ltac:(lia)).
  rewrite (H8694 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 41%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 40%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 40%nat) else wbkill_decode 40%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 40%nat)); reflexivity.
 }
 assert (H8842 : forall time, (45 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8842 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 41%nat instruction);wbkill_high (wbkill_decode 41%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8842,joint_update_expr_8842) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1233%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8842 joint_update_expr_8842 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8842 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8280 time ltac:(lia) ltac:(lia)).
  rewrite (H8841 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 41%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 40%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 40%nat) else wbkill_decode 40%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 40%nat)); reflexivity.
 }
 assert (H8891 : forall time, (45 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8891 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 41%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8891,joint_update_expr_8891) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1282%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8891 joint_update_expr_8891 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8891 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8280 time ltac:(lia) ltac:(lia)).
  rewrite (H8890 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 41%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 40%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 40%nat) else wbkill_decode 40%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 40%nat)); reflexivity.
 }
 assert (H8696 : forall time, (46 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8696 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 42%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8696,joint_update_expr_8696) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1185%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8696 joint_update_expr_8696 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8696 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8278 time ltac:(lia) ltac:(lia)).
  rewrite (H8695 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 42%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 41%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 41%nat) else wbkill_decode 41%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 41%nat)); reflexivity.
 }
 assert (H8843 : forall time, (46 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8843 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 42%nat instruction);wbkill_high (wbkill_decode 42%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8843,joint_update_expr_8843) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1234%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8843 joint_update_expr_8843 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8843 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8278 time ltac:(lia) ltac:(lia)).
  rewrite (H8842 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 42%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 41%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 41%nat) else wbkill_decode 41%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 41%nat)); reflexivity.
 }
 assert (H8892 : forall time, (46 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8892 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 42%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8892,joint_update_expr_8892) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1283%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8892 joint_update_expr_8892 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8892 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8278 time ltac:(lia) ltac:(lia)).
  rewrite (H8891 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 42%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 41%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 41%nat) else wbkill_decode 41%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 41%nat)); reflexivity.
 }
 assert (H8697 : forall time, (47 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8697 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 43%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8697,joint_update_expr_8697) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1186%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8697 joint_update_expr_8697 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8697 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8276 time ltac:(lia) ltac:(lia)).
  rewrite (H8696 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 43%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 42%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 42%nat) else wbkill_decode 42%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 42%nat)); reflexivity.
 }
 assert (H8844 : forall time, (47 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8844 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 43%nat instruction);wbkill_high (wbkill_decode 43%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8844,joint_update_expr_8844) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1235%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8844 joint_update_expr_8844 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8844 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8276 time ltac:(lia) ltac:(lia)).
  rewrite (H8843 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 43%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 42%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 42%nat) else wbkill_decode 42%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 42%nat)); reflexivity.
 }
 assert (H8893 : forall time, (47 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8893 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 43%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8893,joint_update_expr_8893) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1284%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8893 joint_update_expr_8893 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8893 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8276 time ltac:(lia) ltac:(lia)).
  rewrite (H8892 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 43%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 42%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 42%nat) else wbkill_decode 42%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 42%nat)); reflexivity.
 }
 assert (H8698 : forall time, (48 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8698 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 44%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8698,joint_update_expr_8698) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1187%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8698 joint_update_expr_8698 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8698 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8274 time ltac:(lia) ltac:(lia)).
  rewrite (H8697 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 44%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 43%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 43%nat) else wbkill_decode 43%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 43%nat)); reflexivity.
 }
 assert (H8845 : forall time, (48 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8845 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 44%nat instruction);wbkill_high (wbkill_decode 44%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8845,joint_update_expr_8845) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1236%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8845 joint_update_expr_8845 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8845 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8274 time ltac:(lia) ltac:(lia)).
  rewrite (H8844 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 44%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 43%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 43%nat) else wbkill_decode 43%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 43%nat)); reflexivity.
 }
 assert (H8894 : forall time, (48 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8894 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 44%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8894,joint_update_expr_8894) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1285%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8894 joint_update_expr_8894 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8894 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8274 time ltac:(lia) ltac:(lia)).
  rewrite (H8893 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 44%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 43%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 43%nat) else wbkill_decode 43%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 43%nat)); reflexivity.
 }
 assert (H8699 : forall time, (49 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8699 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 45%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8699,joint_update_expr_8699) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1188%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8699 joint_update_expr_8699 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8699 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8272 time ltac:(lia) ltac:(lia)).
  rewrite (H8698 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 45%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 44%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 44%nat) else wbkill_decode 44%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 44%nat)); reflexivity.
 }
 assert (H8846 : forall time, (49 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8846 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 45%nat instruction);wbkill_high (wbkill_decode 45%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8846,joint_update_expr_8846) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1237%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8846 joint_update_expr_8846 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8846 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8272 time ltac:(lia) ltac:(lia)).
  rewrite (H8845 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 45%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 44%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 44%nat) else wbkill_decode 44%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 44%nat)); reflexivity.
 }
 assert (H8895 : forall time, (49 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8895 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 45%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8895,joint_update_expr_8895) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1286%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8895 joint_update_expr_8895 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8895 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8272 time ltac:(lia) ltac:(lia)).
  rewrite (H8894 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 45%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 44%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 44%nat) else wbkill_decode 44%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 44%nat)); reflexivity.
 }
 assert (H8700 : forall time, (50 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8700 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 46%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8700,joint_update_expr_8700) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1189%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8700 joint_update_expr_8700 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8700 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8270 time ltac:(lia) ltac:(lia)).
  rewrite (H8699 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 46%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 45%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 45%nat) else wbkill_decode 45%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 45%nat)); reflexivity.
 }
 assert (H8847 : forall time, (50 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8847 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 46%nat instruction);wbkill_high (wbkill_decode 46%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8847,joint_update_expr_8847) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1238%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8847 joint_update_expr_8847 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8847 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8270 time ltac:(lia) ltac:(lia)).
  rewrite (H8846 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 46%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 45%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 45%nat) else wbkill_decode 45%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 45%nat)); reflexivity.
 }
 assert (H8896 : forall time, (50 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8896 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 46%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8896,joint_update_expr_8896) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1287%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8896 joint_update_expr_8896 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8896 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8270 time ltac:(lia) ltac:(lia)).
  rewrite (H8895 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 46%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 45%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 45%nat) else wbkill_decode 45%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 45%nat)); reflexivity.
 }
 assert (H8701 : forall time, (51 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8701 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 47%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8701,joint_update_expr_8701) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1190%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8701 joint_update_expr_8701 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8701 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8268 time ltac:(lia) ltac:(lia)).
  rewrite (H8700 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 47%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 46%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 46%nat) else wbkill_decode 46%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 46%nat)); reflexivity.
 }
 assert (H8848 : forall time, (51 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8848 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 47%nat instruction);wbkill_high (wbkill_decode 47%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8848,joint_update_expr_8848) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1239%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8848 joint_update_expr_8848 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8848 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8268 time ltac:(lia) ltac:(lia)).
  rewrite (H8847 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 47%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 46%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 46%nat) else wbkill_decode 46%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 46%nat)); reflexivity.
 }
 assert (H8897 : forall time, (51 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8897 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 47%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8897,joint_update_expr_8897) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1288%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8897 joint_update_expr_8897 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8897 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8268 time ltac:(lia) ltac:(lia)).
  rewrite (H8896 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 47%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 46%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 46%nat) else wbkill_decode 46%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 46%nat)); reflexivity.
 }
 assert (H8702 : forall time, (52 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8702 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 48%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8702,joint_update_expr_8702) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1191%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8702 joint_update_expr_8702 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8702 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8266 time ltac:(lia) ltac:(lia)).
  rewrite (H8701 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 48%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 47%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 47%nat) else wbkill_decode 47%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 47%nat)); reflexivity.
 }
 assert (H8849 : forall time, (52 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8849 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 48%nat instruction);wbkill_high (wbkill_decode 48%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8849,joint_update_expr_8849) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1240%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8849 joint_update_expr_8849 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8849 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8266 time ltac:(lia) ltac:(lia)).
  rewrite (H8848 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 48%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 47%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 47%nat) else wbkill_decode 47%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 47%nat)); reflexivity.
 }
 assert (H8898 : forall time, (52 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8898 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 48%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8898,joint_update_expr_8898) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1289%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8898 joint_update_expr_8898 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8898 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8266 time ltac:(lia) ltac:(lia)).
  rewrite (H8897 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 48%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 47%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 47%nat) else wbkill_decode 47%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 47%nat)); reflexivity.
 }
 assert (H8703 : forall time, (53 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8703 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8703,joint_update_expr_8703) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1192%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8703 joint_update_expr_8703 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8703 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8264 time ltac:(lia) ltac:(lia)).
  rewrite (H8702 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 49%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 48%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 48%nat) else wbkill_decode 48%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 48%nat)); reflexivity.
 }
 assert (H8850 : forall time, (53 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8850 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49%nat instruction);wbkill_high (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8850,joint_update_expr_8850) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1241%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8850 joint_update_expr_8850 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8850 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8264 time ltac:(lia) ltac:(lia)).
  rewrite (H8849 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 49%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 48%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 48%nat) else wbkill_decode 48%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 48%nat)); reflexivity.
 }
 assert (H8899 : forall time, (53 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8899 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8899,joint_update_expr_8899) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1290%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8899 joint_update_expr_8899 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8899 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8264 time ltac:(lia) ltac:(lia)).
  rewrite (H8898 time ltac:(lia) ltac:(lia)).
  change (wbkill_decode 49%nat instruction) with (if wbkill_choice instruction (nth wbkill_default_row wbkill_rows 48%nat) then wbkill_row_value (nth wbkill_default_row wbkill_rows 48%nat) else wbkill_decode 48%nat instruction).
  destruct (wbkill_choice instruction (nth wbkill_default_row wbkill_rows 48%nat)); reflexivity.
 }
 assert (H8998 : forall time, (54 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8998 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8998,joint_update_expr_8998) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1389%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8998 joint_update_expr_8998 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8998 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8703 time ltac:(lia) ltac:(lia)).
  reflexivity.
 }
 assert (H8999 : forall time, (54 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8999 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  assert (Member : List.In (8999,joint_update_expr_8999) joint_update_expected_nodes).
  { apply (List.nth_error_In joint_update_expected_nodes 1390%nat). vm_compute. reflexivity. }
  destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes 8999 joint_update_expr_8999 joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
  eapply formal_combinational_known_ground_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|apply Steps;lia].
  cbn [joint_update_expr_8999 eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
  try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
  rewrite (H8899 time ltac:(lia) ltac:(lia)).
  reflexivity.
 }
 assert (H8251 : forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8251 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 9011%nat 749%nat 8251 8998 1%nat (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)]) (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)]) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_8251_checked|apply H8998;lia| |apply Steps;lia].
  reflexivity.
 }
 assert (H85 : forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 85 (history time) = Some (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 62%nat 9928%nat 85 8251 1%nat (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)]) (Gval (Fuint 1) [::wbkill_kill (wbkill_decode 49%nat instruction)]) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_85_checked|apply H8251;lia| |apply Steps;lia].
  reflexivity.
 }
 assert (H8259 : forall time, (54 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8259 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49%nat instruction);wbkill_high (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 9019%nat 749%nat 8259 8850 2%nat (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49%nat instruction);wbkill_high (wbkill_decode 49%nat instruction)]) (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49%nat instruction);wbkill_high (wbkill_decode 49%nat instruction)]) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_8259_checked|apply H8850;lia| |apply Steps;lia].
  reflexivity.
 }
 assert (H93 : forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 93 (history time) = Some (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49%nat instruction);wbkill_high (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 70%nat 9928%nat 93 8259 2%nat (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49%nat instruction);wbkill_high (wbkill_decode 49%nat instruction)]) (Gval (Fuint 2) [::wbkill_low (wbkill_decode 49%nat instruction);wbkill_high (wbkill_decode 49%nat instruction)]) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_93_checked|apply H8259;lia| |apply Steps;lia].
  reflexivity.
 }
 assert (H8260 : forall time, (55 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 8260 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 9020%nat 749%nat 8260 8999 1%nat (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)]) (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)]) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_8260_checked|apply H8999;lia| |apply Steps;lia].
  reflexivity.
 }
 assert (H94 : forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat -> VM.find 94 (history time) = Some (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)])).
 { intros time Lower Upper. destruct time as [|time]; [lia|].
  eapply (declared_wire_checked_value flat_memories flat_statements 71%nat 9928%nat 94 8260 1%nat (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)]) (Gval (Fuint 1) [::wbkill_enable (wbkill_decode 49%nat instruction)]) invalid (history time) (history time) (history (S time)));
  [exact wbkill_wire_94_checked|apply H8260;lia| |apply Steps;lia].
  reflexivity.
 }
 intros time Lower Upper. repeat split; [apply H85|apply H93|apply H94];lia.
Qed.
Theorem control_writeback_kill_history invalid history limit instruction :
 size instruction = 32%nat ->
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction) ->
 (forall time, (time < limit)%coq_nat -> formal_value_iter invalid flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (56 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 94 (history time) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 93 (history time) <> Some (Gval (Fuint 2) [::false;false]) ->
 VM.find 85 (history time) = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Size Initial Steps time Lower Upper Enable NonAlu.
 destruct (control_writeback_decode_history invalid history limit instruction Size Initial Steps time Lower Upper) as [Kill [Sel En]].
 pose proof (wbkill_decode_safe 49 instruction ltac:(lia)) as Safe.
 destruct (wbkill_decode 49 instruction) as [kill low high enabled].
 destruct kill, low, high, enabled; cbn [wbkill_safe wbkill_kill wbkill_low wbkill_high wbkill_enable] in *; try congruence.
 all: try discriminate.
 Show.
Qed.
