"""One induction over the actual 48-entry illegal-instruction mux spine."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration/ReferenceIllegalSpine.v'
s='''Require Import CoreSocModel ComparisonNodes ReferenceInstructionDecode ReferenceIllegalFold ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCertificates3 ReferenceControlNodeCongruence3.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_illegal_expression row := @Emux VarOrder.T
 (@Eref VarOrder.T (@Eid VarOrder.T (reference_instruction_guard row)))
 (@Econst VarOrder.T (Fuint 1) [::false])
 (match row with O => @Econst VarOrder.T (Fuint 1) [::true]
 | S n => @Eref VarOrder.T (@Eid VarOrder.T (2993 + N.of_nat n)) end).
Lemma reference_illegal_member row : (row < 48)%coq_nat ->
 List.In (2993+N.of_nat row, reference_illegal_expression row) reference_control_3_nodes.
Proof. intro Bound.
'''
for n in range(48):s+=f' destruct row as [|row];[exact reference_control_member_{2993+n}|].\n'
s+=' lia.\nQed.\n'
s+='''Lemma reference_illegal_step row guards invalid old result :
 (row < 48)%coq_nat ->
 VM.find (reference_instruction_guard row) old = Some (Gval (Fuint 1) [::guards row]) ->
 (row <> 0%nat -> VM.find (2992+N.of_nat row) old = Some (Gval (Fuint 1) [::reference_illegal_fold guards row])) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (2993+N.of_nat row) result = Some (Gval (Fuint 1) [::reference_illegal_fold guards (S row)]).
Proof.
 intros Bound Guard Previous Step.
 eapply (reference_redirect_ground_step reference_control_3_offsets reference_control_3_nodes _ (reference_illegal_expression row));
 [exact reference_control_3_positions|exact reference_control_3_safety|apply reference_illegal_member;exact Bound| |exact Step].
 intros site. unfold reference_illegal_expression. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Guard.
 destruct row as [|row].
 - cbn [reference_illegal_fold]. destruct (guards 0%nat);reflexivity.
 - assert (Prev : VM.find (2993+N.of_nat row) old = Some (Gval (Fuint 1) [::reference_illegal_fold guards (S row)])).
   { replace (2993+N.of_nat row) with (2992+N.of_nat (S row)) by lia. apply Previous;discriminate. }
   destruct (guards (S row)) eqn:Choice;cbn;unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref];rewrite Prev;
   cbn [reference_illegal_fold];rewrite Choice;destruct (guards row);reflexivity.
Qed.
Theorem reference_illegal_prefix_history invalid history limit start guards :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall row i, (row < 48)%coq_nat -> (start <= i)%coq_nat -> (i <= limit)%coq_nat -> VM.find (reference_instruction_guard row) (history i) = Some (Gval (Fuint 1) [::guards row])) ->
 forall count, (0 < count)%coq_nat -> (count <= 48)%coq_nat ->
 forall time, (Nat.add start count <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (2992+N.of_nat count) (history time) = Some (Gval (Fuint 1) [::reference_illegal_fold guards count]).
Proof.
 intros Steps Guards count. induction count as [|count IH];intros Positive Bound [|time] Lower Upper;try lia.
 replace (2992+N.of_nat (S count)) with (2993+N.of_nat count) by lia.
 eapply (reference_illegal_step count guards invalid (history time) (history (S time)));[lia|apply Guards;lia| |apply Steps;lia].
 intro Nonzero. apply IH;lia.
Qed.
'''
mark='(* Final illegal output. *)'
tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n'
p.write_text(s+mark+tail)
