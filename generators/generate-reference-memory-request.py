"""Batch load/store request decode and request spine from flattened model."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';model=(base/'CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
guards=[1886,1958,1962,1966,1970,1951,1946,1941]
ids=sorted([n for g in guards for n in [g-1,g]])
expr={};pos=[]
for n in ids:
 a=model.index(f'(@Snode VarOrder.T {n} ')+len(f'(@Snode VarOrder.T {n} ');d=0
 for b in range(a,len(model)):
  d+=(model[b]=='(')-(model[b]==')')
  if d==0:break
 expr[n]=model[a:b+1];pos.append(bisect.bisect_right(q,a)-1)
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
widths=[];codes=[]
for g in guards:
 m=re.search(r'\(Fuint (\d+)\) \[::([^]]*)\]',expr[g]);widths.append(int(m[1]));codes.append(sum((b.strip()=='true')<<i for i,b in enumerate(m[2].split(';'))))
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine DUTRedirectDecode LoadTypeCorrespondence.
From Coq Require Import NArith ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
out+='Definition reference_memory_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := '+seq([f'({n},{expr[n]})' for n in ids])+'.\n'
out+='Definition reference_memory_offsets := '+seq([str(n)+'%nat' for n in [pos[0]]+[b-a-1 for a,b in zip(pos,pos[1:])]])+'.\n'
out+='Definition reference_memory_guards : seq VarOrder.T := '+seq(guards)+'.\n'
out+='Definition reference_memory_codes : seq N := '+seq(codes)+'.\n'
out+='Definition reference_memory_code_widths : seq nat := '+seq([str(n)+'%nat' for n in widths])+'.\n'
out+='''Lemma reference_memory_positions : select_node_offsets reference_memory_offsets flat_statements = Some reference_memory_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma reference_memory_safety : selected_node_safety flat_memories flat_statements reference_memory_offsets flat_statements = true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition reference_memory_guard row := nth 0 reference_memory_guards row.
Definition reference_memory_code row := nth 0 reference_memory_codes row.
Definition reference_memory_code_width row := nth 0%nat reference_memory_code_widths row.
Definition reference_memory_mask_expression (row:nat) := @Eprim_binop VarOrder.T Band (@Eref VarOrder.T (@Eid VarOrder.T 1884)) (@Econst VarOrder.T (Fuint 15) (from_N 15 28799)).
Definition reference_memory_guard_expression row := @Eprim_binop VarOrder.T (Bcomp Beq)
 (@Econst VarOrder.T (Fuint (reference_memory_code_width row)) (from_N (reference_memory_code_width row) (reference_memory_code row)))
 (@Eref VarOrder.T (@Eid VarOrder.T (reference_memory_guard row - 1))).
Lemma reference_memory_decode_certificates row : (row < 8)%coq_nat ->
 List.In (reference_memory_guard row - 1,reference_memory_mask_expression row) reference_memory_nodes /\\
 List.In (reference_memory_guard row,reference_memory_guard_expression row) reference_memory_nodes /\\
 to_N (from_N (reference_memory_code_width row) (reference_memory_code row)) = reference_memory_code row.
Proof.
 intro Row. do 8 (destruct row as [|row];[repeat split;try reflexivity;vm_compute;tauto|]);lia.
Qed.
Theorem reference_memory_decode_history invalid history limit instruction row :
 (row < 8)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (i <= limit)%coq_nat -> VM.find 1884 (history i) = Some (Gval (Fuint 32) instruction)) ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (reference_memory_guard row) (history time) = Some (Gval (Fuint 1) [::N.eqb (reference_memory_code row) (N.land (to_N instruction) 28799)]).
Proof.
 intros Row Steps Instruction [|[|time]] Lower Upper;try lia.
 destruct (reference_memory_decode_certificates row Row) as [MC [GC Code]].
 assert (Mask : VM.find (reference_memory_guard row - 1) (history (S time)) = Some (Gval (Fuint 32) (andB instruction (from_N 15 28799)))).
 { eapply (reference_redirect_ground_step reference_memory_offsets reference_memory_nodes _ (reference_memory_mask_expression row));
 [exact reference_memory_positions|exact reference_memory_safety|exact MC| |apply Steps;lia].
 intros site. unfold reference_memory_mask_expression. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite (Instruction time ltac:(lia)) size_from_N ltnn. unfold zext_to. rewrite size_from_N subnn. unfold zext. rewrite zeros0 cats0. reflexivity. }
 eapply (reference_redirect_ground_step reference_memory_offsets reference_memory_nodes _ (reference_memory_guard_expression row));
 [exact reference_memory_positions|exact reference_memory_safety|exact GC| |apply Steps;lia].
 intros site. unfold reference_memory_guard_expression. cbn [eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite size_from_N ltnn. unfold zext_to. rewrite size_from_N subnn. unfold zext. rewrite zeros0 cats0 Mask.
 rewrite (redirect_mask_decode instruction (from_N 15 28799) (from_N (reference_memory_code_width row) (reference_memory_code row)) 32 15 (reference_memory_code_width row)) Code N.eqb_sym. reflexivity.
Qed.
Lemma reference_memory_decode_load instruction lane row : (lane < 5)%coq_nat -> (row < 8)%coq_nat ->
 N.land instruction 28799 = load_type_lane_code lane ->
 N.eqb (reference_memory_code row) (N.land instruction 28799) = Nat.eqb row lane.
Proof.
 intros Lane Row Load. rewrite Load.
 do 5 (destruct lane as [|lane];[do 8 (destruct row as [|row];[reflexivity|]);lia|]);lia.
Qed.
'''
p=base/'staged-integration/ReferenceMemoryRequest.v';mark='(* Unified request spine. *)';tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n';p.write_text(out+mark+tail)
