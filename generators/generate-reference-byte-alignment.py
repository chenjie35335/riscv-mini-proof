"""Shared actual byte-alignment proof, without address or operand premises."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
expr=dict(re.findall(r'Definition reference_control_expr_(\d+) := (.*)\.',(base/'ReferenceControlExpressions.v').read_text()))
rows=[([2566,2625,2628],[2624,2627,2630],[2631,2632,2633],2634),([2724,2727,2730],[2726,2729,2732],[2733,2734,2735],2736),([2665,2671,2674],[2670,2673,2676],[2677,2678,2679],None)]
out='''Require Import CoreSocModel ComparisonNodes ReferenceBooleanShape ReferenceRedirectSpine ReferenceControlExpressions ReferenceControlNodeCongruence2 ReferenceControlNodeCertificates2 NormalizedBit.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem reference_byte_alignment_history lane invalid history limit :
 (lane < 3)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if Nat.eqb lane 0 then 2634 else if Nat.eqb lane 1 then 2736 else 2679) (history time) = Some (Gval (Fuint 1) [::Nat.eqb lane 2]).
Proof.
 intros Lane Steps.
'''
for constants,comparisons,muxes,output in rows:
 out+=' destruct lane as [|lane].\n {\n'
 def ground(n):
  return f''' eapply (reference_redirect_ground_step reference_control_2_offsets reference_control_2_nodes {n} reference_control_expr_{n});
 [exact reference_control_2_positions|exact reference_control_2_safety|exact reference_control_member_{n}| |apply Steps;lia].
 intros site. cbn [reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
 for n in constants:
  out+=f''' assert (C{n} : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find {n} (history t) = Some (Gval (Fuint 1) [::false])).
 {{ intros [|t] Lower Upper;try lia.
'''+ground(n)+' reflexivity. }\n'
 for n in comparisons:
  source=re.search(r'\(@Eid VarOrder.T (\d+)\)',expr[str(n)])[1]
  out+=f''' assert (N{n} : forall t, (1 <= t)%coq_nat -> (t <= limit)%coq_nat -> exists value, VM.find {n} (history t) = Some value /\ normalized_bit value).
 {{ intros [|t] Lower Upper;try lia.
 exact (reference_zero_comparison_normalized reference_control_2_offsets reference_control_2_nodes {n} {source} invalid (history t) (history (S t)) reference_control_2_positions reference_control_2_safety reference_control_member_{n} (Steps t ltac:(lia))). }}
'''
 for j,n in enumerate(muxes):
  c=constants[2-j];y=comparisons[2-j]
  out+=f''' assert (M{n} : forall t, ({j+2} <= t)%coq_nat -> (t <= limit)%coq_nat -> VM.find {n} (history t) = Some (Gval (Fuint 1) [::true])).
 {{ intros [|t] Lower Upper;try lia.
 destruct (N{y} t ltac:(lia) ltac:(lia)) as [value [Lookup Normal]].
'''+ground(n)+f' rewrite (C{c} t ltac:(lia) ltac:(lia)). cbn.\n'
  if j:out+=f' rewrite (M{muxes[j-1]} t ltac:(lia) ltac:(lia)).\n'
  out+=" unfold eval_type_of_expr;cbn [type_of_expr' eval_type_of_ref]. rewrite Lookup. destruct Normal;reflexivity. }\n"
 if output is None:
  out+=' intros time Lower Upper. exact (M2679 time ltac:(lia) Upper). }\n'
 else:
  out+=' intros [|time] Lower Upper;try lia.\n'+ground(output)
  out+=f' rewrite (M{muxes[-1]} time ltac:(lia) ltac:(lia)). reflexivity. }}\n'
out+=' lia.\nQed.\n'
out+='''Theorem reference_byte_invalid_history writing invalid history limit :
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 forall time, (5 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find (if writing then 2736 else 2634) (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Steps time Lower Upper. destruct writing;
 [exact (reference_byte_alignment_history 1%nat invalid history limit ltac:(lia) Steps time Lower Upper)
 |exact (reference_byte_alignment_history 0%nat invalid history limit ltac:(lia) Steps time Lower Upper)].
Qed.
'''
p=base/'ReferenceByteAlignment.v';mark='(* Observed byte alignment. *)'
tail=p.read_text().split(mark,1)[1] if p.exists() and mark in p.read_text() else '\n'
p.write_text(out+mark+tail)
