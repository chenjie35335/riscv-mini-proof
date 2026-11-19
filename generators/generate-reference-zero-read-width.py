"""Actual selected-zero read-width chain, independent of alignment/data values."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/CoreSocModel.v').read_text()
def expr(n):
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+' ',s);d=0
 for e in range(m.start(),len(s)):
  d+=(s[e]=='(')-(s[e]==')')
  if d==0:return s[m.end():e]
head='''Require Import CoreSocModel ComparisonNodes ReferenceRequestSpine ReferenceRedirectSpine SelectedZeroMux FormalDeclaredWireCheck.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
rows=[(6531,1970,6520),(6555,1966,6531),(6580,1962,6555),(6598,1958,6580),(6621,1886,6598)]
nodes=[6520]+[r[0] for r in rows]+[7112,7187]
for n in nodes:
 head+=f'Definition zero_read_expression_{n} :={expr(n)}.\n'
 head+=f'Lemma zero_read_member_{n} :List.In({n},zero_read_expression_{n})reference_request_nodes.\nProof. vm_compute;tauto. Qed.\n'
head+='''Theorem reference_zero_read_width_history invalid history limit start enabled :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1707(history t)=Some(Gval(Fuint 1)[::enabled])) ->
 (forall node,List.In node [::1970;1966;1962;1958;1886] ->forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1521(history t)=Some(Gval(Fuint 6)(zeros 6)).
Proof.
 intros Steps Enable Guards.
 assert(Base:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6520(history t)=Some(Gval(Fuint 6)(zeros 6))).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 6520 zero_read_expression_6520);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_6520| |apply Steps;lia]. intros site;reflexivity. }
'''
for i,(n,g,source) in enumerate(rows):
 head+=f''' assert(Z{n}:forall t,(Nat.add start {i+2}<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find {n}(history t)=Some(Gval(Fuint width)(zeros width))).
 {{ intros[|t] Lower Upper;try lia.
'''
 head+=(' pose proof(Base t ltac:(lia) ltac:(lia))as Zero.\n' if i==0 else f' destruct(Z{source} t ltac:(lia) ltac:(lia))as[width Zero].\n')
 head+=f''' eapply(selected_zero_mux reference_request_offsets reference_request_nodes {n} _ _ _ invalid(history t)(history(S t))false {'6' if i==0 else 'width'});
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_{n}| | |apply Steps;lia].
 - intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. apply Guards;[cbn;tauto|lia|lia].
 - intros site;exact Zero. }}
'''
head+=''' assert(Z7112:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 7112(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia. destruct(Z6621 t ltac:(lia) ltac:(lia))as[width Zero].
 destruct enabled;
 eapply(selected_zero_mux reference_request_offsets reference_request_nodes 7112 _ _ _ invalid(history t)(history(S t)));
 try exact reference_request_positions;try exact reference_request_safety;try exact zero_read_member_7112;
 try (intros site;cbn [eval_hfexpr_validif_policy eval_href_validif_policy];apply Enable;lia);
 try (intros site;exact Zero);try (intros site;apply Base;lia);try (apply Steps;lia). }
 assert(Z7187:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->exists width,VM.find 7187(history t)=Some(Gval(Fuint width)(zeros width))).
 { intros[|t] Lower Upper;try lia. destruct(Z7112 t ltac:(lia) ltac:(lia))as[width Zero]. exists width.
 eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes 7187 zero_read_expression_7187);
 [exact reference_request_positions|exact reference_request_safety|exact zero_read_member_7187|intros site;exact Zero|apply Steps;lia]. }
 assert(Z1711:forall t,(Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1711(history t)=Some(Gval(Fuint 6)(zeros 6))).
 { intros[|t] Lower Upper;try lia. destruct(Z7187 t ltac:(lia) ltac:(lia))as[width Zero].
 eapply declared_wire_checked_value;[exact(reference_request_wire_certificate 1%nat false ltac:(lia))|exact Zero| |apply Steps;lia].
 cbn [adapt_hvalue_as_type]. rewrite zero_word_resize;reflexivity. }
 intros[|t] Lower Upper;try lia.
 pose proof(Z1711 t ltac:(lia) ltac:(lia))as Zero.
 eapply declared_wire_checked_value;[exact(reference_request_wire_certificate 1%nat true ltac:(lia))|exact Zero|reflexivity|apply Steps;lia].
Qed.
'''
(root/'formal/flat-low/staged-integration/ReferenceZeroReadWidth.v').write_text(head)
