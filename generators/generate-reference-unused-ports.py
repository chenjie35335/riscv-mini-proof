"""Zero default read addresses for the JAL/JALR unused operand ports."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration';src=(p/'RFALUReferencePorts.v').read_text();s=src[:src.index('Definition rf_alu_rs1_node')]
s+='Require Import RFALUReferencePorts ReferenceImmediatePrefix RFLinkReferenceEffect.\n'
for port,count,base,guards,raws,group,gate,output,gi,oi in [(1,42,2099,[2096,2092,2088],[2098,2094,2090],0,2144,2145,15,16),(2,24,2594,[2059,2054,2049],[2593,2592,2591],2,2621,2622,6,7)]:
 typ=(p/f'ReferenceRs{port}Types.v').read_text();ids=list(map(int,re.search(r'Definition reference_rs'+str(port)+r'_ids.*?\[::(.*?)\]',typ)[1].split(';')))
 s+=f'Definition unused_rs{port}_prefix_guards :seq VarOrder.T := [::'+ ';'.join(map(str,guards))+'].\n'
 s+=f'''Theorem unused_rs{port}_history inputs path history limit reset time instruction :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<3)%coq_nat ->VM.find(nth 0 unused_rs{port}_prefix_guards n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 (forall n,(n<{count})%coq_nat ->VM.find(rf_alu_rs{port}_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find {output}(history time)=Some(Gval(Fuint 5)(zeros 5)).
Proof.
 intros Resets Steps Source Lower Upper Enabled PrefixGuards Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\type_of_val value=Gtyp(Fuint 32)).
 {{intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity].}}
'''.replace('/\t','/\\t')
 for i,(g,raw) in enumerate(zip(guards,raws)):
  node=base+i
  s+=f''' destruct(reference_rs{port}_types_history _ history limit 200 Steps Typed {ids.index(raw)}%nat ltac:(vm_compute;lia)time ltac:(cbv[reference_rs{port}_rank reference_rs{port}_ranks nth];lia)ltac:(lia))as[other{i}[Other{i} Shape{i}]].
 assert(V{node}:VM.find {node}(history time)=Some(Gval(Fuint 5)(zeros 5))).
 {{ rewrite(reference_control_stable_{node}_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_{group}_offsets reference_control_{group}_nodes {node} reference_control_expr_{node});[exact reference_control_{group}_positions|exact reference_control_{group}_safety|exact reference_control_member_{node}| |apply Steps;lia].
 intro site. cbn[reference_control_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy].
 pose proof(PrefixGuards {i}%nat ltac:(lia))as Guard. change(VM.find {g}(history time)=Some(Gval(Fuint 1)[::false]))in Guard. rewrite Guard. cbn.
'''
  if i:s+=f' rewrite V{node-1}.\n'
  s+=f''' unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Other{i};cbn[option_map];rewrite Shape{i}. reflexivity. }}
'''
 s+=f''' assert(Selected:VM.find(rf_alu_rs{port}_node {count-1}%nat)(history time)=Some(Gval(Fuint 5)(zeros 5))).
 {{ eapply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time){count} 5(zeros 5){base+2} rf_alu_rs{port}_node rf_alu_rs{port}_guard rf_alu_rs{port}_yes);[reflexivity| |exact Guards| |exact V{base+2}|lia].
 - intros n Bound value Eval. rewrite(rf_alu_rs{port}_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 apply(rf_alu_rs{port}_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs{port}_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }}
 assert(Gate:VM.find {gate}(history time)=Some(Gval(Fuint 5)(zeros 5))).
 {{eapply(rf_alu_rs{port}_value {gi} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[rf_alu_rs{port}_aux_expr nth reference_control_expr_{gate} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Selected. reflexivity. }}
 eapply(rf_alu_rs{port}_value {oi} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Gate.
Qed.
'''
(p/'ReferenceUnusedReadPorts.v').write_text(s)
