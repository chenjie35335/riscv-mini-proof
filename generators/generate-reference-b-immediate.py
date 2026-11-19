"""One parameterized six-lane extraction proof for B immediates."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration';s=(p/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.',s).group(1).split(';')))
nodes=[[1975+6*l for l in range(6)],[1976+6*l for l in range(6)],[1977+6*l for l in range(6)],[2332+4*l for l in range(6)],[2333+4*l for l in range(6)],[2334+4*l for l in range(6)],[2335+4*l for l in range(6)],[2318+l for l in range(6)],[2371+l for l in range(6)],[2386+l for l in range(6)]]
words=['take 31 instruction','take 25 instruction','take 20 instruction','take 15 instruction','take 12 instruction','take 8 instruction','drop 7(take 8 instruction)','drop 31(take 32 instruction)','drop 25(take 31 instruction)','drop 8(take 12 instruction)'];widths=[31,25,20,15,12,8,1,1,6,4];deps=[None,0,1,2,3,4,5,None,0,4]
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='''Require Import ReferenceBranchImmediate ReferenceImmediateTypes ReferenceControlExpressions CoreSocModel ComparisonNodes.
From Coq Require Import NArith Arith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
out+=f'Definition branch_raw_index stage lane :=nth 0%nat(nth [::] {seq([seq([str(ids.index(n))+"%nat"for n in row])for row in nodes])} stage)lane.\n'
out+='Definition branch_raw_node stage lane :=reference_immediate_node(branch_raw_index stage lane).\n'
out+=f'Definition branch_raw_width stage :=nth 0%nat {seq([str(w)+"%nat"for w in widths])} stage.\n'
out+=f'Definition branch_raw_word stage (instruction:bits) :=nth [::] {seq(["("+w+")"for w in words])} stage.\n'
out+='''Lemma branch_raw_bound stage lane : (stage<10)%coq_nat ->(lane<6)%coq_nat ->(branch_raw_index stage lane<304)%coq_nat.
Proof. do 10(destruct stage as[|stage];[do 6(destruct lane as[|lane];[vm_compute;lia|]);lia|]);lia. Qed.
Lemma branch_raw_eval stage lane invalid old instruction :
 (stage<10)%coq_nat ->(lane<6)%coq_nat ->
 VM.find 1884 old=Some(Gval(Fuint 32)instruction) ->
 (forall previous,(previous<stage)%coq_nat ->VM.find(branch_raw_node previous lane)old=Some(Gval(Fuint(branch_raw_width previous))(branch_raw_word previous instruction))) ->
 forall site,eval_hfexpr_validif_policy invalid site flat_memories(reference_immediate_expression(branch_raw_index stage lane))old old=Some(Gval(Fuint(branch_raw_width stage))(branch_raw_word stage instruction)).
Proof.
 intros Stage Lane Source Previous site.
'''
for stage,row in enumerate(nodes):
 out+=' destruct stage as[|stage].\n {\n'
 if deps[stage] is not None:out+=f' pose proof(Previous {deps[stage]}%nat ltac:(lia))as Dep.\n'
 for lane,node in enumerate(row):
  src=1884 if deps[stage]is None else nodes[deps[stage]][lane];dep='Source'if deps[stage]is None else'Dep';dw=32 if deps[stage]is None else widths[deps[stage]];word='instruction'if deps[stage]is None else words[deps[stage]]
  out+=f''' destruct lane as[|lane].
 {{ change(VM.find {src} old=Some(Gval(Fuint {dw})({word})))in {dep}.
 change(eval_hfexpr_validif_policy invalid site flat_memories reference_control_expr_{node} old old=Some(Gval(Fuint {widths[stage]})({words[stage]}))).
 cbn[reference_control_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {dep};cbn.
 repeat rewrite drop0. repeat rewrite <-take_min. cbn;reflexivity. }}
'''
 out+=' lia. }\n'
out+=' lia.\nQed.\n'
out+='''Theorem branch_raw_fields_history inputs path history limit reset time instruction lane :
 (lane<6)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1884(history time)=Some(Gval(Fuint 32)instruction) ->
 forall stage,(stage<10)%coq_nat ->VM.find(branch_raw_node stage lane)(history time)=Some(Gval(Fuint(branch_raw_width stage))(branch_raw_word stage instruction)).
Proof.
 intros Lane Resets Steps Lower Upper Source stage. induction stage using lt_wf_ind;intro Stage.
 eapply(reference_immediate_value_history (branch_raw_index stage lane) inputs path history limit reset time);[apply branch_raw_bound;assumption|exact Resets|exact Steps|exact Lower|exact Upper|].
 eapply(branch_raw_eval stage lane _ _ instruction Stage Lane Source). intros previous Before;apply H;lia.
Qed.
'''
target=p/'ReferenceConditionalBranchImmediate.v';marker='(* Branch selection and assembly. *)';old=target.read_text()if target.exists()else'';tail=old.split(marker,1)[1]if marker in old else'\n';target.write_text(out+marker+tail)
