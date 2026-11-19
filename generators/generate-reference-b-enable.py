"""Finish the four shared field outputs after the six-way mux."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration';s=(p/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.',s).group(1).split(';')))
out='''Definition branch_field_output group : VarOrder.T :=nth 0 [::2331;2369;2384;2399]group.
Theorem branch_field_output_history group lane inputs path history limit reset time instruction :
 (group<4)%coq_nat ->(lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 VM.find(branch_field_output group)(history time)=Some(Gval(Fuint(branch_field_width group))(branch_field_word group instruction)).
Proof.
 intros Group Lane Size Resets Steps Source Lower Upper Enabled Guards.
 pose proof(branch_field_mux_history group lane inputs path history limit reset time instruction Group Lane Size Resets Steps Source Lower Upper Guards)as Final.
 pose proof(branch_field_size group instruction Group Size)as WordSize.
'''
for group,(node,width,word)in enumerate([(2330,1,'drop 31(take 32 instruction)'),(2368,1,'drop 7(take 8 instruction)'),(2383,6,'drop 25(take 31 instruction)'),(2398,4,'drop 8(take 12 instruction)')]):
 out+=f''' destruct group as[|group].
 {{ change(VM.find {node-1}(history time)=Some(Gval(Fuint {width})({word})))in Final.
 assert(Value:VM.find {node}(history time)=Some(Gval(Fuint {width})({word}))).
 {{ eapply(reference_immediate_value_history {ids.index(node)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_{node}(history time)(history time)=Some(Gval(Fuint {width})({word}))).
 cbn[reference_control_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint {width})({word}))(Gtyp(Fuint {width}))=Some(Gval(Fuint {width})({word}))). apply dut_decode_adapt;exact WordSize. }}
 eapply(reference_immediate_value_history {ids.index(node+1)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact Value. }}
'''
out+=' lia.\nQed.\n'
target=p/'ReferenceConditionalBranchImmediate.v';old=target.read_text();marker='(* Branch field enable. *)';end='(* Parameterized branch assembly. *)';tail=end+old.split(end,1)[1]if end in old else'';base=old.split(marker)[0]if marker in old else old.split(end)[0];target.write_text(base+marker+'\n'+out+tail)
