"""Compose the actual eight-node JAL immediate assembly, using shared certificates."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration';s=(p/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.',s).group(1).split(';')))
out='''Theorem reference_jal_assembly_history inputs path history limit reset time sign middle bit low :
 size sign=1%nat ->size middle=8%nat ->size bit=1%nat ->size low=10%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 2453(history time)=Some(Gval(Fuint 1)sign) ->
 VM.find 2458(history time)=Some(Gval(Fuint 8)middle) ->
 VM.find 2369(history time)=Some(Gval(Fuint 1)bit) ->
 VM.find 2464(history time)=Some(Gval(Fuint 10)low) ->
 VM.find 2470(history time)=Some(Gval(Fuint 32)(sext_to 32(([::false]++low)++(bit++(middle++sign))))).
Proof.
 intros SignSize MiddleSize BitSize LowSize Resets Steps Lower Upper Sign Middle Bit Low.
 set(payload:=([::false]++low)++(bit++(middle++sign))).
 assert(Size:size payload=21%nat)by(unfold payload;repeat rewrite size_cat;rewrite SignSize MiddleSize BitSize LowSize;reflexivity).
'''
rows=[(2459,9,'middle++sign','rewrite Sign Middle. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(2460,10,'bit++(middle++sign)','rewrite V2459 Bit. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(2465,11,'[::false]++low','rewrite Low. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(2466,21,'payload','rewrite V2460 V2465. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(2467,1,'[::msb payload]','rewrite V2466. change(Some(Gval(Fuint 1)(drop(21-1)%nat(take 21 payload)))=Some(Gval(Fuint 1)[::msb payload])). rewrite(reference_load_sign_bit 21 payload Size(eq_refl true));reflexivity.'),(2468,1,'[::msb payload]','rewrite V2467;destruct(msb payload);reflexivity.'),(2469,11,'nseq 11(msb payload)','rewrite V2468;destruct(msb payload);reflexivity.'),(2470,32,'sext_to 32 payload','rewrite V2469 V2466. unfold eval_binop;try rewrite immediate_cat_no_absorbing. change(Some(Gval(Fuint 32)(payload++nseq 11(msb payload)))=Some(Gval(Fuint 32)(sext_to 32 payload))). unfold sext_to,sext;rewrite Size;reflexivity.')]
for n,w,word,proof in rows:
 step=f'eapply(reference_immediate_value_history {ids.index(n)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].' if n in ids else f'''rewrite(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time(S time) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
 eapply(reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes {n} reference_control_expr_{n});[exact reference_control_1_positions|exact reference_control_1_safety|exact reference_control_member_{n}| |apply Steps;lia].'''
 out+=f''' assert(V{n}:VM.find {n}(history time)=Some(Gval(Fuint {w})({word}))).
 {{ {step}
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_{n}(history time)(history time)=Some(Gval(Fuint {w})({word}))).
 cbn[reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. {proof} }}
'''
out+=' exact V2470.\nQed.\n'
target=p/'ReferenceBranchImmediate.v';old=target.read_text();marker='(* JAL assembly. *)';tail='(* Final immediate composition. *)'+old.split('(* Final immediate composition. *)',1)[1] if '(* Final immediate composition. *)' in old else '';target.write_text(old.split(marker)[0]+marker+'\nRequire Import ReferenceLoadSemantics ReferenceControlNodeCongruence1.\n'+out+tail)
