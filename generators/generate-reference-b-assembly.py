"""A single parameterized eight-node B assembly certificate (six decode lanes)."""
from pathlib import Path
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration'
rows=[[2370,2385,2400,2401,2402,2403,2404,2405]]+[list(range(2406+8*l,2414+8*l))for l in range(5)]
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='Require Import ReferenceControlNodeCongruence1 ReferenceControlNodeCertificates1 ReferenceControlStabilityHistory ReferenceRedirectSpine ReferenceLoadSemantics.\n'
out+=f'Definition branch_assembly_node lane stage : VarOrder.T :=nth 0(nth [::]{seq([seq(r)for r in rows])}lane)stage.\n'
ref=lambda n:f'(@Eref VarOrder.T (@Eid VarOrder.T {n}))'
node=lambda n:ref(f'(branch_assembly_node lane {n})')
cat=lambda a,b:f'(@Eprim_binop VarOrder.T Bcat {a} {b})'
expr=[cat(ref(2331),ref(2369)),cat(node(0),ref(2384)),cat(ref(2399),'(@Econst VarOrder.T (Fuint 1)[::false])'),cat(node(1),node(2)),f'(@Eprim_unop VarOrder.T(Uextr 12 12){node(3)})',f'(@Eprim_unop VarOrder.T(Uextr 0 0){node(4)})',f'(@Emux VarOrder.T {node(5)} (@Econst VarOrder.T(Fuint 19)(nseq 19 true))(@Econst VarOrder.T(Fuint 19)(nseq 19 false)))',cat(node(6),node(3))]
out+=f'Definition branch_assembly_expression lane stage :=nth (@Econst VarOrder.T(Fuint 1)[::false]){seq(expr)}stage.\n'
out+='''Lemma branch_assembly_member lane stage : (lane<6)%coq_nat ->(stage<8)%coq_nat ->
 List.In(branch_assembly_node lane stage,branch_assembly_expression lane stage)reference_control_1_nodes.
Proof.
'''
for row in rows:
 out+=' destruct lane as[|lane].\n {\n'
 for n in row:out+=f' destruct stage as[|stage];[intros;exact reference_control_member_{n}|].\n'
 out+=' lia. }\n'
out+=' lia.\nQed.\n'
out+='''Lemma branch_assembly_stable lane stage inputs path history limit reset time :
 (lane<6)%coq_nat ->(stage<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find(branch_assembly_node lane stage)(history time)=VM.find(branch_assembly_node lane stage)(history(S time)).
Proof.
 intros Lane Stage Resets Steps Lower Upper.
'''
for row in rows:
 out+=' destruct lane as[|lane].\n {\n'
 for n in row:out+=f' destruct stage as[|stage];[exact(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia))|].\n'
 out+=' lia. }\n'
out+=' lia.\nQed.\n'
out+='''Theorem branch_assembly_value lane stage inputs path history limit reset time width word :
 (lane<6)%coq_nat ->(stage<8)%coq_nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(branch_assembly_expression lane stage)(history time)(history time)=Some(Gval(Fuint width)word)) ->
 VM.find(branch_assembly_node lane stage)(history time)=Some(Gval(Fuint width)word).
Proof.
 intros Lane Stage Resets Steps Lower Upper Eval.
 rewrite(branch_assembly_stable lane stage inputs path history limit reset time Lane Stage Resets Steps Lower Upper).
 eapply(reference_redirect_ground_step reference_control_1_offsets reference_control_1_nodes _ (branch_assembly_expression lane stage));[exact reference_control_1_positions|exact reference_control_1_safety|apply branch_assembly_member;assumption|exact Eval|apply Steps;lia].
Qed.
Theorem branch_assembly_history lane inputs path history limit reset time sign bit high low :
 (lane<6)%coq_nat ->size sign=1%nat ->size bit=1%nat ->size high=6%nat ->size low=4%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 2331(history time)=Some(Gval(Fuint 1)sign) ->VM.find 2369(history time)=Some(Gval(Fuint 1)bit) ->
 VM.find 2384(history time)=Some(Gval(Fuint 6)high) ->VM.find 2399(history time)=Some(Gval(Fuint 4)low) ->
 VM.find(branch_assembly_node lane 7)(history time)=Some(Gval(Fuint 32)(sext_to 32(([::false]++low)++(high++(bit++sign))))).
Proof.
 intros Lane SignSize BitSize HighSize LowSize Resets Steps Lower Upper Sign Bit High Low.
 set(payload:=([::false]++low)++(high++(bit++sign))).
 assert(Size:size payload=13%nat)by(unfold payload;repeat rewrite size_cat;rewrite SignSize BitSize HighSize LowSize;reflexivity).
'''
vals=[(2,'bit++sign','rewrite Sign Bit. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(8,'high++(bit++sign)','rewrite V0 High. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(5,'[::false]++low','rewrite Low. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(13,'payload','rewrite V1 V2. unfold eval_binop;try rewrite immediate_cat_no_absorbing;reflexivity.'),(1,'[::msb payload]','rewrite V3. change(Some(Gval(Fuint 1)(drop(13-1)%nat(take 13 payload)))=Some(Gval(Fuint 1)[::msb payload])). rewrite(reference_load_sign_bit 13 payload Size(eq_refl true));reflexivity.'),(1,'[::msb payload]','rewrite V4;destruct(msb payload);reflexivity.'),(19,'nseq 19(msb payload)','rewrite V5;destruct(msb payload);reflexivity.'),(32,'sext_to 32 payload','rewrite V6 V3. unfold eval_binop;try rewrite immediate_cat_no_absorbing. change(Some(Gval(Fuint 32)(payload++nseq 19(msb payload)))=Some(Gval(Fuint 32)(sext_to 32 payload))). unfold sext_to,sext;rewrite Size;reflexivity.')]
for stage,(width,word,proof)in enumerate(vals):
 out+=f''' assert(V{stage}:VM.find(branch_assembly_node lane {stage})(history time)=Some(Gval(Fuint {width})({word}))).
 {{ eapply(branch_assembly_value lane {stage} inputs path history limit reset time);[exact Lane|lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[branch_assembly_expression nth eval_hfexpr_validif_policy eval_href_validif_policy]. {proof} }}
'''
out+=' exact V7.\nQed.\n'
target=p/'ReferenceConditionalBranchImmediate.v';old=target.read_text();marker='(* Parameterized branch assembly. *)';tail='(* Final branch composition. *)'+old.split('(* Final branch composition. *)',1)[1]if'(* Final branch composition. *)'in old else'';target.write_text(old.split(marker)[0]+marker+'\n'+out+tail)
