from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
expr=dict((int(n),e)for n,e in re.findall(r'Definition reference_control_expr_(\d+) := (.*)\.',(p/'ReferenceControlExpressions.v').read_text()))
rs1=[2074,2070,2066,2032,2027,2017];rs2=[2587,2586,2584];nodes=[]
def add(n):
 if n==1884 or n in nodes:return
 for d in map(int,re.findall(r'Eid VarOrder.T (\d+)',expr[n])):add(d)
 nodes.append(n)
for n in rs1+rs2:add(n)
base=(p/'RFCompareReferencePorts.v').read_text();s=base[:base.index('Definition rf_compare_port_nodes')].replace('RFCompareCycle','RFShiftCycle')
s+='Definition rf_shift_rs1_target immediate lane:=if immediate then Nat.add 3 lane else nth 0%nat[::12%nat;13%nat;15%nat]lane.\nDefinition rf_shift_rs2_target lane:=nth 0%nat[::3%nat;4%nat;6%nat]lane.\n'
s+='Definition rf_shift_rs1_source immediate lane :VarOrder.T:=if immediate then nth 0[::2074;2070;2066]lane else nth 0[::2032;2027;2017]lane.\nDefinition rf_shift_rs2_source lane :VarOrder.T:=nth 0[::2587;2586;2584]lane.\n'
s+='Definition rf_shift_port_nodes :seq VarOrder.T:=[::'+';'.join(map(str,nodes))+'].\nDefinition rf_shift_port_expr n:=nth (@Econst VarOrder.T(Fuint 1)[::false])[::'+';'.join('reference_control_expr_'+str(n)for n in nodes)+']n.\n'
helper=base[base.index('Lemma rf_compare_port_value'):base.index('Theorem rf_compare_port_slices')]
a=helper.index('destruct n as[|n].');helper=helper[:a].replace('rf_compare','rf_shift').replace('(n<8)',f'(n<{len(nodes)})')
s+=helper
for n in nodes:
 g=0 if n<2500 else 2
 s+=f'''destruct n as[|n]. {{ change(VM.find {n}(history time)=Some(Gval(Fuint width)word)).
rewrite(reference_control_stable_{n}_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
eapply(reference_redirect_ground_step reference_control_{g}_offsets reference_control_{g}_nodes {n} reference_control_expr_{n});[exact reference_control_{g}_positions|exact reference_control_{g}_safety|exact reference_control_member_{n}|exact Eval|apply Steps;lia]. }}
'''
s+='lia. Qed.\nTheorem rf_shift_port_slices inputs path history limit reset time instruction immediate lane :\n (lane<3)%coq_nat ->\n'
s+=base[base.index(' (forall t,(t<=limit)',base.index('Theorem rf_compare_port_slices')):base.index(' VM.find(if unsigned',base.index('Theorem rf_compare_port_slices'))]
s+=' VM.find(rf_shift_rs1_source immediate lane)(history time)=Some(Gval(Fuint 5)(rf_instruction_address false instruction)) /\\\n VM.find(rf_shift_rs2_source lane)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).\nProof.\n intros Lane Resets Steps Lower Upper Source.\n'
vals={1884:'instruction'}
for n in nodes:
 d=int(re.search(r'Eid VarOrder.T (\d+)',expr[n])[1]);hi,lo=map(int,re.search(r'Uextr (\d+) (\d+)',expr[n]).groups());v=f'drop {lo}(take {hi+1}({vals[d]}))';vals[n]=v
 s+=f'''assert(V{n}:VM.find {n}(history time)=Some(Gval(Fuint {hi-lo+1})({v}))).
{{ eapply(rf_shift_port_value {nodes.index(n)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
cbn[rf_shift_port_expr nth reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {'Source'if d==1884 else 'V'+str(d)}. reflexivity. }}
'''
s+='unfold rf_instruction_address. rewrite !drop0 !take_take in '+','.join('V'+str(n)for n in rs1+rs2)+';try reflexivity.\ndestruct immediate;do 3(destruct lane as[|lane];[split;assumption|]);lia.\nQed.\n'
# rs1 copied generic suffix
part=base[base.index('Theorem rf_compare_rs1_history'):base.index('Theorem rf_compare_rs2_history')]
part=part.replace('rf_compare','rf_shift').replace('instruction unsigned','instruction immediate lane').replace(':size instruction',':(lane<3)%coq_nat ->size instruction').replace('(if unsigned then 8%nat else 7%nat)','(rf_shift_rs1_target immediate lane)').replace('((if unsigned then 8 else 7)<42)','(rf_shift_rs1_target immediate lane<42)').replace('intros Size','intros Lane Size').replace('instruction immediate lane Resets','instruction immediate lane Lane Resets').replace('destruct unsigned;vm_compute;lia','destruct immediate;do 3(destruct lane as[|lane];[vm_compute;lia|]);lia').replace('destruct unsigned;exact Raw','destruct immediate;do 3(destruct lane as[|lane];[exact Raw|]);lia')
s+=part
# rs2 use suffix directly instead of compare prefix
s+='''Theorem rf_shift_rs2_history inputs path history limit reset time instruction lane :
 (lane<3)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<24)%coq_nat ->VM.find(rf_alu_rs2_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(rf_shift_rs2_target lane)])) ->
 VM.find 2622(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards.
 assert(Typed:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\\type_of_val v=Gtyp(Fuint 32)).
 { intros t L U. exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }
 pose proof(proj2(rf_shift_port_slices inputs path history limit reset time instruction false lane Lane Resets Steps Lower Upper(Source time ltac:(lia)ltac:(lia))))as Raw.
 assert(Selected:VM.find 2620(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 { change(VM.find(rf_alu_rs2_node 23)(history time)=Some(Gval(Fuint 5)(rf_instruction_address true instruction))).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history(S time))24 (rf_shift_rs2_target lane) 5(rf_instruction_address true instruction)2596 rf_alu_rs2_node rf_alu_rs2_guard rf_alu_rs2_yes);[ltac:(do 3(destruct lane as[|lane];[vm_compute;lia|]);lia)|exact(rf_instruction_address_size true instruction Size)| | |exact Guards| | |ltac:(do 3(destruct lane as[|lane];[exact Raw|]);lia)|ltac:(do 3(destruct lane as[|lane];[vm_compute;lia|]);lia)|lia].
 - intros n Bound. exact(rf_alu_rs2_same n inputs path history limit reset time Bound Resets Steps Lower Upper).
 - intros n Bound value Eval. apply(rf_alu_rs2_step n _ _ _ value Bound Eval);apply Steps;exact Upper.
 - intros n Bound. exact(proj1(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))).
 - intros n Bound. exact(proj2(rf_alu_rs2_types n _ history limit time Bound Steps Typed Lower ltac:(lia))). }
'''
start=base.index(' assert(Gate:VM.find 2621',base.index('Theorem rf_compare_rs2_history'));end=base.index('Require Import ObservedJointRegisterConcrete',start)
s+=base[start:end]
# observed and bank API
s+='''Require Import ObservedJointRegisterConcrete LoadTypeCorrespondence ReferenceSecondRegisterRead ReferenceLoadRs1 ReferenceRegisterRead.
Theorem rf_shift_index_observed second memory inputs k observed instruction immediate lane :
 generated_observe memory inputs k=Some observed ->generated_legal_trace memory inputs k ->
 VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 7750(top_environment observed)=Some(Gval(Fuint 32)instruction) ->
 (lane<3)%coq_nat ->(second=true ->immediate=false) ->
 N.land(to_N instruction)(reference_instruction_mask(rf_shift_class immediate lane))=reference_instruction_code(rf_shift_class immediate lane) ->
 VM.find(if second then 2622 else 2145)(top_environment observed)=Some(Gval(Fuint 5)(rf_instruction_address second instruction)).
Proof.
 intros Observe Legal Enabled Instruction Lane Kind Match.
 destruct(rf_reference_operand_context memory inputs k observed instruction(rf_shift_class immediate lane)Observe Legal Enabled Instruction(rf_shift_class_bound immediate lane Lane)Match)
 as[Size[reset[history[Last[Resets[Steps[Source[Enable Decode]]]]]]]].
 destruct second.
 - specialize(Kind(Logic.eq_refl true));subst immediate.
 pose proof(rf_shift_rs2_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable ltac:(intros n Bound;unfold rf_alu_rs2_guard;rewrite(Decode(rf_alu_rs2_decoder n)ltac:(do 24(destruct n as[|n];[cbn[rf_alu_rs2_decoder nth];lia|]);lia));do 3(destruct lane as[|lane];[do 24(destruct n as[|n];[reflexivity|]);lia|]);lia))as Value.
 rewrite(reference_control_stable_2622_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
 - pose proof(rf_shift_rs1_history (generated_observation_input inputs k)nil history 9259 reset 9250 instruction immediate lane Lane Size Resets Steps Source ltac:(vm_compute;lia)ltac:(vm_compute;lia)Enable ltac:(intros n Bound;unfold rf_alu_rs1_guard;rewrite(Decode(rf_alu_rs1_decoder n)ltac:(do 42(destruct n as[|n];[cbn[rf_alu_rs1_decoder nth];lia|]);lia));destruct immediate;do 3(destruct lane as[|lane];[do 42(destruct n as[|n];[reflexivity|]);lia|]);lia))as Value.
 rewrite(reference_control_stable_2145_history (generated_observation_input inputs k)nil history 9259 reset Resets Steps 9250 9259 ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia)ltac:(vm_compute;lia))Last in Value. exact Value.
Qed.
'''
part=base[base.index('Theorem rf_compare_bank_observed'):].replace('rf_compare','rf_shift').replace('instruction unsigned','instruction immediate lane').replace('((rf_shift_class unsigned))','(rf_shift_class immediate lane)').replace(' rf_reference_bank_at',' (lane<3)%coq_nat ->(second=true ->immediate=false) ->\n rf_reference_bank_at').replace('intros Observe Legal Enabled Instruction Match Bank.','intros Observe Legal Enabled Instruction Match Lane Kind Bank.').replace('Observe Legal Enabled Instruction Match)as Index','Observe Legal Enabled Instruction Lane Kind Match)as Index')
s+=part
(p/'RFShiftReferencePorts.v').write_text(s)
