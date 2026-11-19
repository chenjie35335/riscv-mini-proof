#!/usr/bin/env python3
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/staged-integration/RFALUReferenceImmediate.v').read_text()
t=(root/'formal/flat-low/staged-integration/ReferenceImmediateTypes.v').read_text()
ids=list(map(int,re.search(r'Definition reference_immediate_ids.*?\[::(.*?)\]\.',t).group(1).split(';')))
head=s[:s.index('Definition rf_i_low_node')]
parts=[head,'Require Import RFALUReferenceImmediate ReferenceImmediatePrefix ReferenceControlStabilityHistory ReferenceControlNodeCertificates2.\n']
for upper,width,start,yes in [(False,12,2229,[2228,2227,2226]),(True,32,2521,[2520,2516,2512])]:
 name='high' if upper else 'low'
 parts.append(f'Definition alu_i_{name}_raw lane :VarOrder.T:=nth 0[::'+ ';'.join(map(str,yes))+']lane.\n')
 parts.append(f'''Lemma alu_i_{name}_prefix inputs path history limit reset time word lane :(lane<3)%coq_nat ->size word={width}%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists v,VM.find 1884(history t)=Some v /\\ type_of_val v=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall n,(n<3)%coq_nat ->VM.find(nth 0[::2096;2092;2088]n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->
 VM.find(alu_i_{name}_raw lane)(history time)=Some(Gval(Fuint {width})word) ->
 VM.find {start+2}(history time)=Some(Gval(Fuint {width})word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Guards Raw.
''')
 for selected in range(3):
  parts.append('destruct lane as[|lane]. {\n')
  for n in range(selected,3):
   node=start+n;guard=[2096,2092,2088][n];other=(start+n-1 if n==selected else yes[n])
   parts.append(f'assert(V{n}:VM.find {node}(history time)=Some(Gval(Fuint {width})word)).\n{{ eapply(reference_immediate_value_history {ids.index(node)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.\n')
   parts.append(f'pose proof(Guards {n}%nat ltac:(lia))as Guard.\n')
   if n==0:
    parts.append(f'cbn[reference_immediate_expression reference_immediate_expressions nth reference_control_expr_{node} eval_hfexpr_validif_policy eval_href_validif_policy].\nchange(VM.find {guard}(history time)=Some(Gval(Fuint 1)[::true]))in Guard.\nchange(VM.find {yes[n]}(history time)=Some(Gval(Fuint {width})word))in Raw.\nrewrite Guard;cbn;rewrite Raw. apply dut_decode_adapt;exact Size. }}\n')
   else:
    parts.append(f'destruct(reference_immediate_types_history _ history limit 200 Steps Source {ids.index(other)}%nat ltac:(lia)time ltac:(cbv[reference_immediate_rank reference_immediate_ranks nth];lia)ltac:(lia))as[other[Other Shape]].\n')
    parts.append(f'change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_{node}(history time)(history time)=Some(Gval(Fuint {width})word)).\n')
    bit='true' if n==selected else 'false'
    val='Raw' if n==selected else f'V{n-1}'
    parts.append(f'eapply(immediate_selected_mux _ _ _ _ _ _ _ word other {bit});[exact Size|exact Guard|exact {val}|exact Other|exact Shape]. }}\n')
  parts.append('exact V2. }\n')
 parts.append('lia. Qed.\n')
 # Suffix pass-through, with enabled output stages identical to original.
 chunk=s[s.index(f'Lemma rf_i_{name}_selected'):]
 chunk=chunk[:chunk.index('Qed.')+4]
 chunk=chunk.replace(f'rf_i_{name}_selected',f'alu_i_{name}_suffix').replace('word lane :(lane<3)%coq_nat ->','word :')
 chunk=chunk.replace('Nat.eqb n lane','false').replace(f'(rf_i_{name}_yes lane)',f' {start+2}').replace('intros Lane Size','intros Size')
 a=chunk.index(' eapply(immediate_stable_mux_suffix');b=chunk.index(' assert(Gate:',a)
 count=27 if upper else 15;prefix=start+2
 chunk=chunk[:a]+f''' eapply(immediate_stable_mux_prefix (formal_invalid_policy inputs path)(history time){count} {width} word {prefix} rf_i_{name}_node rf_i_{name}_guard rf_i_{name}_yes);[exact Size| |exact Guards| |exact Raw|lia].
 - intros n Bound value Eval. exact(rf_i_{name}_value n inputs path history limit reset time value Bound Resets Steps Lower Upper Eval).
 - intros n Bound. exact(proj1(rf_i_{name}_types n _ history limit time Bound Steps Source Lower ltac:(lia))). }}
'''+chunk[b:]
 parts.append(chunk+'\n')
raw=s[s.index('Lemma rf_i_raw'):s.index('Lemma rf_i_sign')]
raw=raw.replace('rf_i_raw','alu_i_raw').replace('rf_i_low_yes','alu_i_low_raw')
for a,b in [(2225,2228),(2224,2227),(2223,2226)]:raw=raw.replace(str(a),str(b))
for a,b in [(38,41),(37,40),(36,39)]:raw=raw.replace('value_history '+str(a),'value_history '+str(b))
parts.append(raw)
sign=s[s.index('Lemma rf_i_sign'):s.index('Theorem rf_i_immediate_history')]
sign=sign.replace('rf_i_sign','alu_i_sign').replace('rf_i_high_yes','alu_i_high_raw')
for a in range(2497,2509):sign=sign.replace(str(a),str(a+12))
for a in [260,261,262,263,264,265]:sign=sign.replace('value_history '+str(a)+' ', 'value_history '+str(a+6)+' ')
parts.append(sign)
hist=s[s.index('Theorem rf_i_immediate_history'):s.index('Require Import ReferenceIllegalObserved')]
hist=hist.replace('rf_i_immediate_history','alu_i_immediate_history').replace('Nat.eqb n lane','false')
needle=' (forall n,(n<15)%coq_nat'
hist=hist.replace(needle,' (forall n,(n<3)%coq_nat ->VM.find(nth 0[::2096;2092;2088]n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n lane])) ->\n'+needle)
hist=hist.replace('Enabled LowGuards','Enabled PrefixGuards LowGuards').replace('rf_i_raw','alu_i_raw').replace('rf_i_sign','alu_i_sign')
a=hist.index(' pose proof(rf_i_low_selected');b=hist.index(' pose proof(alu_i_sign',a)
hist=hist[:a]+""" pose proof(alu_i_low_prefix inputs path history limit reset time(drop 20(take 32 instruction))lane Lane RawSize Resets Steps Typed Lower Upper PrefixGuards Raw)as PrefixLow.
 pose proof(alu_i_low_suffix inputs path history limit reset time(drop 20(take 32 instruction))RawSize Resets Steps Typed Lower Upper Enabled LowGuards PrefixLow)as Low.
"""+hist[b:]
a=hist.index(' exact(rf_i_high_selected')
hist=hist[:a]+""" pose proof(alu_i_high_prefix inputs path history limit reset time(load_i_immediate instruction)lane Lane(load_i_immediate_size instruction Size)Resets Steps Typed Lower Upper PrefixGuards Sign)as PrefixHigh.
 exact(alu_i_high_suffix inputs path history limit reset time(load_i_immediate instruction)(load_i_immediate_size instruction Size)Resets Steps Typed Lower Upper Enabled HighGuards PrefixHigh).
Qed.
"""
parts.append(hist)
parts.append(s[s.index('Require Import ReferenceIllegalObserved'):s.index('Lemma rf_bitwise_reference_enabled')])
for kind,count in [('low',15),('high',27)]:
 parts.append(f"""Lemma alu_i_{kind}_decode instruction lane n :(lane<3)%coq_nat ->(n<{count})%coq_nat ->
 N.land(to_N instruction)(reference_instruction_mask lane)=reference_instruction_code lane ->
 N.eqb(reference_instruction_code(rf_i_{kind}_decoder n))(N.land(to_N instruction)(reference_instruction_mask(rf_i_{kind}_decoder n)))=false.
Proof. intros Lane Bound Match.
 rewrite(rf_reference_decode_onehot instruction lane(rf_i_{kind}_decoder n)ltac:(lia)ltac:(do {count}(destruct n as[|n];[vm_compute;lia|]);lia)Match).
 do 3(destruct lane as[|lane];[do {count}(destruct n as[|n];[reflexivity|]);lia|]);lia.
Qed.
""")
obs=s[s.index('Theorem rf_bitwise_immediate_observed'):]
obs=obs.replace('rf_bitwise_immediate_observed','reference_alu_i_immediate_active_observed').replace('(Nat.add 3 lane)',' lane')
obs=obs.replace(' (lane<3)%coq_nat ->',' VM.find 1707(top_environment observed)=Some(Gval(Fuint 1)[::true]) ->\n (lane<3)%coq_nat ->',1)
obs=obs.replace('intros Observe Legal Reset Lane Instruction Match.','intros Observe Legal Reset Enabled Lane Instruction Match.')
a=obs.index(' assert(Enabled:');b=obs.index(' destruct(observed_joint_register_concrete',a);obs=obs[:a]+obs[b:]
obs=obs.replace('Nat.eqb n lane','false')
obs=obs.replace('rf_i_low_decode instruction','alu_i_low_decode instruction').replace('rf_i_high_decode instruction','alu_i_high_decode instruction')
a=obs.index(' assert(Low:')
obs=obs[:a]+""" assert(Prefix:forall n,(n<3)%coq_nat ->VM.find(nth 0[::2096;2092;2088]n)(history 9250%nat)=Some(Gval(Fuint 1)[::Nat.eqb n lane])).
 { intros n Bound. assert(Id:nth 0[::2096;2092;2088]n=reference_instruction_guard n)by(do 3(destruct n as[|n];[reflexivity|]);lia).
 rewrite Id(Decode n ltac:(lia))(rf_reference_decode_onehot instruction lane n ltac:(lia)ltac:(lia)Match);reflexivity. }
"""+obs[a:]
obs=obs.replace('rf_i_immediate_history','alu_i_immediate_history').replace('))Low High)', '))Prefix Low High)')
parts.append(obs)
(root/'formal/flat-low/staged-integration/ReferenceALUIImmediate.v').write_text('\n'.join(parts))
