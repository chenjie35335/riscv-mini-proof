"""Compose actual JAL fields using the shared immediate history certificate."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration'
s=(p/'ReferenceImmediateTypes.v').read_text()
ids=list(map(int,re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.',s).group(1).split(';')))
words={2360:(1,'drop 20(take 21 instruction)'),2450:(1,'drop 31(take 32 instruction)'),2455:(8,'drop 12(take 20 instruction)'),2461:(10,'drop 21(take 31 instruction)')}
rows=[(2361,2360,2357,'mux')]+[(n,n-1,g,'fallback')for n,g in zip(range(2362,2368),[2004,1998,1992,1986,1980,1974])]+[(2368,2367,1707,'mux'),(2369,2368,0,'wire'),(2451,2450,2357,'mux'),(2452,2451,1707,'mux'),(2453,2452,0,'wire'),(2456,2455,2357,'mux'),(2457,2456,1707,'mux'),(2458,2457,0,'wire'),(2462,2461,2357,'mux'),(2463,2462,1707,'mux'),(2464,2463,0,'wire')]
for n,src,g,kind in rows:words[n]=words[src]
out='''Theorem reference_jal_selected_fields_history inputs path history limit reset time instruction :
 size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2357(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall guard,List.In guard [::2004;1998;1992;1986;1980;1974] ->VM.find guard(history time)=Some(Gval(Fuint 1)[::false])) ->
'''
out+=' /\\\n '.join(f'VM.find {n}(history time)=Some(Gval(Fuint {words[n][0]})({words[n][1]}))'for n in[2369,2453,2458,2464])+'.\nProof.\n intros Size Resets Steps Source Lower Upper Enabled Jal Branch.\n'
out+=' destruct(reference_jal_raw_fields_history inputs path history limit reset time instruction Resets Steps Lower Upper ltac:(apply Source;lia))as[V2360[V2450[V2455 V2461]]].\n'
out+=' assert(TypedSource:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\\type_of_val value=Gtyp(Fuint 32)).\n { intros t L U;exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }\n'
for n,src,g,kind in rows:
 w,word=words[n]
 out+=f' assert(V{n}:VM.find {n}(history time)=Some(Gval(Fuint {w})({word}))).\n {{ eapply(reference_immediate_value_history {ids.index(n)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].\n intro site. change(eval_hfexpr_validif_policy (isolated_validif_policy(formal_invalid_policy inputs path)) site flat_memories reference_control_expr_{n} (history time)(history time)=Some(Gval(Fuint {w})({word}))).\n'
 if kind=='fallback':
  yes=2355-4*(n-2362)
  out+=f''' destruct(reference_immediate_typed_history {ids.index(yes)} _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find {yes}(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 1))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ ({word}) other false);[rewrite size_drop size_take Size;reflexivity|apply Branch;vm_compute;tauto|exact V{src}|exact Other|exact Typed]. }}
'''
 elif kind=='wire':out+=f' exact V{src}. }}\n'
 else:
  out+=f''' cbn[reference_control_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite {'Jal' if g==2357 else 'Enabled'};cbn;rewrite V{src}.
 change(adapt_hvalue_as_type(Gval(Fuint {w})({word}))(Gtyp(Fuint {w}))=Some(Gval(Fuint {w})({word}))). apply dut_decode_adapt. rewrite size_drop size_take Size;reflexivity. }}
'''
out+=' repeat split;assumption.\nQed.\n'
target=p/'ReferenceBranchImmediate.v';old=target.read_text();marker='(* Selected JAL fields. *)';tail='(* JAL assembly. *)'+old.split('(* JAL assembly. *)',1)[1] if '(* JAL assembly. *)' in old else '';target.write_text(old.split(marker)[0]+marker+'\n'+out+tail)
