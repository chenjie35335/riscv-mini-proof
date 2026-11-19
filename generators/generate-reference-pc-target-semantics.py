"""Arithmetic and mux semantics of the 41 actual reference PC target nodes."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';src=(p/'ReferencePCTargetStability.v').read_text();line=src.split('Definition ref_pc_target_nodes')[1].split('\n')[0];nodes=[]
for m in re.finditer(r'\((\d+),\(@',line):
 n=int(m[1]);a=m.end()-2;d=0
 for b in range(a,len(line)):
  d+=(line[b]=='(')-(line[b]==')')
  if not d:break
 nodes.append((n,line[a:b+1]))
assert len(nodes)==41
cuts=[int(x)for x in re.search(r'Definition ref_pc_target_cuts :.*?\[::(.*?)\]',src)[1].split(';')];guards=[x for x in cuts if x not in [2812,2552,2209]]
word={2812:'pc',2552:'immediate',2209:'rs1'};width={2812:32,2552:32,2209:32};exprs={};kinds={};deps={}
for n,e in nodes:
 ds=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',e)));deps[n]=ds
 if '(@Emux' in e:
  c,y,z=ds;value=f'if guards {c} then {word[y]} else {word[z]}';w=32;kind='mux'
 elif 'Badd' in e:value=f'from_N 33(to_N {word[ds[0]]}+to_N {word[ds[1]]})';w=33;kind='add'
 elif '(Utail 1)' in e:value=f'take 32 {word[ds[0]]}';w=32;kind='tail'
 elif '(Uextr 31 1)' in e:value=f'drop 1(take 32 {word[ds[0]]})';w=31;kind='extract'
 elif 'Bcat' in e:value=f'[::false]++{word[ds[0]]}';w=32;kind='cat'
 elif '(@Eref' in e:value=word[ds[0]];w=32;kind='alias'
 else:raise ValueError(e)
 exprs[n]=value;width[n]=w;word[n]=f'w{n}';kinds[n]=kind
head='''Require Import CoreSocModel ComparisonNodes ReferencePCTargetStability ReferencePCTargetEquations ReferenceRedirectSpine.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma ref_pc_target_resize32 word :size word=32%nat ->zext_to 32(take 32 word)=word.
Proof. intro Size. assert(Take:take 32 word=word)by(rewrite <-Size;apply take_size).
 rewrite Take. unfold zext_to,zext. rewrite Size subnn cats0. reflexivity. Qed.
'''
s=head+'Definition reference_pc_target_value (guards:VarOrder.T->bool) pc immediate rs1 :=\n'
for n,e in nodes:s+=f' let w{n} := {exprs[n]} in\n'
s+=' w6508.\nDefinition reference_pc_target_guard_nodes :seq VarOrder.T := [::'+';'.join(map(str,guards))+'].\n'
s+='''Theorem reference_pc_target_semantics inputs path history limit reset time guards pc immediate rs1 :
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (225<=time)%coq_nat ->(time<limit)%coq_nat ->size pc=32%nat ->size rs1=32%nat ->
 VM.find 2812(history time)=Some(Gval(Fuint 32)pc) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)immediate) ->
 VM.find 2209(history time)=Some(Gval(Fuint 32)rs1) ->
 (forall node,List.In node reference_pc_target_guard_nodes ->VM.find node(history time)=Some(Gval(Fuint 1)[::guards node])) ->
 VM.find 6508(history time)=Some(Gval(Fuint 32)(reference_pc_target_value guards pc immediate rs1)).
Proof.
 intros Resets Steps Lower Upper PCSize Rs1Size PC Immediate Rs1 Guards.
'''
lookup={2812:'PC',2552:'Immediate',2209:'Rs1'};sizes={2812:'PCSize',2209:'Rs1Size'}
for i,(n,e) in enumerate(nodes):
 s+=f' set(w{n}:={exprs[n]}).\n'
 if kinds[n] in ['mux','tail','extract','cat','alias']:
  s+=f' assert(Size{n}:size w{n}={width[n]}%nat).\n {{ unfold w{n}. '
  k=kinds[n];ds=deps[n]
  if k=='mux':s+=f'destruct(guards {ds[0]});[exact {sizes[ds[1]]}|exact {sizes[ds[2]]}].'
  elif k=='tail':s+=f'rewrite size_take {sizes[ds[0]]};reflexivity.'
  elif k=='extract':s+=f'rewrite size_drop size_take {sizes[ds[0]]};reflexivity.'
  elif k=='cat':s+=f'rewrite size_cat {sizes[ds[0]]};reflexivity.'
  else:s+=f'exact {sizes[ds[0]]}.'
  s+=' }\n'
 else:s+=f' assert(Size{n}:size w{n}=33%nat)by(unfold w{n};rewrite size_from_N;reflexivity).\n'
 sizes[n]=f'Size{n}'
 s+=f' assert(V{n}:VM.find {n}(history time)=Some(Gval(Fuint {width[n]})w{n})).\n {{ destruct(reference_pc_target_equation inputs path history limit reset time {i}%nat Resets Steps Lower Upper ltac:(lia))as[site E].\n'
 s+=f' change(VM.find {n}(history time)=eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories {e} (history time)(history time))in E.\n rewrite E. cbn[eval_hfexpr_validif_policy eval_href_validif_policy].\n'
 if kinds[n]=='mux':
  c,y,z=deps[n];s+=f' rewrite(Guards {c} ltac:(vm_compute;tauto)). destruct(guards {c});cbn[is_zero];rewrite {lookup[y]} {lookup[z]};unfold eval_type_of_expr;cbn[type_of_expr\' eval_type_of_ref];rewrite ?{lookup[y]} ?{lookup[z]}.\n'
  s+=f' - change(Some(Gval(Fuint 32)(zext_to 32(take 32 {word[y]})))=Some(Gval(Fuint 32){word[y]})). rewrite(ref_pc_target_resize32 _ {sizes[y]});reflexivity.\n'
  s+=f' - change(Some(Gval(Fuint 32)(zext_to 32(take 32 {word[z]})))=Some(Gval(Fuint 32){word[z]})). rewrite(ref_pc_target_resize32 _ {sizes[z]});reflexivity.\n'
 else:
  s+=' rewrite '+' '.join(lookup[d]for d in deps[n])+'. reflexivity.\n'
 s+=' }\n';lookup[n]=f'V{n}'
s+=' exact V6508.\nQed.\n';(p/'ReferencePCTargetSemantics.v').write_text(s)
