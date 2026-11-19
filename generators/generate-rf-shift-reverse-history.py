from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
src=(p/'RFShiftNodes.v').read_text()
expr=dict((int(n),e) for n,e in re.findall(r'Definition rf_shift_expr_(\d+) := (.*)\.',src))
head='''Require Import RFShiftNodes RFShiftNodeStep RFShiftReverse CoreSocModel ComparisonNodes.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for first,source in [(1173,1151),(1230,1229)]:
 words={source:'word'};width={source:32};rank={source:0};deps={};defs=[]
 for n in range(first,first+49):
  e=expr[n];ds=list(map(int,re.findall(r'Eid VarOrder.T (\d+)',e)));deps[n]=ds
  rank[n]=1+max([rank[d] for d in ds] or [0])
  if not ds:v='zeros 16++ones 16';w=32
  elif 'Bxor' in e:
   v=f'xorB '+(' (ones 32)' if len(ds)==1 else words[ds[0]])+' '+words[ds[-1]];w=32
  elif 'Band' in e or 'Bor' in e:
   v=('andB' if 'Band' in e else 'orB')+' '+words[ds[0]]+' '+words[ds[1]];w=max(width[d]for d in ds)
  elif 'Unot' in e:v='invB '+words[ds[0]];w=width[ds[0]]
  elif '(Uextr' in e:
   hi,lo=map(int,re.search(r'Uextr (\d+) (\d+)',e).groups());v=f'drop {lo}(take {hi+1} {words[ds[0]]})';w=hi+1-lo
  elif '(Ushl' in e:
   sh=int(re.search(r'Ushl (\d+)',e)[1]);v=f'zeros {sh}++{words[ds[0]]}';w=width[ds[0]]+sh
  elif '(Ushr' in e:
   sh=int(re.search(r'Ushr (\d+)',e)[1]);v=f'drop {sh} {words[ds[0]]}';w=width[ds[0]]-sh
  else:raise ValueError(e)
  head+=f'Definition rf_shift_word_{n} (word:bits) := {v}.\n';defs.append(f'rf_shift_word_{n}');words[n]=f'(rf_shift_word_{n} word)';width[n]=w
 last=first+48
 head+=f'''Lemma rf_shift_reverse_{last} word :size word=32%nat ->rf_shift_word_{last} word=rev word.
Proof.
 intro Size. unfold {" , ".join(reversed(defs))}. rewrite !drop0. change(rf_reverse32 word=rev word). exact(rf_reverse32_correct word Size).
Qed.
Theorem rf_shift_reverse_history_{last} invalid history limit word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find {source}(history t)=Some(Gval(Fuint 32)word)) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,({rank[last]}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {last}(history t)=Some(Gval(Fuint 32)(rev word)).
Proof.
 intros Size Source Steps.
'''
 for n in range(first,last+1):
  head+=f''' assert(V{n}:forall t,({rank[n]}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {n}(history t)=Some(Gval(Fuint {width[n]})(rf_shift_word_{n} word))).
 {{ intros [|t] Lower Upper;[lia|].
 eapply(rf_shift_node_step {n} rf_shift_expr_{n});
 [apply(List.nth_error_In rf_shift_nodes {n-1171}%nat);reflexivity| |apply Steps;lia].
 intro site. cbn[rf_shift_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
  if deps[n]:head+=' rewrite '+' '.join(f'({"Source" if d==source else "V"+str(d)} t '+('ltac:(lia)' if d==source else 'ltac:(lia)ltac:(lia)')+')' for d in deps[n])+'.\n'
  head+=' reflexivity. }\n'
 head+=f'intros t Lower Upper. rewrite <-(rf_shift_reverse_{last} word Size). exact(V{last} t Lower Upper).\nQed.\n'
(p/'RFShiftReverseHistory.v').write_text(head)
