"""Shared actual destination-register projection, reusing existing node certificates."""
from pathlib import Path
import re,json
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text();es={}
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',s):
 n=int(m[1])
 if n>3221:continue
 d=1;j=m.end()
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 es[n]=s[m.end():j-1]
seen=set();guards=set()
def visit(n):
 if n==1884 or n in seen:return
 e=es[n];ds=list(map(int,re.findall(r'@Eid VarOrder.T (\d+)',e)))
 if '@Emux'in e:guards.add(ds[0]);ds=ds[1:]
 for d in ds:visit(d)
 seen.add(n)
visit(3221);ids=sorted(n for n in seen if 'Uextr'in es[n]);rank={1884:0};width={1884:32};rows=[]
for n in ids:
 hi,lo=map(int,re.search(r'Uextr (\d+) (\d+)',es[n]).groups());src=int(re.search(r'@Eid VarOrder.T (\d+)',es[n])[1]);assert width[src]>=hi+1
 rows.append((n,src,hi,lo,width[src],rank[src]+1));rank[n]=rank[src]+1;width[n]=hi-lo+1
certs={}
for b in range(4):
 t=(p/f'ReferenceControlNodeCertificates{b}.v').read_text();lst=re.findall(r'\((\d+),reference_control_expr_\d+\)',t)
 for i,n in enumerate(lst):certs[int(n)]=(f'reference_control_{b}',i)
t=(p/'RFReferenceNopDecode.v').read_text();lst=re.findall(r'\((\d+),rf_nop_expr_\d+\)',t)
for i,n in enumerate(lst):certs[int(n)]=('rf_nop',i)
out='''Require Import CoreSocModel ComparisonNodes RFReferenceNopDecode ReferenceRedirectSpine ReferenceControlNodeCertificates0 ReferenceControlNodeCertificates1 ReferenceControlNodeCertificates2 ReferenceControlNodeCertificates3 X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Record rf_rd_slice := {rds_node:N;rds_source:N;rds_high:nat;rds_low:nat;rds_source_width:nat;rds_rank:nat}.
Definition rf_rd_slices := [::'''+ ';'.join('{|rds_node:='+str(n)+';rds_source:='+str(src)+';rds_high:='+str(hi)+'%nat;rds_low:='+str(lo)+'%nat;rds_source_width:='+str(sw)+'%nat;rds_rank:='+str(r)+'%nat|}'for n,src,hi,lo,sw,r in rows)+'''].
Definition rf_rd_slice_at i := nth {|rds_node:=0;rds_source:=0;rds_high:=0%nat;rds_low:=0%nat;rds_source_width:=0%nat;rds_rank:=0%nat|} rf_rd_slices i.
Definition rf_rd_slice_expr row := @Eprim_unop VarOrder.T (Uextr(rds_high row)(rds_low row))(@Eref VarOrder.T(@Eid VarOrder.T(rds_source row))).
Definition rf_rd_slice_value row instruction := Gval(Fuint(S(rds_high row)-rds_low row)%nat)(drop(rds_low row)(take(S(rds_high row))instruction)).
Lemma rf_rd_slice_certificates i : (i<171)%coq_nat ->
 exists offsets nodes,select_node_offsets offsets flat_statements=Some nodes /\\selected_node_safety flat_memories flat_statements offsets flat_statements=true /\\List.In(rds_node(rf_rd_slice_at i),rf_rd_slice_expr(rf_rd_slice_at i))nodes /\\(rds_low(rf_rd_slice_at i)<=rds_high(rf_rd_slice_at i))%nat /\\(S(rds_high(rf_rd_slice_at i))<=rds_source_width(rf_rd_slice_at i))%nat.
Proof. intro Bound.
'''
for n,*_ in rows:
 c,i=certs[n];out+=f'destruct i as[|i]. {{exists {c}_offsets,{c}_nodes. split;[exact {c}_positions|]. split;[exact {c}_safety|]. split;[apply(List.nth_error_In {c}_nodes {i}%nat);reflexivity|split;reflexivity]. }}\n'
out+='lia. Qed.\n'
out+='''Lemma rf_rd_slice_step i invalid old result instruction : (i<171)%coq_nat ->
 VM.find(rds_source(rf_rd_slice_at i))old=Some(Gval(Fuint(rds_source_width(rf_rd_slice_at i)))(take(rds_source_width(rf_rd_slice_at i))instruction)) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find(rds_node(rf_rd_slice_at i))result=Some(rf_rd_slice_value(rf_rd_slice_at i)instruction).
Proof.
 intros Bound Source Step. destruct(rf_rd_slice_certificates i Bound)as[offsets[nodes[Positions[Safety[Member[Lower Width]]]]]].
 eapply(reference_redirect_ground_step offsets nodes _ (rf_rd_slice_expr(rf_rd_slice_at i)));[exact Positions|exact Safety|exact Member| |exact Step].
 intros site. unfold rf_rd_slice_expr. cbn[eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Source.
 cbn [eval_unop]. rewrite Lower Width.
 change(Some(Gval(Fuint(S(rds_high(rf_rd_slice_at i))-rds_low(rf_rd_slice_at i))%nat)(drop(rds_low(rf_rd_slice_at i))(take(S(rds_high(rf_rd_slice_at i)))(take(rds_source_width(rf_rd_slice_at i))instruction))))=Some(rf_rd_slice_value(rf_rd_slice_at i)instruction)).
 rewrite take_takel;[reflexivity|exact Width].
Qed.
'''
f=p/'RFScalarControl.v';marker='(* Scalar history and ISA composition. *)';manual=f.read_text().split(marker,1)[1]if f.exists()and marker in f.read_text()else'\n';f.write_text(out+marker+manual)
(root/'formal/flat-low/rf-rd-slice-map.json').write_text(json.dumps({'rows':rows,'guards':sorted(guards)},indent=2)+'\n')
print('slices',len(rows),'maxrank',max(rank.values()))
