from pathlib import Path
import re
s=Path('formal/flat-low/CoreSocModel.v').read_text()
ids=[8005,8006,8007,8073,8074,8198]
expr=[]; positions=[]
for n in ids:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',s);d=0
 for j in range(m.start(),len(s)):
  d+=(s[j]=='(')-(s[j]==')')
  if d==0:break
 expr.append(s[m.end():j]);positions.append(s[:m.start()].count('(@Qcons VarOrder.T '))
# model contains only one generated statement definition
out='''Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceRedirectSpine RequestEnableNormalized FormalDeclaredWireCheck MemoryRequestWidth.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n,e in zip(ids,expr):out+=f'Definition read_valid_expr_{n} := {e}.\n'
out+='Definition read_valid_nodes := [::'+ ';'.join(f'({n},read_valid_expr_{n})'for n in ids)+'].\n'
offs=[positions[0]-1]+[b-a-1 for a,b in zip(positions,positions[1:])]
out+='Definition read_valid_offsets := [::'+';'.join(f'{n}%nat'for n in offs)+'].\n'
out+='''Lemma read_valid_positions :select_node_offsets read_valid_offsets flat_statements=Some read_valid_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma read_valid_safety :selected_node_safety flat_memories flat_statements read_valid_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem read_valid_history kind invalid history limit start :
 (kind<8)%coq_nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 7995(history t)=Some(Gval(Fuint 6)(from_N 6(memory_request_width false kind)))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 128(history t)=Some(Gval(Fuint 1)[::false])) ->
 forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1474(history t)=Some(Gval(Fuint 1)[::memory_request_active false kind]).
Proof.
 intros Kind Steps Width Quiet.
'''
for i,n in enumerate(ids):
 dep={8005:1,8006:1,8007:2,8073:3,8074:4,8198:5}[n]
 bit='true' if n==8006 else 'memory_request_active false kind'
 out+=f''' assert(V{n}:forall t,(Nat.add start {dep}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {n}(history t)=Some(Gval(Fuint 1)[::{bit}])).
 {{ intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step read_valid_offsets read_valid_nodes {n} read_valid_expr_{n});
 [exact read_valid_positions|exact read_valid_safety|apply(List.nth_error_In read_valid_nodes {i}%nat);reflexivity| |apply Steps;lia].
 intros site. cbn[read_valid_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
 if n==8005:out+=' rewrite(Width t ltac:(lia)ltac:(lia)). do 8(destruct kind as[|kind];[reflexivity|]);lia. }\n'
 elif n==8006:out+=' rewrite(Quiet t ltac:(lia)ltac:(lia));reflexivity. }\n'
 elif n==8007:out+=' rewrite(V8005 t ltac:(lia)ltac:(lia))(V8006 t ltac:(lia)ltac:(lia)). destruct(memory_request_active false kind);reflexivity. }\n'
 else:out+=f' exact(V{ids[i-1]} t ltac:(lia)ltac:(lia)). }}\n'
out+=''' intros[|t] Lower Upper;try lia. eapply declared_wire_checked_value;
 [exact read_valid_certificate_1474|exact(V8198 t ltac:(lia)ltac:(lia))|reflexivity|exact(Steps t ltac:(lia))].
Qed.
'''
Path('formal/flat-low/staged-integration/ReadValidHistory.v').write_text(out)
print(positions,offs)
