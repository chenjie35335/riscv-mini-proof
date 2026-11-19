"""Certify actual read-valid output adaptation and the shared OR guard."""
from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2]
s=(root/'formal/flat-low/CoreSocModel.v').read_text()
q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
out='''Require Import CoreSocModel ComparisonNodes DeclaredWireObservation FormalDeclaredWireCheck NormalizedBit NormalizedOr FormalNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in [1474,1519]:
 d=bisect.bisect_right(q,s.index(f'(@Swire VarOrder.T {n} '))-1
 m=re.search(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(n)+r'\) \(@Eref VarOrder.T \(@Eid VarOrder.T (\d+)\)\)\)',s)
 c=bisect.bisect_right(q,m.start())-1;src=int(m[1]);dist=c-d-1
 out+=f'''Lemma read_valid_certificate_{n} :declared_wire_check flat_memories flat_statements {d} {dist} {n} {src} 1=true.
Proof. vm_compute;reflexivity. Qed.
Theorem read_valid_normalized_{n} invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 exists value,VM.find {n} result=Some value /\ normalized_bit value.
Proof.
 intro Step. destruct(declared_wire_checked_observation _ _ _ _ _ _ _ _ _ _ _ read_valid_certificate_{n} Step)as[source[value[Source[Adapt Value]]]].
 exists value;split;[exact Value|exact(adapted_bit_normalized source value Adapt)].
Qed.
'''
n=7569;m=re.search(r'\(@Snode VarOrder.T 7569 ',s);depth=0
for end in range(m.start(),len(s)):
 depth+=(s[end]=='(')-(s[end]==')')
 if depth==0:break
expr=s[m.end():end];pos=bisect.bisect_right(q,m.start())-1
out+=f'''Definition read_valid_or_expression :={expr}.
Definition read_valid_or_tail :=match straight_drop {pos+1} flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma read_valid_or_position :straight_drop {pos} flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T 7569 read_valid_or_expression)read_valid_or_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma read_valid_or_suffix :memory_suffix_safe flat_memories 7569 read_valid_or_tail.
Proof. apply memory_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma read_valid_or_nonregister :has_register 7569 flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Theorem read_valid_or_normalized invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements=Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements=Some s2 ->
 exists value,VM.find 7569 s2=Some value /\ normalized_bit value.
Proof.
 intros S1 S2.
 destruct(read_valid_normalized_1474 invalid s0 s0 s1 S1)as[left[Left NL]].
 destruct(read_valid_normalized_1519 invalid s0 s0 s1 S1)as[right[Right NR]].
 exists(normalized_or_value left right);split;[|exact(normalized_or_normal left right NL NR)].
 rewrite(formal_combinational_node_equation _ _ _ _ _ invalid flat_memories s1 s1 s2 read_valid_or_position read_valid_or_suffix read_valid_or_nonregister S2).
 unfold read_valid_or_expression. cbn [eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Left Right.
 exact(normalized_or_total left right NL NR).
Qed.
'''
(root/'formal/flat-low/staged-integration/RequestEnableNormalized.v').write_text(out)
