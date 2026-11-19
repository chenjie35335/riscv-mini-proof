"""Exact equations for the existing assumption, including reset gating and trap aliases."""
import re
from pathlib import Path
root=Path(__file__).resolve().parents[2]; base=root/'formal/flat-low'
model=(base/'CoreSocModel.v').read_text()
out='''Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in [9139,9140,9141,9153,9157,9237,9238,9239,9240]:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model);depth=0
 for end in range(m.start(),len(model)):
  depth+=(model[end]=='(')-(model[end]==')')
  if depth==0:break
 expr=model[m.end():end];pos=len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
 out+=f'''Definition legal_expr_{n} := {expr}.
Definition legal_tail_{n} := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_position_{n} : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} legal_expr_{n}) legal_tail_{n}).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_suffix_{n} : memory_suffix_safe flat_memories {n} legal_tail_{n}.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_nonregister_{n} : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_equation_{n} invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = eval_hfexpr_with_memory flat_memories legal_expr_{n} old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 legal_position_{n} legal_suffix_{n} legal_nonregister_{n} Step).
Qed.
'''
for n in [9141,9157]:
 out=out.replace(f'memory_suffix_safe flat_memories {n} legal_tail_{n}', f'formal_typed_suffix_safe flat_memories {n} legal_tail_{n}')
 marker=f'Lemma legal_suffix_{n}'
 a=out.index(marker); b=out.index('Qed.',a)
 out=out[:a]+out[a:b].replace('memory_suffix_safe_b_sound','formal_typed_suffix_safe_b_sound')+out[b:]
 a=out.index(f'Theorem legal_equation_{n}');b=out.index('Qed.',a)+4
 replacement=f"""Theorem legal_value_{n} invalid old current result value :
 eval_hfexpr_with_memory flat_memories legal_expr_{n} old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact legal_position_{n}|exact legal_suffix_{n}|exact legal_nonregister_{n}|exact Eval|exact Typed|exact Step].
Qed."""
 out=out[:a]+replacement+out[b:]
out+='Print Assumptions legal_equation_9240.\n' 
p=base/'staged-integration/LegalAssumptionNodes.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
