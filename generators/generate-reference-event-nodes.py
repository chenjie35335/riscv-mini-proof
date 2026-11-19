"""Exact equations for the reference event and assertion44 enable."""
import re
import argparse
from pathlib import Path
parser=argparse.ArgumentParser()
parser.add_argument('--assertion43', action='store_true')
parser.add_argument('--assertion2', action='store_true')
args=parser.parse_args()
root=Path(__file__).resolve().parents[2]; base=root/'formal/flat-low'
model=(base/'CoreSocModel.v').read_text()
out='''Require Import CoreSocModel ComparisonNodes FormalNodeEquation FormalTypedNodeEquation FormalTypedNodeFrames MemorySuffixCertificates MemoryWriteFrames ScalarNodeFrames RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n in ([7575,7576] if args.assertion2 else [7741,7742] if args.assertion43 else [7083,7116,7117,7202,7727,7745,7746]):
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',model);depth=0
 for end in range(m.start(),len(model)):
  depth+=(model[end]=='(')-(model[end]==')')
  if depth==0:break
 expr=model[m.end():end];pos=len(re.findall(r'\(@Qcons VarOrder.T ',model[:m.start()]))-1
 out+=f'''Definition reference_event_expr_{n} := {expr}.
Definition reference_event_tail_{n} := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_event_position_{n} : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} reference_event_expr_{n}) reference_event_tail_{n}).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_event_suffix_{n} : memory_suffix_safe flat_memories {n} reference_event_tail_{n}.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_event_nonregister_{n} : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_event_equation_{n} invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = eval_hfexpr_with_memory flat_memories reference_event_expr_{n} old old.
Proof.
 intro Step. exact (formal_combinational_node_equation _ _ _ _ _ invalid flat_memories old current result
 reference_event_position_{n} reference_event_suffix_{n} reference_event_nonregister_{n} Step).
Qed.
'''
for n in ([] if args.assertion43 or args.assertion2 else [7202]):
 out=out.replace(f'memory_suffix_safe flat_memories {n} reference_event_tail_{n}', f'formal_typed_suffix_safe flat_memories {n} reference_event_tail_{n}')
 marker=f'Lemma reference_event_suffix_{n}'
 a=out.index(marker); b=out.index('Qed.',a)
 out=out[:a]+out[a:b].replace('memory_suffix_safe_b_sound','formal_typed_suffix_safe_b_sound')+out[b:]
 a=out.index(f'Theorem reference_event_equation_{n}');b=out.index('Qed.',a)+4
 replacement=f"""Theorem reference_event_value_{n} invalid old current result value :
 eval_hfexpr_with_memory flat_memories reference_event_expr_{n} old old = Some value ->
 type_of_val value = Gtyp (Fuint 1) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some value.
Proof.
 intros Eval Typed Step. eapply formal_combinational_known_node;
 [exact reference_event_position_{n}|exact reference_event_suffix_{n}|exact reference_event_nonregister_{n}|exact Eval|exact Typed|exact Step].
Qed."""
 out=out[:a]+replacement+out[b:]
out+=('Print Assumptions reference_event_equation_7576.\n' if args.assertion2 else 'Print Assumptions reference_event_equation_7742.\n' if args.assertion43 else 'Print Assumptions reference_event_equation_7746.\n') 
p=base/'staged-integration'/('Assertion2GuardNodes.v' if args.assertion2 else 'Assertion43GuardNodes.v' if args.assertion43 else 'ReferenceEventNodes.v')
if not p.exists() or p.read_text()!=out:p.write_text(out)
