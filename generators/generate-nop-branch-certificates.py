"""Generate actual branch shape and zero propagation certificates."""
from pathlib import Path
import re
base=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration'
def write_if_changed(path, content):
 if not path.exists() or path.read_text() != content:
  path.write_text(content)

ids=list(map(int,re.findall(r'\((\d+),joint_update_expr_', (base/'JointUpdateNodePositions.v').read_text())))
header='''Require Import NopBranchShapes.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
# Require does not export dependencies, so keep direct imports explicit.
header=header.replace('Require Import NopBranchShapes.','Require Import NopBranchShapes CoreSocModel ComparisonNodes FormalTypedNodeEquation SelectedNodeSafety FormalSuccessfulNodeEvaluation JointUpdateNodePositions JointUpdateExpressionCertificates NormalizedBit.')
s=header
norm={1363:1362,1364:1363,1374:1370,1375:1373}
extr={1368:1362,1369:1357,1371:1362,1372:1358}
for n,src in list(norm.items())+list(extr.items()):
 p='normalized_bit' if n in norm else '(fun value => type_of_val value = Gtyp (Fuint 1))'
 s+=f'''Theorem nop_branch_shape_{n} invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find {n} result = Some value /\\ {p} value.
Proof.
 intro Step. eapply (nop_branch_node_shape {n} joint_update_expr_{n} _ invalid old current result).
 - apply (List.nth_error_In joint_update_expected_nodes {ids.index(n)}%nat). vm_compute. reflexivity.
 - intros site value Eval.
   cbn [joint_update_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.
   destruct (VM.find {src} old) as [source|]; [|discriminate Eval].
'''
 if n==1363:s+='   eapply nop_branch_reduction_or_normalized;exact Eval.\n'
 elif n in norm:s+='   eapply nop_branch_comparison_false_normalized;exact Eval.\n'
 else:s+='   exact (nop_branch_extract_result_type 31 31 source value Eval).\n'
 s+=(' - exact nop_branch_normalized_type.\n' if n in norm else ' - intros value Typed; exact Typed.\n')+' - exact Step.\nQed.\n'
for n,a,b in [(1370,1368,1369),(1373,1371,1372)]:
 s+=f'''Theorem nop_branch_shape_{n} invalid s0 s1 s2 :
 formal_value_iter invalid flat_memories s0 false s0 flat_statements = Some s1 ->
 formal_value_iter invalid flat_memories s1 false s1 flat_statements = Some s2 ->
 exists value, VM.find {n} s2 = Some value /\\ normalized_bit value.
Proof.
 intros Step1 Step2.
 destruct (nop_branch_shape_{a} invalid s0 s0 s1 Step1) as [left [Left LeftType]].
 destruct (nop_branch_shape_{b} invalid s0 s0 s1 Step1) as [right [Right RightType]].
 eapply (nop_branch_node_shape {n} joint_update_expr_{n} _ invalid s1 s1 s2).
 - apply (List.nth_error_In joint_update_expected_nodes {ids.index(n)}%nat). vm_compute. reflexivity.
 - intros site value Eval.
   change (eval_hfexpr_with_memory flat_memories joint_update_expr_{n} s1 s1 = Some value) in Eval.
   exact (nop_branch_mux_normalized flat_memories s1 (@Eref VarOrder.T (@Eid VarOrder.T 1367)) {a} {b} left right value Left LeftType Right RightType Eval).
 - exact nop_branch_normalized_type.
 - exact Step2.
Qed.
'''
write_if_changed(base/'NopBranchNodeShapes.v', s)
s=header.replace('Require Import NopBranchShapes','Require Import FormalDeclaredConnection JointUpdateConnectionCertificates NopBranchShapes')
selectors={1376:1359,1378:1359,1381:1359,1384:1359,1387:1359,1390:1359}
masks={1377:(1376,1364),1379:(1378,1363),1382:(1381,1370),1385:(1384,1374),1388:(1387,1373),1391:(1390,1375)}
ors={1380:(1377,1379),1383:(1380,1382),1386:(1383,1385),1389:(1386,1388),1392:(1389,1391)}
wires={1359:(90,3),1360:(1392,1)}
order=[1359]+list(range(1376,1393))+[1360]
def zero(w):return f'(Gval (Fuint {w}) [::'+ ';'.join(['false']*w)+'])'
conns=(base/'JointUpdateConnectionCertificates.v').read_text()
for n in order:
 if n in wires:src,w=wires[n];deps=[src]
 elif n in selectors:w=1;deps=[1359]
 elif n in masks:w=1;deps=[masks[n][0]]
 else:w=1;deps=list(ors[n])
 s+=f'Theorem nop_branch_zero_step_{n} invalid old current result :\n'
 for d in deps:s+=f' VM.find {d} old = Some {zero(3 if d in [90,1359] else 1)} ->\n'
 if n in masks:
  operand=masks[n][1];s+=f' (exists value, VM.find {operand} old = Some value /\\ normalized_bit value) ->\n'
 s+=' formal_value_iter invalid flat_memories old false current flat_statements = Some result ->\n'+f' VM.find {n} result = Some {zero(w)}.\nProof.\n intros '+' '.join(f'H{d}' for d in deps)+(' [value [Value Normal]]' if n in masks else '')+' Step.\n'
 if n in wires:
  m=re.search(r'Lemma (\w+)_position\s*:\s*straight_drop (\d+) flat_statements = Some \(@Qcons VarOrder.T \(@Swire VarOrder.T '+str(n)+r' \(Gtyp \(Fuint '+str(w)+r'\)\)\)',conns);assert m,n
  p,pos=m[1],m[2]
  s+=f''' apply (declared_connection_value {pos} flat_statements {p}_decl {p}_mid {p}_tail
 {n} {src} {w} {zero(w)} {zero(w)} invalid flat_memories old current result
 {p}_position {p}_split {p}_straight {p}_mid_safe {p}_tail_safe {p}_nonregister (Logic.eq_refl _) H{src});
 [reflexivity|exact Step].
'''
 else:
  s+=f''' assert (Member : List.In ({n},joint_update_expr_{n}) joint_update_expected_nodes).
 {{ apply (List.nth_error_In joint_update_expected_nodes {ids.index(n)}%nat). vm_compute. reflexivity. }}
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes {n} joint_update_expr_{n} joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node;
 [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [joint_update_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].
'''
  for d in deps:s+=f' rewrite H{d}.\n'
  if n in masks:s+=' rewrite Value. apply nop_branch_zero_and_normalized. exact Normal.\n'
  else:s+=' reflexivity.\n'
 s+='Qed.\n'
write_if_changed(base/'NopBranchValues.v', s)
s=header.replace('Require Import NopBranchShapes','Require Import NopBranchNodeShapes NopBranchValues NopKillHistory FormalInstructionResetConstants JointUpdateBoundaryHistory JointBoundaryRegisters NopBranchShapes')
steps='(forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i)))'
for n in list(norm)+[1370,1373]:
 s+=f'''Theorem nop_branch_normalized_history_{n} invalid history limit :
 {steps} ->
 forall time, (2 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 exists value, VM.find {n} (history time) = Some value /\\ normalized_bit value.
Proof.
 intros Steps time Lower Upper.
'''
 if n in norm:
  s+=f''' destruct time as [|time]; [lia|].
 apply (nop_branch_shape_{n} invalid (history time) (history time) (history (S time))).
 apply Steps; lia.
'''
 else:
  s+=f''' destruct time as [|[|time]]; try lia.
 apply (nop_branch_shape_{n} invalid (history time) (history (S time)) (history (S (S time)))); apply Steps; lia.
'''
 s+='Qed.\n'
ranks={90:55}
for n in order:
 if n in wires:deps=[wires[n][0]]
 elif n in selectors:deps=[1359]
 elif n in masks:deps=[masks[n][0]]
 else:deps=list(ors[n])
 rank=max(ranks[d] for d in deps)+1;ranks[n]=rank
 s+=f'''Theorem nop_branch_zero_history_{n} invalid history limit :
 VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop) ->
 {steps} ->
 forall time, ({rank} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find {n} (history time) = Some {zero(3 if n==1359 else 1)}.
Proof.
 intros Initial Steps time Lower Upper.
 destruct time as [|time]; [lia|].
 apply (nop_branch_zero_step_{n} invalid (history time) (history time) (history (S time))).
'''
 for d in deps:
  name='nop_br_type_zero_history' if d==90 else f'nop_branch_zero_history_{d}'
  s+=f' - apply ({name} invalid history limit Initial Steps time); lia.\n'
 if n in masks:s+=f' - apply (nop_branch_normalized_history_{masks[n][1]} invalid history limit Steps time); lia.\n'
 s+=' - apply Steps; lia.\nQed.\n'
s+='''Definition nop_branch_false_history := nop_branch_zero_history_1360.
Theorem nop_branch_false_history_from_final invalid history limit :
 VM.find 7748 (history limit) = Some (Gval (Fuint 32) instruction_nop) ->
'''+steps+''' ->
 forall time, (64 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 VM.find 1360 (history time) = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Final Steps time Lower Upper.
 assert (Initial : VM.find 7748 (history 0%nat) = Some (Gval (Fuint 32) instruction_nop)).
 { rewrite (joint_update_register_history_same invalid history limit 7748 32 nop_kill_register_member Steps limit (Nat.le_refl limit)) in Final. exact Final. }
 exact (nop_branch_false_history invalid history limit Initial Steps time Lower Upper).
Qed.
'''
write_if_changed(base/'NopBranchHistory.v', s)
write_if_changed(base/'NopBranchHistoryAssumptions.v', 'Require Import NopBranchHistory.\nPrint Assumptions nop_branch_false_history.\nPrint Assumptions nop_branch_false_history_from_final.\n')
print('NOP branch false history rank',ranks[1360])
