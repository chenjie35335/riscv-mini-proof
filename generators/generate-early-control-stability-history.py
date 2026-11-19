"""Compose certified control dependencies into exact history stability.

Register/data/wire results stay UInt; additional joint nodes may be any concrete
FIRRTL ground value. All validity choices retain the same policy and site.
"""
import json,re
from pathlib import Path
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';proof=base/'staged-integration'
plan=json.loads((base/'early-bubble-stability-plan.json').read_text());entries=plan['nodes']
model=(base/'CoreSocModel.v').read_text();regs=set(map(int,re.findall(r'\(@Sreg VarOrder.T (\d+) ',model)))
snodes=set(map(int,re.findall(r'\(@Snode VarOrder.T (\d+) ',model)))
wirewidth={int(n):int(w) for n,w in re.findall(r'\(@Swire VarOrder.T (\d+) \(Gtyp \(Fuint (\d+)\)\)\)',model)}
joint_text=(proof/'JointBoundaryRegisters.v').read_text().split('Lemma joint_boundary_register_check',1)[0]
joint=[tuple(map(int,x)) for x in re.findall(r'\((\d+),(\d+)\)',joint_text)]
widths=dict(joint);data=set(plan['certificate_coverage']['data']);x0=set(plan['certificate_coverage']['x0']);extra=set(plan['certificate_coverage']['joint'])
kind={r['id']:('reg' if r['id'] in regs else 'data' if r['id'] in data else 'x0' if r['id'] in x0 else 'joint' if r['id'] in extra else 'wire') for r in entries}
uint={n for n,k in kind.items() if k!='joint'}
header='''Require Import CoreSocModel ComparisonNodes EarlyControlDataCongruence EarlyControlJointCongruence EarlyControlWireCongruence JointBoundaryRegisters JointUpdateBoundaryHistory ConcreteRegisterInitialization JointUpdateOutputCertificates DataAddressExpressionCertificates DataAddressUIntCertificates DataAddressPositionCertificate DataAddressSafetyCertificate X0ConcreteOutputCertificates X0ConcreteExpressionCertificates X0UIntExpressionCertificates SelectedUIntNodeCongruence SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation.
From Coq Require Import ZArith List Lia PeanoNat.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma early_control_data_uint_output node expression inputs path old result :
 List.In (node,expression) data_address_expected_nodes ->
 (forall site value,
  eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories expression old old = Some value ->
  exists width bits, value = Gval (Fuint width) bits) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false old flat_statements = Some result ->
 exists width bits, VM.find node result = Some (Gval (Fuint width) bits).
Proof.
 intros Member Typed Step.
 destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements
 data_address_expected_nodes node expression data_address_actual_node_expressions data_address_actual_nodes_safe Member)
 as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail node expression (formal_invalid_policy inputs path)
 flat_memories old false old result Position Step) as [value Eval]. rewrite add0n in Eval.
 destruct (Typed _ value Eval) as [width [bits Eq]]. subst value.
 exists width,bits.
 exact (formal_combinational_known_node count flat_statements tail node expression width (Gval (Fuint width) bits)
 (formal_invalid_policy inputs path) flat_memories old old result Position Safe Nonreg Eval (Logic.eq_refl _) Step).
Qed.
Lemma early_control_node_7805_congruent inputs path left right next_left next_right :
 (exists width bits, VM.find 7750 left = Some (Gval (Fuint width) bits)) ->
 VM.find 7750 left = VM.find 7750 right ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 VM.find 7805 next_left = VM.find 7805 next_right.
Proof.
 intros Concrete Equal L R.
 apply (x0_selected_uint_node_congruent 7805 x0_concrete_expr_7805 (formal_invalid_policy inputs path) left right next_left next_right).
 - apply (List.nth_error_In X0ConcretePositionCertificate.x0_expected_nodes 152%nat). vm_compute. reflexivity.
 - intro site. cbn [x0_concrete_expr_7805 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Equal. reflexivity.
 - intros site value Eval. destruct (x0_uint_result_7805 _ site flat_memories left value Concrete Eval) as [width [bits Eq]].
   subst value. exists width. reflexivity.
 - exact L.
 - exact R.
Qed.
'''
common=''' (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width (history 0%nat)) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
'''
out=header
for e in entries:
 n,r,deps=e['id'],e['rank'],e['dependencies'];k=kind[n]
 if k=='reg':
  w=widths[n];out+=f'''Lemma early_control_member_{n} : List.In ({n}%nat,{w}%nat) joint_boundary_registers.
Proof. apply (List.nth_error_In joint_boundary_registers {joint.index((n,w))}%nat). vm_compute. reflexivity. Qed.
'''
 result=f'exists width bits, VM.find {n} (history time) = Some (Gval (Fuint width) bits)' if n in uint else f'exists ground bits, VM.find {n} (history time) = Some (Gval ground bits)'
 out+=f'Theorem early_control_concrete_{n}_history inputs path history limit :\n'+common+f''' forall time, ({r} <= time)%coq_nat -> (time <= limit)%coq_nat ->
 {result}.
Proof.
 intros Boundary Steps time Lower Upper.
'''
 def dep_apply(d,t='time',want_uint=False):
  assert not want_uint or d in uint,(n,d)
  if want_uint or d not in uint:
   return f'apply (early_control_concrete_{d}_history inputs path history limit Boundary Steps {t}); lia.'
  return f'destruct (early_control_concrete_{d}_history inputs path history limit Boundary Steps {t} ltac:(lia) ltac:(lia)) as [w [b V]]. exists (Fuint w), b. exact V.'
 if k=='reg':
  out+=f''' rewrite (joint_update_register_history_same _ history limit {n} {w} early_control_member_{n} Steps time Upper).
 destruct (Boundary {n}%nat {w}%nat early_control_member_{n}) as [bits [Size Lookup]].
 exists {w}%nat, bits. exact Lookup.
'''
 else:
  out+=' destruct time as [|time]; [lia|].\n'
  if k=='data':
   for d in deps:
    out+=f' assert (H{d} : exists width bits, VM.find {d} (history time) = Some (Gval (Fuint width) bits)).\n {{ '+dep_apply(d,want_uint=True)+' }\n'
   out+=f''' apply (early_control_data_uint_output {n} address_expr_{n} inputs path (history time) (history (S time)) early_control_data_member_{n}).
 - intros site value Eval. exact (address_uint_result_{n} inputs path site flat_memories (history time) value '''+' '.join(f'H{d}' for d in deps)+''' Eval).
 - apply Steps. lia.
'''
  elif k=='x0':
   out+=f' apply (x0_node_output_{n} inputs path (history time) (history time) (history (S time))).\n'
   for d in deps:out+=' - '+dep_apply(d,want_uint=True)+'\n'
   out+=' - apply Steps. lia.\n'
  elif k=='joint':
   out+=f' apply (joint_update_node_output_{n} inputs path (history time) (history time) (history (S time))).\n'
   for d in deps:out+=' - '+dep_apply(d)+'\n'
   out+=(' - ' if deps else ' ')+'apply Steps. lia.\n'
  else:
   assert len(deps)==1
   out+=f' destruct (early_control_wire_{n}_output (formal_invalid_policy inputs path) (history time) (history time) (history (S time))) as [bits Value].\n'
   out+=' - '+dep_apply(deps[0])+'\n - apply Steps. lia.\n'
   out+=f' - exists {wirewidth[n]}%nat, bits. exact Value.\n'
 out+='Qed.\n'
 out+=f'Theorem early_control_stable_{n}_history inputs path history limit :\n'+common+f''' forall t u, ({r} <= t)%coq_nat -> ({r} <= u)%coq_nat ->
 (t <= limit)%coq_nat -> (u <= limit)%coq_nat ->
 VM.find {n} (history t) = VM.find {n} (history u).
Proof.
 intros Boundary Steps t u LT LU UT UU.
'''
 if k=='reg':
  out+=f''' rewrite (joint_update_register_history_same _ history limit {n} {w} early_control_member_{n} Steps t UT).
 rewrite (joint_update_register_history_same _ history limit {n} {w} early_control_member_{n} Steps u UU). reflexivity.
'''
 else:
  out+=' destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].\n'
  call=f'early_control_wire_{n}_congruent (formal_invalid_policy inputs path)' if k=='wire' else f'early_control_node_{n}_congruent inputs path'
  out+=f' apply ({call} (history t) (history u) (history (S t)) (history (S u))).\n'
  if k!='wire':
   for d in deps:out+=' - '+dep_apply(d,t='t',want_uint=k in ['data','x0'])+'\n'
  for d in deps:out+=f' - apply (early_control_stable_{d}_history inputs path history limit Boundary Steps t u); lia.\n'
  out+=' - apply Steps. lia.\n - apply Steps. lia.\n'
 out+='Qed.\n'
out+='(* Audit the two public targets separately in EarlyControlStabilityHistoryAssumptions.v. *)\n'
p=proof/'EarlyControlStabilityHistory.v'
if not p.exists() or p.read_text()!=out:p.write_text(out)
p=proof/'EarlyControlStabilityHistoryAssumptions.v';a='Require Import EarlyControlStabilityHistory.\nPrint Assumptions early_control_stable_85_history.\nPrint Assumptions early_control_stable_1360_history.\n'
if not p.exists() or p.read_text()!=a:p.write_text(a)
print('Generated history concreteness and stability for',len(entries),'nodes; targets85/1360 ranks56/64')
