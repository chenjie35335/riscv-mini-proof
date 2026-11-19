"""Join 68 actual scalar-register commits; memory loads remain separate."""
import contextlib,io,json,re,runpy
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration'
with contextlib.redirect_stdout(io.StringIO()):a=runpy.run_path(str(root/'scripts/audit-x0-concrete-cone.py'))
regs=a['report']['joint_register_candidates'];model=a['source'];targets=sorted(map(int,json.loads((root/'formal/flat-low/joint-update-dependency-ranks.json').read_text())['targets']))
out='''Require Import CoreSocModel ComparisonNodes JointBoundaryRegisters JointRegisterCommitCertificates JointUpdateTargets ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem joint_scalar_registers_commit inputs path old current result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width old) ->
 (forall source, List.In source joint_update_targets -> exists ground bits, VM.find (N.of_nat source) old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 node <> 9220%nat -> node <> 9222%nat -> map_uint_concrete (N.of_nat node) width result.
Proof.
 intros Boundary Sources Step node width Member NotFetch NotLoad.
 unfold joint_boundary_registers in Member.
 repeat destruct Member as [Equal|Member]; try contradiction; inversion Equal; subst node width.
'''
for i,n in enumerate(regs):
 if n in (9220,9222):out+=' - contradiction.\n';continue
 width=int(re.search(r'\(@Sreg VarOrder.T '+str(n)+r' \(@mk_freg VarOrder.T \(Gtyp \(Fuint (\d+)\)\)',model)[1])
 out+=f''' - assert (Present : List.In ({n}%nat,{width}%nat) joint_boundary_registers).
   {{ apply (@List.nth_error_In _ joint_boundary_registers {i} ({n}%nat,{width}%nat)). vm_compute. reflexivity. }}
   destruct (Boundary {n}%nat {width}%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_{n}_commit inputs path old current result (Gval (Fuint {width}) bits)); [exact Lookup|reflexivity|'''
 out+='|'.join('' for _ in a['drivers'][n][0]['dependencies'])+'|exact Step].\n'
 # Avoid brackets with an ambiguous number of holes; use separate bullets instead.
 start=out.rfind('   eapply ')
 out=out[:start]+f'''   eapply (joint_register_{n}_commit inputs path old current result (Gval (Fuint {width}) bits)).
   + exact Lookup.
   + reflexivity.
'''
 for d in a['drivers'][n][0]['dependencies']:
  out+=f'''   + apply (Sources {d}%nat). apply (@List.nth_error_In _ joint_update_targets {targets.index(d)} {d}%nat). vm_compute. reflexivity.
'''
 out+='   + exact Step.\n'
out+='Qed.\nPrint Assumptions joint_scalar_registers_commit.\n'
f=p/'JointScalarRegisterCommit.v'
if not f.exists() or f.read_text()!=out:f.write_text(out)
