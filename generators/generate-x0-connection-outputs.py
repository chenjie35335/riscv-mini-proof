"""Reuse checked connection positions to expose uniform concrete UInt rules."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
model=(root/'formal/flat-low/CoreSocModel.v').read_text()
connections={785:7805,784:7941,128:442,123:7750,118:7758,122:7752,127:7760,124:7759,126:7755,125:7754,81:40,40:9218,74:33,33:9216}
out='''Require Import CoreSocModel ComparisonNodes FormalRFInputConnections FormalExceptionInput FormalStallConnections X0RegisterInputConnections FormalDeclaredConnection.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for node,source in sorted(connections.items()):
 decl=re.search(r'\(@Swire VarOrder.T '+str(node)+r' \(Gtyp \(Fuint (\d+)\)\)\)',model)
 width=int(decl[1]); pos=len(re.findall(r'\(@Qcons VarOrder.T ',model[:decl.start()]))-1
 out+=f'''Theorem x0_connection_output_{node} invalid old current result :
 (exists width bits, VM.find {source} old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find {node} result = Some (Gval (Fuint width) bits).
Proof.
 intros [width [bits Source]] Step. exists {width}.
'''
 if node in [123,118,122,127,124,126,125]:
  out+=f' exact (x0_register_input_concrete_{node} invalid old current result width bits Source Step).\n'
 elif node in [784,785,128]:
  name=f'rf_input_connection_{node}' if node!=128 else 'exception_input_connection_128'
  out+=f' eexists. eapply {name}; [exact Source|reflexivity|exact Step].\n'
 else:
  out+=f''' eexists. eapply (declared_connection_value {pos} flat_statements stall_declared_{node} stall_middle_{node} stall_after_{node}
 {node} {source} 1 (Gval (Fuint width) bits) _ invalid flat_memories old current result);
 [exact stall_declaration_{node}|exact stall_split_{node}|exact stall_straight_{node}|
 exact stall_middle_safe_{node}|exact stall_after_safe_{node}|exact stall_connection_nonregister_{node}|reflexivity|exact Source|reflexivity|exact Step].
'''
 out+='Qed.\n'
out+='Print Assumptions x0_connection_output_785.\n'
generated_path = root/'formal/flat-low/staged-integration/X0ConcreteConnectionOutputs.v'
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print('Generated 14 uniform connection transfer rules from existing certificates.')
