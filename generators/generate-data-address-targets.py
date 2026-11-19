"""Connect the five extraction nodes to concrete UInt memory address sources."""
from pathlib import Path
import re
root = Path(__file__).resolve().parents[2]
position = (root / 'formal/flat-low/staged-integration/DataAddressPositionCertificate.v').read_text()
nodes = [int(n) for n in re.findall(r'N.of_nat (\d+), address_expr_', position)]
out = '''Require Import CoreSocModel ComparisonNodes ConcreteExtractNode DataAddressPositionCertificate DataAddressSafetyCertificate DataAddressExpressionCertificates FormalDataReaderAddresses.
From Coq Require Import List ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for node in [9186,9194,9202,9210,9221]:
    out += f'''Lemma data_address_target_member_{node} : List.In ({node}, address_expr_{node}) data_address_expected_nodes.
Proof.
 apply (@List.nth_error_In _ data_address_expected_nodes {nodes.index(node)} ({node}, address_expr_{node})).
 vm_compute. reflexivity.
Qed.
Lemma data_address_target_uint_{node} inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 exists width bits, VM.find {node} result = Some (Gval (Fuint width) bits).
Proof.
 intros Source Step.
 eapply selected_extract_node_concrete;
 [exact data_address_actual_node_expressions|exact data_address_actual_nodes_safe|
 exact data_address_target_member_{node}|exact Source|exact Step].
Qed.
'''
out += '''Theorem data_address_sources_from_9182 inputs path old current result :
 (exists ground bits, VM.find 9182 old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 data_reader_sources_concrete result.
Proof.
 intros Source Step node Member.
 repeat destruct Member as [Equal|Member]; try contradiction; subst node.
'''
for node in [9186,9194,9202,9210,9221]:
    out += f' - exact (data_address_target_uint_{node} inputs path old current result Source Step).\n'
out += 'Qed.\nPrint Assumptions data_address_sources_from_9182.\n'
p = root / 'formal/flat-low/staged-integration/DataAddressUIntTargets.v'
if not p.exists() or p.read_text() != out:
    p.write_text(out)
