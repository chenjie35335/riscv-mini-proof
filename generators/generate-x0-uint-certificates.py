"""Certify UInt results for every selected x0 node, given concrete UInt references."""
import contextlib
import io
from pathlib import Path
import runpy

root = Path(__file__).resolve().parents[2]
with contextlib.redirect_stdout(io.StringIO()):
    data = runpy.run_path(str(root / 'formal/generators/generate-x0-expression-certificates.py'))
out = '''Require Import X0ConcreteExpressionCertificates ConcreteUIntOperations ConcreteUIntScalarExpressions.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Ltac solve_uint_ready :=
 repeat first [eapply uint_ready_ref; eassumption | apply uint_ready_const
 | apply uint_ready_unary; [reflexivity|] | apply uint_ready_binary].
'''
for node, entry in sorted(data['nodes'].items()):
    refs = entry['dependencies']
    out += f'Lemma x0_uint_result_{node} invalid site mm old result :\n'
    for ref in refs:
        out += f' (exists width bits, VM.find {ref} old = Some (Gval (Fuint width) bits)) ->\n'
    out += f' eval_hfexpr_validif_policy invalid site mm x0_concrete_expr_{node} old old = Some result ->\n concrete_uint_value result.\nProof.\n'
    for ref in refs:
        out += f' intros [w{ref} [b{ref} H{ref}]].\n'
    if 'Emux' not in entry['expression']:
        out += f' apply formal_uint_scalar_concrete. unfold x0_concrete_expr_{node}. solve_uint_ready.\n'
    else:
        out += f' intro Eval. unfold x0_concrete_expr_{node} in Eval.\n'
        out += ' cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Eval.\n'
        out += ' rewrite ' + ' '.join('?' + f'H{r}' for r in refs) + ' in Eval.\n'
        out += ' unfold eval_type_of_expr in Eval. cbn [type_of_expr\' eval_type_of_ref] in Eval.\n'
        out += ' rewrite ' + ' '.join('?' + f'H{r}' for r in refs) + ' in Eval.\n'
        out += ' repeat match type of Eval with context [if is_zero ?bits then _ else _] => destruct (is_zero bits) end;\n'
        out += ' cbn [option_map type_of_val extend_hvalue_as_type adapt_hvalue_as_type ftype_mux fgtyp_mux] in Eval;\n'
        out += ' inversion Eval; subst; do 2 eexists; reflexivity.\n'
    out += 'Qed.\n'
out += 'Print Assumptions x0_uint_result_7941.\n'
generated_path = root / 'formal/flat-low/staged-integration/X0UIntExpressionCertificates.v'
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print(f'Generated {len(data["nodes"])} UInt expression certificates.')
