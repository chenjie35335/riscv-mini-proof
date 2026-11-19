"""Generate expression lemmas from the saved flat-model decoder cone.
The generated lemmas prove expression evaluation only, not circuit assertions.
"""
import json
import re
from pathlib import Path
p = Path('formal/flat-low')
cone = json.loads((p / 'pc-decode-cone.json').read_text())
order = json.loads((p / 'pc-decode-order.json').read_text())['order']
out = '''Require Import ConcreteDecodeOperations.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
count = 0
for n in order:
    item = cone['nodes'][str(n)]
    stmt = item['ast']
    if not stmt.startswith('(@Snode'):
        continue
    expr = stmt.split(f'(@Snode VarOrder.T {n} ', 1)[1][:-1]
    refs = item['dependencies']
    cw, cb = re.search(r'\(@Econst VarOrder.T \(Fuint (\d+)\) (\[::[^]]*\])\)', expr).groups()
    out += f'Definition decode_expr_{n} := {expr}.\n'
    if 'Eprim_binop' in expr:
        equal = '(Bcomp Beq)' in expr
        result = 'bit' if equal else 'word'
        value = 'Gval (Fuint 1) [::bit]' if equal else 'Gval (Fuint 32) word'
        helper = 'concrete_equal_const_ref' if equal else 'concrete_mask_ref_const'
        out += f'''Lemma decode_eval_{n} mm old source_word :
 VM.find {refs[0]} old = Some (Gval (Fuint 32) source_word) ->
 exists {result}, eval_hfexpr_with_memory mm decode_expr_{n} old old = Some ({value}).
Proof.
 intro Source. unfold decode_expr_{n}.
 destruct ({helper} mm old {refs[0]} 32 source_word {cw} {cb} Source ltac:(reflexivity)) as [value Value].
 exists value. exact Value.
Qed.
'''
    else:
        out += f'''Lemma decode_eval_{n} mm old bit'''
        out += ' :\n' if len(refs) == 1 else ' source_word :\n'
        out += f' VM.find {refs[0]} old = Some (Gval (Fuint 1) [::bit]) ->\n'
        if len(refs) == 2:
            out += f' VM.find {refs[1]} old = Some (Gval (Fuint 2) source_word) ->\n'
        out += f' exists word, eval_hfexpr_with_memory mm decode_expr_{n} old old = Some (Gval (Fuint 2) word).\nProof.\n'
        if len(refs) == 1:
            out += f''' intro Condition. cbn [decode_expr_{n} eval_hfexpr_with_memory eval_href_with_memory].
 rewrite Condition. destruct bit; eexists; reflexivity.
'''
        else:
            out += f''' intros Condition Source. unfold decode_expr_{n}.
 destruct (concrete_uint_mux_const_ref mm old {refs[0]} {refs[1]} bit {cw} 2 {cb} source_word Condition Source ltac:(reflexivity)) as [word Value].
 exists word. exact Value.
'''
        out += 'Qed.\n'
    count += 1
out += 'Print Assumptions decode_eval_8409.\n'
(p / 'PCDecodeExpressionValues.v').write_text(out)
print(f'Generated {count} expression lemmas; no assertion is discharged.')
