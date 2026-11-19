"""Generate flat statement certificates for the decoder expression lemmas."""
import json
from pathlib import Path
p=Path('formal/flat-low')
cone=json.loads((p/'pc-decode-cone.json').read_text())
order=json.loads((p/'pc-decode-order.json').read_text())['order']
out='''Require Import PCDecodeExpressionValues CoreSocModel ComparisonNodes TypedMemoryCertificates TypedMemoryFrames ScalarNodeFrames StatementSegments RegisterInvariants.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
count=0
for n in order:
 item=cone['nodes'][str(n)]
 if not item['ast'].startswith('(@Snode'):continue
 pos=item['position']
 width=1 if '(Bcomp Beq)' in item['ast'] else 2 if 'Emux' in item['ast'] else 32
 out+=f'''Definition decode_tail_{n} := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma decode_position_{n} : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} decode_expr_{n}) decode_tail_{n}).
Proof. vm_compute. reflexivity. Qed.
Lemma decode_suffix_{n} : typed_memory_suffix_safe flat_memories {n} decode_tail_{n}.
Proof. apply typed_memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma decode_nonregister_{n} : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem decode_node_{n} invalid old phase current result value :
 eval_hfexpr_with_memory flat_memories decode_expr_{n} old old = Some value ->
 type_of_val value = Gtyp (Fuint {width}) ->
 value_iter_with_memory_policy invalid flat_memories old phase current flat_statements = Some result ->
 VM.find {n} result = Some value.
Proof.
 intros Eval Typed Step. eapply full_iteration_known_node;
 [exact decode_position_{n}|exact decode_suffix_{n}|exact decode_nonregister_{n}|exact Eval|exact Typed|exact Step].
Qed.
'''
 count+=1
out+='Print Assumptions decode_node_8409.\n'
(p/'PCDecodeNodeCertificates.v').write_text(out)
print(f'Generated {count} node certificates, pending Coq validation.')
