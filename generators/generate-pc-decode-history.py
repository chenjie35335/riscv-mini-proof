"""Generate a depth induction connecting EX to the real PC decoder."""
import json
from pathlib import Path
p=Path('formal/flat-low')
cone=json.loads((p/'pc-decode-cone.json').read_text())
order=json.loads((p/'pc-decode-order.json').read_text())
out='''Require Import PCDecodeNodeCertificates PCDecodeExpressionValues PCDecodeInputConnections PCDecodeConnections CoreSocModel ComparisonNodes X0OutputPaths.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem pc_decode_history_concrete invalid history (n : nat) :
 (forall i, (i < n)%coq_nat -> flat_local_step invalid (history i) (history (S i))) ->
 (forall (j : nat), (j <= n)%coq_nat -> exists word, VM.find 7748 (history j) = Some (Gval (Fuint 32) word)) ->
 forall (j : nat), (Nat.le 55 j /\ Nat.le j n) -> exists word, VM.find 84 (history j) = Some (Gval (Fuint 2) word).
Proof.
 intros Steps V7748.
'''
for node in order['order']:
 item=cone['nodes'][str(node)];refs=item['dependencies'];depth=order['depths'][str(node)];ast=item['ast']
 eq='(Bcomp Beq)' in ast
 width=1 if eq else 2 if 'Emux' in ast or node in [84,8250] else 32
 result='bit' if eq else 'word';value='[::bit]' if eq else 'word'
 out+=f''' assert (V{node} : forall (j : nat), (Nat.le {depth} j /\ Nat.le j n) -> exists {result}, VM.find {node} (history j) = Some (Gval (Fuint {width}) {value})).
 {{ intros j Bound. destruct j as [|j]; [lia|].
'''
 for k,ref in enumerate(refs):
  out+=f'   destruct (V{ref} j ltac:(lia)) as [source{k} Source{k}].\n'
 if ast.startswith('(@Sfcnct'):
  prefix='decode_input' if node in [83,8249] else 'pc_decode'
  out+=f'   eexists. eapply {prefix}_connection_{node}; [exact Source0|reflexivity|apply Steps; lia].\n'
 else:
  args=' '.join(f'source{k}' for k in range(len(refs)))
  proofs=' '.join(f'Source{k}' for k in range(len(refs)))
  out+=f'''   destruct (decode_eval_{node} flat_memories (history j) {args} {proofs}) as [value Eval].
   exists value. eapply decode_node_{node}; [exact Eval|reflexivity|apply Steps; lia].
'''
 out+=' }\n'
out+=' exact V84.\nQed.\nPrint Assumptions pc_decode_history_concrete.\n'
(p/'PCDecodeHistoryConcrete.v').write_text(out)
print('Generated complete 55-layer history proof, pending Coq validation.')
