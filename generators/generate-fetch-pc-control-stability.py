import json
from pathlib import Path
p=Path('formal/flat-low'); q=p/'staged-integration'
cone=json.loads((p/'pc-decode-cone.json').read_text());order=json.loads((p/'pc-decode-order.json').read_text())
out='''Require Import FormalPCDecodeNodeCertificates PCDecodeExpressionValues FormalPCDecodeInputConnections FormalPCDecodeConnections CoreSocModel ComparisonNodes FormalLocalHistory.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem fetch_pc_decode_history_same invalid history (n : nat) :
 (forall i, (i < n)%coq_nat -> formal_flat_local_step invalid (history i) (history (S i))) ->
 (forall t u, (t <= n)%coq_nat -> (u <= n)%coq_nat -> exists word,
 VM.find 7748 (history t) = Some (Gval (Fuint 32) word) /\\ VM.find 7748 (history u) = Some (Gval (Fuint 32) word)) ->
 forall t u, (55 <= t)%coq_nat -> (55 <= u)%coq_nat -> (t <= n)%coq_nat -> (u <= n)%coq_nat ->
 exists word, VM.find 84 (history t) = Some (Gval (Fuint 2) word) /\\ VM.find 84 (history u) = Some (Gval (Fuint 2) word).
Proof.
 intros Steps V7748.
'''
for node in order['order']:
 item=cone['nodes'][str(node)];refs=item['dependencies'];depth=order['depths'][str(node)];ast=item['ast'];eq='(Bcomp Beq)' in ast
 width=1 if eq else 2 if 'Emux' in ast or node in [84,8250] else 32
 result='bit' if eq else 'word';value='[::bit]' if eq else 'word'
 out+=f''' assert (V{node} : forall t u, (Nat.le {depth} t /\\ Nat.le t n) -> (Nat.le {depth} u /\\ Nat.le u n) -> exists {result}, VM.find {node} (history t) = Some (Gval (Fuint {width}) {value}) /\\ VM.find {node} (history u) = Some (Gval (Fuint {width}) {value})).
 {{ intros t u BoundT BoundU. destruct t as [|t]; [lia|]. destruct u as [|u]; [lia|].
'''
 for k,ref in enumerate(refs):out+=f'   destruct (V{ref} t u ltac:(lia) ltac:(lia)) as [source{k} [Source{k} Other{k}]].\n'
 if ast.startswith('(@Sfcnct'):
  prefix='decode_input' if node in [83,8249] else 'pc_decode'
  out+=f'   eexists. split; eapply {prefix}_connection_{node}; [exact Source0|reflexivity|apply Steps;lia|exact Other0|reflexivity|apply Steps;lia].\n'
 else:
  args=' '.join(f'source{k}' for k in range(len(refs)));proofs=' '.join(f'Source{k}' for k in range(len(refs)))
  out+=f'''   destruct (decode_eval_{node} flat_memories (history t) {args} {proofs}) as [value Eval].
   assert (Equal : eval_hfexpr_with_memory flat_memories decode_expr_{node} (history u) (history u) = eval_hfexpr_with_memory flat_memories decode_expr_{node} (history t) (history t)).
   {{ cbn [decode_expr_{node} eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
     try unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref].
'''
  for k in range(len(refs)):out+=f'     rewrite Source{k} Other{k}.\n'
  out+='     reflexivity. }\n'
  out+=f'''   exists value. split.
   - exact (decode_node_{node} invalid (history t) (history t) (history (S t)) _ Eval (Logic.eq_refl _) (Steps t ltac:(lia))).
   - apply (decode_node_{node} invalid (history u) (history u) (history (S u))); [rewrite Equal;exact Eval|reflexivity|apply Steps;lia].
'''
 out+=' }\n'
out+=' intros t u LT LU UT UU. apply V84; lia.\nQed.\n'
(q/'FetchPCDecodeStability.v').write_text(out)
