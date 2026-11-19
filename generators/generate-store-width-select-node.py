from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
rows=[];positions=[]
for n in [7996]:
 needle=f'(@Snode VarOrder.T {n} ';a=s.index(needle)+len(needle);d=0
 for b in range(a,len(s)):
  d+=(s[b]=='(')-(s[b]==')')
  if d==0:break
 rows.append((n,s[a:b+1]));positions.append(bisect.bisect_right(q,a)-1)
template=(base/'staged-integration/StoreShiftNode.v').read_text();head=template[:template.index('Definition store_shift_expression')]
text=head+'\n'.join(f'Definition store_width_select_expr_{n} := {expr}.' for n,expr in rows)+'\n'
text+='Definition store_width_select_nodes := [::'+';'.join(f'({n},store_width_select_expr_{n})' for n,_ in rows)+'].\n'
offsets=[positions[0]]+[b-a-1 for a,b in zip(positions,positions[1:])]
text+='Definition store_width_select_offsets := [::'+';'.join(str(n)+'%nat' for n in offsets)+'].\n'
text+='''Lemma store_width_select_positions : select_node_offsets store_width_select_offsets flat_statements=Some store_width_select_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma store_width_select_safety : selected_node_safety flat_memories flat_statements store_width_select_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Theorem store_width_select_node_step node expr invalid old current result ground bits :
 List.In(node,expr)store_width_select_nodes ->
 (forall site,eval_hfexpr_validif_policy(isolated_validif_policy invalid)site flat_memories expr old old=Some(Gval ground bits)) ->
 formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find node result=Some(Gval ground bits).
Proof.
 intros Member Eval Step. eapply(reference_redirect_ground_step store_width_select_offsets store_width_select_nodes node expr);
 [exact store_width_select_positions|exact store_width_select_safety|exact Member|exact Eval|exact Step].
Qed.
'''
(base/'staged-integration/StoreWidthSelectNode.v').write_text(text)
