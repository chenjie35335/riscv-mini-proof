from pathlib import Path
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low'
model=(base/'CoreSocModel.v').read_text()
def expression(node):
 a=model.index(f'(@Snode VarOrder.T {node} ')+len(f'(@Snode VarOrder.T {node} ')
 depth=0
 for b in range(a,len(model)):
  depth+=(model[b]=='(')-(model[b]==')')
  if depth==0:return model[a:b+1]
text='''Require Import ReferenceWriteValidShapes ReferenceRequestSpine ReferenceRedirectSpine CoreSocModel ComparisonNodes.
From Coq Require Import NArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
'''
for node,idx,guard,yes,no in [(6641,20,None,None,None),(6642,21,1951,None,6641),(6668,26,1946,6659,6642),(6692,30,1941,6683,6668),(7113,34,1707,6692,6641)]:
 args=' other' if node in [6668,6692] else (' bit' if node==7113 else '')
 text+=f'Lemma reference_write_false_{node} invalid old current result{args} :\n'
 if guard:
  bit='bit' if node==7113 else 'false'
  text+=f' VM.find {guard} old=Some(Gval(Fuint 1)[::{bit}]) ->\n'
 if yes:
  if node==7113:text+=f' VM.find {yes} old=Some(Gval(Fuint 1)[::false]) ->\n'
  else:text+=f' VM.find {yes} old=Some other ->type_of_val other=Gtyp(Fuint 1) ->\n'
 if no:text+=f' VM.find {no} old=Some(Gval(Fuint 1)[::false]) ->\n'
 text+=f''' formal_value_iter invalid flat_memories old false current flat_statements=Some result ->
 VM.find {node} result=Some(Gval(Fuint 1)[::false]).
Proof.
'''
 names=('Guard ' if guard else '')+('Yes Typed ' if node in [6668,6692] else ('Yes ' if yes else ''))+('No ' if no else '')+'Step'
 text+=f' intros {names}.\n'
 text+=f''' eapply(reference_redirect_ground_step reference_request_offsets reference_request_nodes {node} {expression(node)});
 [exact reference_request_positions|exact reference_request_safety|apply(List.nth_error_In reference_request_nodes {idx}%nat);vm_compute;reflexivity| |exact Step].
 intro site.
'''
 if node in [6668,6692]:text+=' exact(reference_write_false_mux_typed invalid site old '+f'{guard} {yes} {no} other Guard Yes Typed No).\n'
 else:
  text+=' cbn[eval_hfexpr_validif_policy eval_href_validif_policy].\n'
  if node==6641:text+=' reflexivity.\n'
  elif node==6642:text+=' rewrite Guard. cbn. rewrite No. reflexivity.\n'
  else:text+=" rewrite Guard. destruct bit;cbn;rewrite ?Yes ?No;unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?Yes ?No;reflexivity.\n"
 text+='Qed.\n'
(base/'staged-integration/ReferenceWriteValidFalse.v').write_text(text)
