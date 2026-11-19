"""Batch two actual immediate mux chains, sharing a selected-suffix theorem."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration'
types=(base/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids[^\n]*\[::([^]]*)\]',types)[1].split(';')))
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
s='''Definition load_imm_mux_count upper := if upper then 11%nat else 8%nat.
Definition load_imm_mux_width upper := if upper then 32%nat else 12%nat.
Definition load_imm_mux_node upper n : VarOrder.T := (if upper then 2540 else 2239)+N.of_nat n.
Definition load_imm_mux_prefix upper : VarOrder.T := if upper then 2539 else 2238.
Definition load_imm_mux_guard upper n : VarOrder.T := nth 0 (if upper then [::1970;1966;1962;1958;1886;1951;1946;1941;1937;1933;1929] else [::1970;1966;1962;1958;1886;1937;1933;1929]) n.
Definition load_imm_mux_yes upper n : VarOrder.T := nth 0 (if upper then [::2317;2313;2309;2305;2301;2297;2292;2287;2260;2256;2252] else [::2218;2217;2216;2215;2214;2213;2212;2211]) n.
Definition load_imm_mux_expression upper n := @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (load_imm_mux_guard upper n)))
 (@Eref VarOrder.T (@Eid VarOrder.T (load_imm_mux_yes upper n)))
 (@Eref VarOrder.T (@Eid VarOrder.T (match n with O => load_imm_mux_prefix upper | S before => load_imm_mux_node upper before end))).
Lemma load_imm_mux_member upper n : (n < load_imm_mux_count upper)%coq_nat ->
 List.In (load_imm_mux_node upper n,load_imm_mux_expression upper n) (if upper then reference_control_2_nodes else reference_control_1_nodes).
Proof. intro Bound;destruct upper.
'''
for upper in [True,False]:
 s+=' -\n';ns=list(range(2540,2551)) if upper else list(range(2239,2247))
 for node in ns:s+=f' destruct n as [|n];[exact reference_control_member_{node}|].\n'
 s+=' cbn [load_imm_mux_count] in Bound;lia.\n'
s+='Qed.\n'
s+='''Theorem load_imm_mux_node_step upper n invalid old result word :
 (n < load_imm_mux_count upper)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy invalid) site flat_memories (load_imm_mux_expression upper n) old old = Some (Gval (Fuint (load_imm_mux_width upper)) word)) ->
 formal_value_iter invalid flat_memories old false old flat_statements = Some result ->
 VM.find (load_imm_mux_node upper n) result = Some (Gval (Fuint (load_imm_mux_width upper)) word).
Proof.
 intros Bound Eval Step. eapply (reference_redirect_ground_step (if upper then reference_control_2_offsets else reference_control_1_offsets) (if upper then reference_control_2_nodes else reference_control_1_nodes) _ (load_imm_mux_expression upper n));
 [destruct upper;[exact reference_control_2_positions|exact reference_control_1_positions]
 |destruct upper;[exact reference_control_2_safety|exact reference_control_1_safety]
 |apply load_imm_mux_member;exact Bound|exact Eval|exact Step].
Qed.
Theorem load_imm_mux_same upper n inputs path history limit reset time :
 (n < load_imm_mux_count upper)%coq_nat ->
 (forall i, (i <= limit)%coq_nat -> VM.find 1 (history i) = Some (Gval (Fuint 1) [::reset])) ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 VM.find (load_imm_mux_node upper n) (history time) = VM.find (load_imm_mux_node upper n) (history (S time)).
Proof. intros Bound Resets Steps Lower Upper;destruct upper.
'''
for upper in [True,False]:
 s+=' -\n';ns=list(range(2540,2551)) if upper else list(range(2239,2247))
 for node in ns:s+=f' destruct n as [|n];[apply (reference_control_stable_{node}_history inputs path history limit reset Resets Steps time (S time));lia|].\n'
 s+=' cbn [load_imm_mux_count] in Bound;lia.\n'
s+='Qed.\n'
s+='''Theorem load_imm_mux_branch_types upper n invalid history limit time :
 (n < load_imm_mux_count upper)%coq_nat ->
 (forall i, (i < limit)%coq_nat -> formal_value_iter invalid flat_memories (history i) false (history i) flat_statements = Some (history (S i))) ->
 (forall i, (200 <= i)%coq_nat -> (i <= limit)%coq_nat -> exists value, VM.find 1884 (history i) = Some value /\\ type_of_val value = Gtyp (Fuint 32)) ->
 (500 <= time)%coq_nat -> (time <= limit)%coq_nat ->
 (exists value, VM.find (load_imm_mux_yes upper n) (history time) = Some value /\\ type_of_val value = Gtyp (Fuint (load_imm_mux_width upper))) /\\
 (exists value, VM.find (match n with O => load_imm_mux_prefix upper | S before => load_imm_mux_node upper before end) (history time) = Some value /\\ type_of_val value = Gtyp (Fuint (load_imm_mux_width upper))).
Proof.
 intros Bound Steps Source Lower Upper;destruct upper.
'''
for upper in [True,False]:
 s+=' -\n';ys=[2317,2313,2309,2305,2301,2297,2292,2287,2260,2256,2252] if upper else [2218,2217,2216,2215,2214,2213,2212,2211]
 for j,y in enumerate(ys):
  no=(2539 if upper else 2238)+j
  s+=' destruct n as [|n].\n { split.\n'
  for v in [y,no]:s+=f' - exact (reference_immediate_types_history invalid history limit 200 Steps Source {ids.index(v)}%nat ltac:(vm_compute;lia) time ltac:(cbv [reference_immediate_rank reference_immediate_ranks nth];lia) Upper).\n'
  s+=' }\n'
 s+=' cbn [load_imm_mux_count] in Bound;lia.\n'
s+='Qed.\n'
aux=list(range(2214,2219))+[2247,2248]+list(range(2298,2318))+[2551,2552]
s+='Definition load_imm_aux_ids : seq VarOrder.T := '+seq(aux)+'.\n'
s+='Definition load_imm_aux_expressions : seq (hfexpr VarOrder.T) := '+seq('reference_control_expr_'+str(n) for n in aux)+'.\n'
s+='''Definition load_imm_aux_node i := nth 0 load_imm_aux_ids i.
Definition load_imm_aux_expression i := nth (@Econst VarOrder.T (Fuint 1) [::false]) load_imm_aux_expressions i.
Definition load_imm_aux_nodes i := if Nat.ltb i 27 then reference_control_1_nodes else reference_control_2_nodes.
Definition load_imm_aux_offsets i := if Nat.ltb i 27 then reference_control_1_offsets else reference_control_2_offsets.
Lemma load_imm_aux_member i : (i < 29)%coq_nat -> List.In (load_imm_aux_node i,load_imm_aux_expression i) (load_imm_aux_nodes i).
Proof. intro Bound.
'''
for n in aux:s+=f' destruct i as [|i];[exact reference_control_member_{n}|].\n'
s+=' lia.\nQed.\n'
s+='''Theorem load_imm_aux_value i inputs path history limit reset time width word :
 (i < 29)%coq_nat ->
 (forall t, (t <= limit)%coq_nat -> VM.find 1 (history t) = Some (Gval (Fuint 1) [::reset])) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (500 <= time)%coq_nat -> (time < limit)%coq_nat ->
 (forall site, eval_hfexpr_validif_policy (isolated_validif_policy (formal_invalid_policy inputs path)) site flat_memories (load_imm_aux_expression i) (history time) (history time) = Some (Gval (Fuint width) word)) ->
 VM.find (load_imm_aux_node i) (history time) = Some (Gval (Fuint width) word).
Proof.
 intros Bound Resets Steps Lower Upper Eval.
 assert (Stable : VM.find (load_imm_aux_node i) (history time) = VM.find (load_imm_aux_node i) (history (S time))).
 {
'''
for n in aux:s+=f' destruct i as [|i];[apply (reference_control_stable_{n}_history inputs path history limit reset Resets Steps time (S time));lia|].\n'
s+=' lia. }\n'
s+=''' rewrite Stable. eapply (reference_redirect_ground_step (load_imm_aux_offsets i) (load_imm_aux_nodes i) _ (load_imm_aux_expression i));
 [unfold load_imm_aux_offsets,load_imm_aux_nodes;destruct (Nat.ltb i 27);[exact reference_control_1_positions|exact reference_control_2_positions]
 |unfold load_imm_aux_offsets;destruct (Nat.ltb i 27);[exact reference_control_1_safety|exact reference_control_2_safety]
 |apply load_imm_aux_member;exact Bound|exact Eval|apply Steps;exact Upper].
Qed.
'''
p=base/'ReferenceLoadImmediate.v';mark='(* Generated immediate mux certificates. *)';endmark='(* Actual load immediate semantics. *)';old=p.read_text();prefix=old.split(mark,1)[0];tail=old.split(endmark,1)[1] if endmark in old else '\n';p.write_text(prefix+mark+'\n'+s+endmark+tail)
