"""Use one typed fallback chain for the actual final JAL immediate selection."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration';s=(p/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.',s).group(1).split(';')))
guards=[2010,2004,1998,1992,1986,1980,1974,1970,1966,1962,1958,1886,1951,1946,1941,1937,1933,1929]
yes=[2449,2445,2437,2429,2421,2413,2405,2317,2313,2309,2305,2301,2297,2292,2287,2260,2256,2252]
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='''Require Import DUTImmediateModes.
Lemma dut_j_immediate_canonical instruction : size instruction=32%nat ->
 dut_j_immediate instruction=sext_to 32(([::false]++drop 21(take 31 instruction))++(drop 20(take 21 instruction)++(drop 12(take 20 instruction)++drop 31(take 32 instruction)))).
Proof.
 intro Size. do 32(let b:=fresh "b" in destruct instruction as[|b instruction];[discriminate Size|];cbn[size]in Size).
 destruct instruction;[reflexivity|discriminate Size].
Qed.
'''
out+=f'''Definition jal_final_guard n : VarOrder.T :=nth 0 {seq(guards)} n.
Definition jal_final_yes n : VarOrder.T :=nth 0 {seq(yes)} n.
Definition jal_final_index n :=nth 0%nat {seq([str(ids.index(n))+'%nat' for n in range(2533,2551)])} n.
Definition jal_final_yes_index n :=nth 0%nat {seq([str(ids.index(n))+'%nat' for n in yes])} n.
Definition jal_final_node n : VarOrder.T :=2533+N.of_nat n.
Lemma jal_final_metadata n : (n<18)%coq_nat ->
 (jal_final_index n<304)%coq_nat /\\(jal_final_yes_index n<304)%coq_nat /\\
 reference_immediate_node(jal_final_index n)=jal_final_node n /\\
 reference_immediate_node(jal_final_yes_index n)=jal_final_yes n /\\
 reference_immediate_width(jal_final_yes_index n)=32%nat /\\
 reference_immediate_expression(jal_final_index n)=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T(jal_final_guard n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(jal_final_yes n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(match n with O=>2532|S before=>jal_final_node before end))).
Proof. do 18(destruct n as[|n];[vm_compute;intuition lia|]);lia. Qed.
Theorem reference_jal_final_history inputs path history limit reset time word :
 size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\\type_of_val value=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 VM.find 2357(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<18)%coq_nat ->VM.find(jal_final_guard n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2470(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Size Resets Steps Source Lower Upper Enabled Jal Guards Selected.
 assert(Start:VM.find 2532(history time)=Some(Gval(Fuint 32)word)).
 {{ eapply(reference_immediate_value_history {ids.index(2532)} inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. change(eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories reference_control_expr_2532(history time)(history time)=Some(Gval(Fuint 32)word)).
 destruct(reference_immediate_typed_history {ids.index(2531)} _ history limit time ltac:(lia) Steps Source Lower ltac:(lia))as[other[Other Typed]].
 change(VM.find 2531(history time)=Some other)in Other. change(type_of_val other=Gtyp(Fuint 32))in Typed.
 eapply(immediate_selected_mux _ _ _ _ _ _ _ word other true);[exact Size|exact Jal|exact Selected|exact Other|exact Typed]. }}
 assert(Final:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 {{ change(VM.find(jal_final_node 17)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_fallback (formal_invalid_policy inputs path)(history time)(history time)18 32 word 2532 jal_final_node jal_final_guard jal_final_yes);[exact Size|intros;reflexivity| |exact Guards| |exact Start|lia].
 - intros n Bound value Eval. destruct(jal_final_metadata n Bound)as[IB[YB[Node[Yes[Width Expr]]]]]. rewrite <-Node.
   eapply(reference_immediate_value_history (jal_final_index n) inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. destruct(jal_final_metadata n Bound)as[IB[YB[Node[Yes[Width Expr]]]]].
   pose proof(reference_immediate_typed_history (jal_final_yes_index n) _ history limit time YB Steps Source Lower ltac:(lia))as Typed. rewrite Yes Width in Typed;exact Typed. }}
 assert(EnabledValue:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 {{ eapply(load_imm_aux_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|].
 intro site. cbn[load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 32)word)(Gtyp(Fuint 32))=Some(Gval(Fuint 32)word)). apply dut_decode_adapt;exact Size. }}
 eapply(load_imm_aux_value 28 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact EnabledValue.
Qed.
'''
target=p/'ReferenceBranchImmediate.v';old=target.read_text();marker='(* Final immediate composition. *)';tail='(* JAL complete history. *)'+old.split('(* JAL complete history. *)',1)[1]if'(* JAL complete history. *)'in old else'';target.write_text(old.split(marker)[0]+marker+'\n'+out+tail)
