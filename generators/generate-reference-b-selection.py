"""Four field mux chains share one six-way selected-expression proof."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration';s=(p/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.',s).group(1).split(';')))
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
mat=lambda rows:seq([seq([str(ids.index(n))+'%nat'for n in row])for row in rows])
nodes=[[base+n for n in range(6)]for base in[2324,2362,2377,2392]];yes=[[2323-n for n in range(6)],[2355-4*n for n in range(6)],[2376-n for n in range(6)],[2391-n for n in range(6)]]
out=f'''Definition branch_field_stage group :=nth 0%nat [::7%nat;6%nat;8%nat;9%nat]group.
Definition branch_field_width group :=branch_raw_width(branch_field_stage group).
Definition branch_field_word group instruction :=branch_raw_word(branch_field_stage group)instruction.
Definition branch_field_index group n :=nth 0%nat(nth [::]{mat(nodes)}group)n.
Definition branch_field_yes_index group n :=nth 0%nat(nth [::]{mat(yes)}group)n.
Definition branch_field_node group n :=reference_immediate_node(branch_field_index group n).
Definition branch_field_yes group n :=reference_immediate_node(branch_field_yes_index group n).
Definition branch_field_guard n : VarOrder.T :=nth 0 [::2004;1998;1992;1986;1980;1974]n.
Definition branch_field_prefix group :=if Nat.eqb group 1 then @Eref VarOrder.T (@Eid VarOrder.T 2361)
 else @Econst VarOrder.T (Fuint(branch_field_width group))(nseq(branch_field_width group)false).
Lemma branch_field_metadata group n : (group<4)%coq_nat ->(n<6)%coq_nat ->
 (branch_field_index group n<304)%coq_nat /\\(branch_field_yes_index group n<304)%coq_nat /\\
 reference_immediate_width(branch_field_index group n)=branch_field_width group /\\
 reference_immediate_width(branch_field_yes_index group n)=branch_field_width group /\\
 reference_immediate_expression(branch_field_index group n)=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T(branch_field_guard n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(branch_field_yes group n)))
 (match n with O=>branch_field_prefix group|S before=>@Eref VarOrder.T (@Eid VarOrder.T(branch_field_node group before))end).
Proof. do 4(destruct group as[|group];[do 6(destruct n as[|n];[vm_compute;intuition lia|]);lia|]);lia. Qed.
Lemma branch_field_selected group lane : (group<4)%coq_nat ->(lane<6)%coq_nat ->
 (branch_field_stage group<10)%coq_nat /\\branch_field_yes group(Nat.sub 5 lane)=branch_raw_node(branch_field_stage group)lane.
Proof. do 4(destruct group as[|group];[do 6(destruct lane as[|lane];[vm_compute;intuition lia|]);lia|]);lia. Qed.
Lemma branch_field_size group instruction : (group<4)%coq_nat ->size instruction=32%nat ->size(branch_field_word group instruction)=branch_field_width group.
Proof. intros Group Size. do 4(destruct group as[|group];[cbn[branch_field_word branch_field_width branch_field_stage branch_raw_word branch_raw_width nth];rewrite size_drop size_take Size;reflexivity|]);lia. Qed.
Lemma immediate_ref_type old node width value : VM.find node old=Some value ->type_of_val value=Gtyp(Fuint width) ->
 eval_type_of_expr(@Eref VarOrder.T (@Eid VarOrder.T node))old=Some(Gtyp(Fuint width)).
Proof. intros Lookup Typed. unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite Lookup;cbn[option_map];rewrite Typed;reflexivity. Qed.
Theorem branch_field_mux_history group lane inputs path history limit reset time instruction :
 (group<4)%coq_nat ->(lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 VM.find(branch_field_node group 5)(history time)=Some(Gval(Fuint(branch_field_width group))(branch_field_word group instruction)).
Proof.
 intros Group Lane Size Resets Steps Source Lower Upper Guards.
 assert(TypedSource:forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\\type_of_val value=Gtyp(Fuint 32)).
 {{ intros t L U;exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity]. }}
 eapply(immediate_stable_expression_suffix (isolated_validif_policy(formal_invalid_policy inputs path))(history time)6(Nat.sub 5 lane)(branch_field_width group)(branch_field_word group instruction)(branch_field_prefix group)(branch_field_node group)branch_field_guard(fun n=>@Eref VarOrder.T (@Eid VarOrder.T(branch_field_yes group n))));[lia|apply branch_field_size;assumption| |exact Guards| | | |lia|lia].
 - intros n Bound value Eval. destruct(branch_field_metadata group n Group Bound)as[IB[YB[Width[YesWidth Expr]]]].
 eapply(reference_immediate_value_history (branch_field_index group n) inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. destruct(branch_field_metadata group n Group Bound)as[IB[YB[Width[YesWidth Expr]]]].
 destruct(reference_immediate_typed_history (branch_field_yes_index group n) _ history limit time YB Steps TypedSource Lower ltac:(lia))as[value[Lookup Typed]].
 eapply immediate_ref_type;[exact Lookup|rewrite YesWidth in Typed;exact Typed].
 - intros n Bound. destruct n as[|n].
   + destruct group as[|[|[|[|group]]]];[vm_compute;reflexivity| |vm_compute;reflexivity|vm_compute;reflexivity|lia].
     destruct(reference_immediate_typed_history {ids.index(2361)} _ history limit time ltac:(lia) Steps TypedSource Lower ltac:(lia))as[value[Lookup Typed]].
     eapply immediate_ref_type;[exact Lookup|exact Typed].
   + destruct(branch_field_metadata group n Group ltac:(lia))as[IB[YB[Width[YesWidth Expr]]]].
     destruct(reference_immediate_typed_history (branch_field_index group n) _ history limit time IB Steps TypedSource Lower ltac:(lia))as[value[Lookup Typed]].
     eapply immediate_ref_type;[exact Lookup|rewrite Width in Typed;exact Typed].
 - intro site. destruct(branch_field_selected group lane Group Lane)as[Stage Selected].
 cbn[eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Selected.
 exact(branch_raw_fields_history inputs path history limit reset time instruction lane Lane Resets Steps Lower Upper ltac:(apply Source;lia)(branch_field_stage group)Stage).
Qed.
'''
target=p/'ReferenceConditionalBranchImmediate.v';old=target.read_text();marker='(* Four branch field selections. *)';tail='(* Branch field enable. *)'+old.split('(* Branch field enable. *)',1)[1]if'(* Branch field enable. *)'in old else'';target.write_text(old.split(marker)[0]+marker+'\n'+out+tail)
