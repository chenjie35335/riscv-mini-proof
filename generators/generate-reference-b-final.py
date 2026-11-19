"""Six-way B immediate selection and the shared all-false upper suffix."""
from pathlib import Path
import re
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration';s=(p/'ReferenceImmediateTypes.v').read_text();ids=list(map(int,re.search(r'Definition reference_immediate_ids .*? := \[::(.*?)\]\.',s).group(1).split(';')))
seq=lambda xs:'[::'+';'.join(map(str,xs))+']'
out='Require Import DUTImmediateModes.\n'
out+=f'''Definition branch_final_index n :=nth 0%nat{seq([str(ids.index(n))+'%nat'for n in range(2534,2540)])}n.
Definition branch_final_node n :=reference_immediate_node(branch_final_index n).
Definition branch_final_yes_index n :=nth 0%nat{seq([str(ids.index(n))+'%nat'for n in[2445,2437,2429,2421,2413,2405]])}n.
Definition branch_final_yes n :=reference_immediate_node(branch_final_yes_index n).
Lemma branch_final_metadata n : (n<6)%coq_nat ->
 (branch_final_index n<304)%coq_nat /\\(branch_final_yes_index n<304)%coq_nat /\\
 reference_immediate_width(branch_final_index n)=32%nat /\\reference_immediate_width(branch_final_yes_index n)=32%nat /\\
 reference_immediate_expression(branch_final_index n)=@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T(branch_field_guard n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(branch_final_yes n)))
 (@Eref VarOrder.T (@Eid VarOrder.T(match n with O=>2533|S before=>branch_final_node before end))).
Proof. do 6(destruct n as[|n];[vm_compute;intuition lia|]);lia. Qed.
Lemma branch_final_selected lane : (lane<6)%coq_nat ->branch_final_yes(Nat.sub 5 lane)=branch_assembly_node lane 7.
Proof. do 6(destruct lane as[|lane];[reflexivity|]);lia. Qed.
Lemma branch_upper_metadata n : (n<11)%coq_nat ->
 (jal_final_index(Nat.add 7 n)<304)%coq_nat /\\
 reference_immediate_node(jal_final_index(Nat.add 7 n))=load_imm_mux_node true n /\\
 reference_immediate_expression(jal_final_index(Nat.add 7 n))=load_imm_mux_expression true n.
Proof. do 11(destruct n as[|n];[vm_compute;intuition lia|]);lia. Qed.
Theorem reference_branch_final_history lane inputs path history limit reset time word :
 (lane<6)%coq_nat ->size word=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->exists value,VM.find 1884(history t)=Some value /\\type_of_val value=Gtyp(Fuint 32)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 (forall n,(n<11)%coq_nat ->VM.find(load_imm_mux_guard true n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find(branch_assembly_node lane 7)(history time)=Some(Gval(Fuint 32)word) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)word).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards UpperGuards Selected.
 assert(Start:VM.find 2539(history time)=Some(Gval(Fuint 32)word)).
 {{ change(VM.find(branch_final_node 5)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_suffix (formal_invalid_policy inputs path)(history time)(history time)6(Nat.sub 5 lane)32 word 2533 branch_final_node branch_field_guard branch_final_yes);[lia|exact Size|intros;reflexivity| |exact Guards| | | |lia|lia].
 - intros n Bound value Eval. destruct(branch_final_metadata n Bound)as[IB[YB[Width[YesWidth Expr]]]].
   eapply(reference_immediate_value_history (branch_final_index n)inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. destruct(branch_final_metadata n Bound)as[IB[YB[Width[YesWidth Expr]]]].
   pose proof(reference_immediate_typed_history(branch_final_yes_index n)_ history limit time YB Steps Source Lower ltac:(lia))as Typed. rewrite YesWidth in Typed;exact Typed.
 - intros n Bound. destruct n as[|n].
   + exact(reference_immediate_typed_history {ids.index(2533)} _ history limit time ltac:(lia) Steps Source Lower ltac:(lia)).
   + destruct(branch_final_metadata n ltac:(lia))as[IB[YB[Width[YesWidth Expr]]]].
     pose proof(reference_immediate_typed_history(branch_final_index n)_ history limit time IB Steps Source Lower ltac:(lia))as Typed. rewrite Width in Typed;exact Typed.
 - rewrite(branch_final_selected lane Lane);exact Selected. }}
 assert(Final:VM.find 2550(history time)=Some(Gval(Fuint 32)word)).
 {{ change(VM.find(load_imm_mux_node true 10)(history time)=Some(Gval(Fuint 32)word)).
 eapply(immediate_stable_mux_fallback (formal_invalid_policy inputs path)(history time)(history time)11 32 word 2539(load_imm_mux_node true)(load_imm_mux_guard true)(load_imm_mux_yes true));[exact Size|intros;reflexivity| |exact UpperGuards| |exact Start|lia].
 - intros n Bound value Eval. destruct(branch_upper_metadata n Bound)as[IB[Node Expr]]. rewrite <-Node.
   eapply(reference_immediate_value_history (jal_final_index(Nat.add 7 n))inputs path history limit reset time);[exact IB|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;rewrite Expr;apply Eval.
 - intros n Bound. exact(proj1(load_imm_mux_branch_types true n _ history limit time Bound Steps Source Lower ltac:(lia))). }}
 assert(EnabledValue:VM.find 2551(history time)=Some(Gval(Fuint 32)word)).
 {{ eapply(load_imm_aux_value 27 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site.
 cbn[load_imm_aux_expression load_imm_aux_expressions nth reference_control_expr_2551 eval_hfexpr_validif_policy eval_href_validif_policy]. rewrite Enabled;cbn;rewrite Final.
 change(adapt_hvalue_as_type(Gval(Fuint 32)word)(Gtyp(Fuint 32))=Some(Gval(Fuint 32)word));apply dut_decode_adapt;exact Size. }}
 eapply(load_imm_aux_value 28 inputs path history limit reset time);[lia|exact Resets|exact Steps|exact Lower|exact Upper|]. intro site;exact EnabledValue.
Qed.
Theorem reference_branch_immediate_history lane inputs path history limit reset time instruction :
 (lane<6)%coq_nat ->size instruction=32%nat ->
 (forall t,(t<=limit)%coq_nat ->VM.find 1(history t)=Some(Gval(Fuint 1)[::reset])) ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter(formal_invalid_policy inputs path)flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(200<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 1884(history t)=Some(Gval(Fuint 32)instruction)) ->
 (500<=time)%coq_nat ->(time<limit)%coq_nat ->VM.find 1707(history time)=Some(Gval(Fuint 1)[::true]) ->
 (forall n,(n<6)%coq_nat ->VM.find(branch_field_guard n)(history time)=Some(Gval(Fuint 1)[::Nat.eqb n(Nat.sub 5 lane)])) ->
 (forall n,(n<11)%coq_nat ->VM.find(load_imm_mux_guard true n)(history time)=Some(Gval(Fuint 1)[::false])) ->
 VM.find 2552(history time)=Some(Gval(Fuint 32)(dut_b_immediate instruction)).
Proof.
 intros Lane Size Resets Steps Source Lower Upper Enabled Guards UpperGuards.
 pose proof(branch_field_output_history 0 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as Sign.
 pose proof(branch_field_output_history 1 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as Bit.
 pose proof(branch_field_output_history 2 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as High.
 pose proof(branch_field_output_history 3 lane inputs path history limit reset time instruction ltac:(lia) Lane Size Resets Steps Source Lower Upper Enabled Guards)as Low.
 pose proof(branch_assembly_history lane inputs path history limit reset time (drop 31(take 32 instruction))(drop 7(take 8 instruction))(drop 25(take 31 instruction))(drop 8(take 12 instruction))Lane
 ltac:(rewrite size_drop size_take Size;reflexivity)ltac:(rewrite size_drop size_take Size;reflexivity)ltac:(rewrite size_drop size_take Size;reflexivity)ltac:(rewrite size_drop size_take Size;reflexivity)
 Resets Steps Lower Upper Sign Bit High Low)as Value.
 eapply(reference_branch_final_history lane inputs path history limit reset time);[exact Lane|exact(dut_imm_result_size 2 instruction ltac:(lia) Size)|exact Resets|exact Steps| |exact Lower|exact Upper|exact Enabled|exact Guards|exact UpperGuards|exact Value].
 intros t L U;exists(Gval(Fuint 32)instruction);split;[apply Source;assumption|reflexivity].
Qed.
'''
target=p/'ReferenceConditionalBranchImmediate.v';old=target.read_text();marker='(* Final branch composition. *)';tail='(* Branch observed interface. *)'+old.split('(* Branch observed interface. *)',1)[1]if'(* Branch observed interface. *)'in old else'';target.write_text(old.split(marker)[0]+marker+'\n'+out+tail)
