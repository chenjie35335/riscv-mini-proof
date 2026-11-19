"""One indexed reference RF NOP entry theorem, from actual flat statements."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];proof=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text()
exprs={};pos={}
for n in list(range(3224,3255))+[3255]:
 m=re.search(r'\(@Snode VarOrder.T '+str(n)+r' ',s);j=m.end();d=1
 while d:d+=(s[j]=='(')-(s[j]==')');j+=1
 exprs[n]=s[m.end():j-1];pos[n]=s[:m.start()].count('(@Qcons VarOrder.T ')-1
out='''Require Import CoreSocModel ComparisonNodes RFReferenceNopRelation X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation FormalGroundNodeEquation.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_reference_entry_condition (index : nat) : hfexpr VarOrder.T :=
 match index with
'''
for i in range(1,32):
 e=exprs[3223+i];a=e.index('(@Eprim_binop');j=a;d=0
 while True:
  d+=(e[j]=='(')-(e[j]==')');j+=1
  if not d:break
 out+=f' | {i}%nat => {e[a:j]}\n'
out+=' | _ => @Econst VarOrder.T (Fuint 1) [::false]\n end.\n'
out+='''Definition rf_reference_entry_expr index := @Emux VarOrder.T (rf_reference_entry_condition index)
 (@Eref VarOrder.T (@Eid VarOrder.T 3222)) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (Nat.sub 2177 index)))).
'''
out+='Definition rf_reference_entry_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::'+ ';'.join(f'({3223+i},rf_reference_entry_expr {i}%nat)' for i in range(1,32))+f';(3255,{exprs[3255]})].\n'
offsets=[];prev=-1
for n in exprs:offsets.append(pos[n]-prev-1);prev=pos[n]
out+='Definition rf_reference_entry_offsets : seq nat := [::'+';'.join(f'{x}%nat' for x in offsets)+'].\n'
out+='''Lemma rf_reference_entry_positions : select_node_offsets rf_reference_entry_offsets flat_statements = Some rf_reference_entry_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reference_entry_safety : selected_node_safety flat_memories flat_statements rf_reference_entry_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reference_entry_member index : (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 List.In (N.of_nat (Nat.add 3223 index),rf_reference_entry_expr index) rf_reference_entry_nodes.
Proof.
 intros Lower Upper.
'''
for i in range(32):out+=' destruct index as [|index]. '+ ('{ lia. }\n' if i==0 else '{ vm_compute. tauto. }\n')
out+=' lia.\nQed.\n'
out+='''Lemma rf_reference_entry_condition_false index mm old :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 VM.find 3221 old = Some (Gval (Fuint 5) [::false;false;false;false;false]) ->
 eval_hfexpr_with_memory mm (rf_reference_entry_condition index) old old = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Lower Upper Rd.
'''
for i in range(32):out+=' destruct index as [|index]. '+ ('{ lia. }\n' if i==0 else '{ cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }\n')
out+=' lia.\nQed.\n'
out+='''Lemma rf_reference_entry_policy_irrelevant index policy site mm old :
 eval_hfexpr_validif_policy policy site mm (rf_reference_entry_expr index) old old =
 eval_hfexpr_with_memory mm (rf_reference_entry_expr index) old old.
Proof.
 do 32 (destruct index as [|index]; [reflexivity|]). reflexivity.
Qed.
'''
out+='''Lemma rf_reference_condition_false_mux_extension mm old condition (yes no : VarOrder.T) base source :
 size base = 32%nat ->
 eval_hfexpr_with_memory mm condition old old = Some (Gval (Fuint 1) [::false]) ->
 VM.find no old = Some (Gval (Fuint 32) base) ->
 eval_hfexpr_with_memory mm (@Emux VarOrder.T condition (@Eref VarOrder.T (@Eid VarOrder.T yes)) (@Eref VarOrder.T (@Eid VarOrder.T no))) old old = Some source ->
 rf_reference_word_extension base source.
Proof.
 intros Size Condition No Eval.
 cbn [eval_hfexpr_with_memory] in Eval. rewrite Condition in Eval.
 change (is_zero [::false]) with true in Eval. cbn in Eval. rewrite No in Eval.
 destruct (eval_type_of_expr (Eref (Eid yes)) old) as [ty|]; [|discriminate].
 unfold extend_hvalue_as_type in Eval.
 destruct ty as [ground|element count|fields]; try discriminate.
 destruct ground; cbn [type_of_val ftype_mux fgtyp_mux option_map adapt_hvalue_as_type] in Eval; try discriminate.
 inversion Eval; subst source. exists (maxn 32 n). split.
 - exact (leq_maxl _ _).
 - f_equal. rewrite take_oversize; [reflexivity|rewrite Size; exact (leq_maxl _ _)].
Qed.
Theorem rf_reference_nop_entry index invalid old current result word :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat -> size word = 32%nat ->
 VM.find 3221 old = Some (Gval (Fuint 5) [::false;false;false;false;false]) ->
 VM.find (N.of_nat (Nat.sub 2177 index)) old = Some (Gval (Fuint 32) word) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find (N.of_nat (Nat.add 3223 index)) result = Some value /\\ rf_reference_word_extension word value.
Proof.
 intros Lower Upper Size Rd Old Step.
 pose proof (rf_reference_entry_member index Lower Upper) as Member.
 destruct (selected_node_safe_position flat_memories flat_statements rf_reference_entry_offsets flat_statements
 rf_reference_entry_nodes _ _ rf_reference_entry_positions rf_reference_entry_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 destruct (formal_successful_node_evaluation count flat_statements tail _ _ invalid flat_memories old false current result Position Step) as [value Eval].
 pose proof Eval as EvalPolicy. rewrite rf_reference_entry_policy_irrelevant in Eval.
 pose proof (rf_reference_entry_condition_false index flat_memories old Lower Upper Rd) as Condition.
 pose proof (rf_reference_condition_false_mux_extension flat_memories old (rf_reference_entry_condition index) 3222 (N.of_nat (Nat.sub 2177 index)) word value Size Condition Old Eval) as Extension.
 exists value. split; [|exact Extension].
 destruct Extension as [width [Width Value]]. subst value.
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg|exact EvalPolicy|reflexivity|exact Step].
Qed.
'''
out+='''Theorem rf_reference_nop_x0_entry invalid old current result :
 VM.find 1707 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 2177 old = Some (Gval (Fuint 32) (nseq 32 false)) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 VM.find 3255 result = Some (Gval (Fuint 32) (nseq 32 false)).
Proof.
 intros Enable Old Step.
 assert (Member : List.In (3255,@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 2177))) rf_reference_entry_nodes).
 { apply (List.nth_error_In rf_reference_entry_nodes 31%nat). vm_compute. reflexivity. }
 destruct (selected_node_safe_position flat_memories flat_statements rf_reference_entry_offsets flat_statements
 rf_reference_entry_nodes _ _ rf_reference_entry_positions rf_reference_entry_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy eval_hfexpr_with_memory eval_href_with_memory eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite Enable. cbn [is_zero]. unfold eval_type_of_expr. cbn [type_of_expr' eval_type_of_ref]. rewrite Old. vm_compute. reflexivity.
Qed.
'''
(proof/'RFReferenceNopEntry.v').write_text(out)
