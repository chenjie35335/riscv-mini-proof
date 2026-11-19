"""Parameterize the 32 original RF assertion predicates; preserve semantic proof prefix."""
from pathlib import Path
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration/RFArchitecturalWriteEffect.v';s=p.read_text();marker='(* Original RF assertion interface. *)';s=s.split(marker,1)[0]
out=marker+'\nRequire Import FormalAssertionDischarge ComparisonTruth AssertionInstances PipelinePCAssertions.\n'
out+='Definition rf_original_assertion_local(index:nat)(env:VM.t hvalue):Prop := nth(fun _=>False)[::'+ ';'.join(f'generated_assert_m0_{i}_local'for i in range(8,40))+']index env.\n'
out+='Definition rf_original_assertion_all(index:nat)(states:SVM.t(VM.t hvalue)):Prop := nth(fun _=>False)[::'+ ';'.join(f'generated_assert_m0_{i}_all'for i in range(8,40))+']index states.\n'
out+='''Lemma rf_original_assertion_at_top index states env :(index<32)%coq_nat ->SVM.find nil states=Some env ->rf_original_assertion_local index env ->rf_original_assertion_all index states.
Proof. intros Bound Env Local.
'''
for i in range(32):
 out+=f' destruct index as[|index]. {{ apply(proj2(assertion_{i+8}_at_top states)). rewrite Env. exact Local. }}\n'
out+=' lia. Qed.\n'
out+='''Theorem rf_original_assertion_from_common_effect index invalid old result states bank effect :
 (index<32)%coq_nat ->SVM.find nil states=Some result ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 (generated_expr_true(pipeline_pc_enable 1395(pipeline_pc_guard_id(S index)))result ->
 VM.find(N.of_nat(Nat.add 1399 index))old=Some(Gval(Fuint 32)(rf_apply_effect bank effect index)) /\\
 VM.find(N.of_nat(Nat.add 1597 index))old=Some(Gval(Fuint 32)(rf_apply_effect bank effect index))) ->
 rf_original_assertion_all index states.
Proof.
 intros Bound Env Step Sources. eapply rf_original_assertion_at_top;[exact Bound|exact Env|].
'''
for i in range(32):
 out+=f' destruct index as[|index]. {{ apply(assertion_{i+8}_from_enabled_agreement invalid old old result Step). intro Enabled. destruct(Sources Enabled)as[Left Right]. exists 32%nat,32%nat,(rf_apply_effect bank effect {i}%nat),(rf_apply_effect bank effect {i}%nat). repeat split;assumption. }}\n'
out+=' lia. Qed.\n';p.write_text(s+out)
