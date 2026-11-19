Require Import CoreSocModel ComparisonNodes FlatRegFileX0 FormalX0ConeNodes.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Lemma real_iteration_rf_round invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 rf_x0_round old result.
Proof.
 intro Step. unfold rf_x0_round.
 split; [rewrite (node_953_full_iteration invalid old current result Step); reflexivity|].
 split; [rewrite (node_954_full_iteration invalid old current result Step); reflexivity|].
 split; [rewrite (node_989_full_iteration invalid old current result Step); reflexivity|].
 rewrite (node_1053_full_iteration invalid old current result Step); reflexivity.
Qed.
Theorem real_three_iterations_rf_x0 invalid first second third fourth enable address data :
 size address = 5 ->
 eval_href rf_addr_ref first first = Some (Gval (Fuint 5) address) ->
 eval_href rf_addr_ref second second = Some (Gval (Fuint 5) address) ->
 eval_href rf_enable_ref second second = Some (Gval (Fuint 1) [::enable]) ->
 VM.find (BinNat.N.of_nat 988) second = Some (Gval (Fuint 32) data) ->
 formal_value_iter invalid flat_memories first false first flat_statements = Some second ->
 formal_value_iter invalid flat_memories second false second flat_statements = Some third ->
 formal_value_iter invalid flat_memories third false third flat_statements = Some fourth ->
 VM.find (BinNat.N.of_nat 1053) fourth = Some rf_zero32.
Proof.
 intros Width First Second Enable Data Step1 Step2 Step3.
 eapply rf_x0_after_three_rounds;
 [exact Width|exact First|exact Second|exact Enable|exact Data| | |].
 - eapply real_iteration_rf_round. exact Step1.
 - eapply real_iteration_rf_round. exact Step2.
 - eapply real_iteration_rf_round. exact Step3.
Qed.
Print Assumptions real_three_iterations_rf_x0.
Require Import FlatRegFileUnknownData.
From firrtl Require Import HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths.
Theorem real_three_iterations_rf_x0_typed invalid first second third fourth enable b0 b1 b2 b3 b4 source :
 eval_href rf_addr_ref first first = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 eval_href rf_addr_ref second second = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 eval_href rf_enable_ref second second = Some (Gval (Fuint 1) [::enable]) ->
 VM.find (BinNat.N.of_nat 988) second = Some source ->
 type_of_val source = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories first false first flat_statements = Some second ->
 formal_value_iter invalid flat_memories second false second flat_statements = Some third ->
 formal_value_iter invalid flat_memories third false third flat_statements = Some fourth ->
 VM.find (BinNat.N.of_nat 1053) fourth = Some rf_zero32.
Proof.
 intros First Second Enable Data Typed Step1 Step2 Step3.
 pose proof (real_iteration_rf_round invalid first first second Step1) as R1.
 pose proof (real_iteration_rf_round invalid second second third Step2) as R2.
 pose proof (real_iteration_rf_round invalid third third fourth Step3) as R3.
 destruct (rf_selected_total second b0 b1 b2 b3 b4 source Second Data Typed) as [selected [Eval SelectedType]].
 pose proof R2 as [_ [_ [Selected _]]]. rewrite Eval in Selected.
 eapply rf_three_rounds_unknown_data;
 [exact First|exact Second|exact Enable|exact Data|exact Typed| |exact R1|exact R2|exact R3].
 cbn [eval_type_of_ref]. rewrite Selected. cbn [option_map]. rewrite SelectedType. reflexivity.
Qed.
Print Assumptions real_three_iterations_rf_x0_typed.
