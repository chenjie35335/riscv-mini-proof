Require Import CycleView CycleViewConstruction CycleViewObserved RFArchitecturalRelation RFArchitecturalObservedRelation RFArchitecturalResetRelation PipelinePCRelation ObservedPipelinePCRelation CoreSocModel ComparisonNodes ConcreteRegisterInitialization FormalLocalHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma cycle_architectural_relation_concrete env :
 rf_architectural_relation env ->rf_architectural_registers_concrete env.
Proof.
 intros Relation node Member. unfold rf_architectural_relation in Relation.
 rewrite List.Forall_forall in Relation.
 assert(Ids:rf_architectural_register_ids=List.flat_map(fun pair=>[::fst pair;snd pair])rf_architectural_register_pairs)by reflexivity.
 rewrite Ids in Member. apply List.in_flat_map in Member.
 destruct Member as[pair[Pair Member]]. destruct(Relation pair Pair)as[word[Size[Dut Reference]]].
 cbn in Member. destruct Member as[Member|[Member|Member]];try contradiction;subst node;
 exists word;split;try exact Size;assumption.
Qed.
Lemma cycle_architectural_pair_index index : (index<32)%coq_nat ->
 List.In((851+index)%nat,(7299+index)%nat)rf_architectural_register_pairs.
Proof.
 intro Bound.
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 0%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 1%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 2%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 3%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 4%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 5%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 6%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 7%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 8%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 9%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 10%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 11%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 12%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 13%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 14%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 15%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 16%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 17%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 18%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 19%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 20%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 21%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 22%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 23%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 24%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 25%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 26%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 27%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 28%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 29%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 30%nat);vm_compute;reflexivity|].
 destruct index as[|index];[apply(List.nth_error_In rf_architectural_register_pairs 31%nat);vm_compute;reflexivity|].
 lia. Qed.
Lemma cycle_architectural_relation_banks env :
 rf_architectural_relation env ->cycle_banks_agree(cycle_snapshot env).
Proof.
 intros Relation index Bound. unfold rf_architectural_relation in Relation.
 rewrite List.Forall_forall in Relation.
 destruct(Relation ((851+index)%nat,(7299+index)%nat)(cycle_architectural_pair_index index Bound))as[word[Size[Dut Reference]]].
 cbn [fst snd]in Dut,Reference. change(cycle_word env(N.of_nat(851+index)%nat)=cycle_word env(N.of_nat(7299+index)%nat)).
 unfold cycle_word. rewrite Dut Reference. reflexivity.
Qed.
Theorem cycle_initial_view memory inputs observed :
 generated_observe memory inputs 0=Some observed ->generated_legal_trace memory inputs 0 ->
 exists v,cycle_view_at(top_environment observed)v /\cycle_banks_agree v /\cycle_pc_aligned v.
Proof.
 intros Observe Legal.
 pose proof(rf_architectural_observe_zero memory inputs observed Observe)as Banks.
 assert(PC:pipeline_pc_relation(top_environment observed)).
 { pose proof Observe as Origin. unfold generated_observe in Origin.
   destruct(generated_run memory inputs 0)as[committed|]eqn:Run;[|discriminate Origin].
   destruct(pipeline_pc_relation_initial memory inputs committed Run)as[env[Env PC]].
   exact(observed_pipeline_pc_relation memory inputs 0 committed env observed Run Env Observe PC). }
 assert(View:cycle_view_at(top_environment observed)(cycle_snapshot(top_environment observed))).
 { apply(cycle_snapshot_from_reference_concrete memory inputs 0 observed Observe Legal).
   - apply cycle_architectural_relation_concrete;exact Banks.
   - destruct PC as[word[Size[Aligned[Value Phase]]]]. exists word;split;assumption. }
 exists(cycle_snapshot(top_environment observed));split;[exact View|].
 split;[apply cycle_architectural_relation_banks;exact Banks|].
 exact(cycle_pc_relation_complete _ _ View PC).
Qed.
Require Import StagedCircuitRegisterHold PipelineBubbleResetBase PipelineBubbleInitialization StagedObservedRegister.
Theorem cycle_initial_bubbles memory inputs observed v :
 generated_observe memory inputs 0=Some observed ->cycle_view_at(top_environment observed)v ->
 cv_early_bubble v=true /\cv_late_bubble v=true.
Proof.
 intros Observe View. pose proof Observe as Origin. unfold generated_observe in Origin.
 destruct(generated_run memory inputs 0)as[committed|]eqn:Run;[|discriminate Origin].
 destruct(pipeline_bubbles_run_zero memory inputs committed Run)as[env[Env[Early Late]]].
 pose proof(staged_observed_register_copies memory inputs 0 committed env observed 7945
 (Logic.eq_refl true)(Logic.eq_refl true)bubble7945_initial_safe bubble7945_present Run Env Observe)as EarlyCopy.
 pose proof(staged_observed_register_copies memory inputs 0 committed env observed 7947
 (Logic.eq_refl true)(Logic.eq_refl true)bubble7947_initial_safe bubble7947_present Run Env Observe)as LateCopy.
 rewrite Early in EarlyCopy. rewrite Late in LateCopy.
 unfold staged_register_lookup in EarlyCopy,LateCopy.
 assert(EarlyObserved:VM.find 7945(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { unfold top_environment. destruct(SVM.find nil observed);[exact EarlyCopy|discriminate EarlyCopy]. }
 assert(LateObserved:VM.find 7947(top_environment observed)=Some(Gval(Fuint 1)[::true])).
 { unfold top_environment. destruct(SVM.find nil observed);[exact LateCopy|discriminate LateCopy]. }
 split;[pose proof(cva_early_bubble _ _ View)|pose proof(cva_late_bubble _ _ View)];congruence.
Qed.
Theorem cycle_initial_base memory inputs observed :
 generated_observe memory inputs 0=Some observed ->generated_legal_trace memory inputs 0 ->
 exists v,cycle_view_at(top_environment observed)v /\cycle_banks_agree v /\cycle_pc_aligned v /\
 cv_early_bubble v=true /\cv_late_bubble v=true.
Proof.
 intros Observe Legal. destruct(cycle_initial_view memory inputs observed Observe Legal)as[v[View[Banks PC]]].
 exists v. split;[exact View|]. split;[exact Banks|]. split;[exact PC|].
 exact(cycle_initial_bubbles memory inputs observed v Observe View).
Qed.
