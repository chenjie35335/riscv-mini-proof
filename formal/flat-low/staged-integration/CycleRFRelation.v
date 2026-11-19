Require Import CycleView CycleInitialState RFArchitecturalRelation.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import HiEnv_with_implicit_widths.
Local Open Scope N_scope.
(* Exact bridge to the existing architectural assertion interface. *)
Lemma cycle_architectural_pairs_indexed :
 rf_architectural_register_pairs =
 List.map (fun index => ((851+index)%nat,(7299+index)%nat)) (List.seq 0 32).
Proof. reflexivity. Qed.
Theorem cycle_rf_relation_sound env v :
 cycle_view_at env v -> cycle_banks_agree v -> rf_architectural_relation env.
Proof.
 intros View Agree. unfold rf_architectural_relation.
 rewrite cycle_architectural_pairs_indexed List.Forall_forall.
 intros pair Member. apply List.in_map_iff in Member.
 destruct Member as [index [Pair Member]]. subst pair.
 apply List.in_seq in Member. assert (Bound:(index<32)%coq_nat) by lia.
 destruct (cva_dut_bank _ _ View index Bound) as [Width Dut].
 destruct (cva_reference_bank _ _ View index Bound) as [_ Reference].
 exists (cv_dut_bank v index). split;[exact Width|].
 split;[exact Dut|]. cbn [fst snd]. rewrite (Agree index Bound). exact Reference.
Qed.
Theorem cycle_rf_relation_complete env v :
 cycle_view_at env v -> rf_architectural_relation env -> cycle_banks_agree v.
Proof.
 intros View Relation index Bound. unfold rf_architectural_relation in Relation.
 rewrite List.Forall_forall in Relation.
 destruct (Relation _ (cycle_architectural_pair_index index Bound)) as [word [Width [Dut Reference]]].
 destruct (cva_dut_bank _ _ View index Bound) as [_ DutView].
 destruct (cva_reference_bank _ _ View index Bound) as [_ ReferenceView].
 cbn [fst snd] in Dut,Reference. rewrite DutView in Dut. rewrite ReferenceView in Reference.
 congruence.
Qed.
Theorem cycle_rf_relation_exact env v :
 cycle_view_at env v -> (cycle_banks_agree v <-> rf_architectural_relation env).
Proof.
 intro View. split;[apply cycle_rf_relation_sound|apply cycle_rf_relation_complete];exact View.
Qed.
