Require Import RegisterInvariants CoreSocModel ScalarNodeFrames MemoryWriteFrames MemorySuffixCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths
 HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition flat_statements :=
 match generated_module_0 with FInmod _ _ s | FExmod _ _ s => s end.
Definition flat_memories := memory_map_of_stmts flat_statements.
Definition comparison_0 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1474)) (@Eref VarOrder.T (@Eid VarOrder.T 1519))).
Definition tail_0 := match straight_drop 8035 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_0 : straight_drop 8034 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7565 comparison_0) tail_0).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_0 : memory_suffix_safe flat_memories 7565 tail_0.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_0 : has_register 7565 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_0_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7565 result = eval_hfexpr_with_memory flat_memories comparison_0 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_0|exact suffix_0|exact nonregister_0|exact Step]. Qed.
Definition comparison_1 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1475)) (@Eref VarOrder.T (@Eid VarOrder.T 1520))).
Definition tail_1 := match straight_drop 8040 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_1 : straight_drop 8039 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7570 comparison_1) tail_1).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_1 : memory_suffix_safe flat_memories 7570 tail_1.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_1 : has_register 7570 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_1_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7570 result = eval_hfexpr_with_memory flat_memories comparison_1 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_1|exact suffix_1|exact nonregister_1|exact Step]. Qed.
Definition comparison_2 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1476)) (@Eref VarOrder.T (@Eid VarOrder.T 1521))).
Definition tail_2 := match straight_drop 8044 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_2 : straight_drop 8043 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7574 comparison_2) tail_2).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_2 : memory_suffix_safe flat_memories 7574 tail_2.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_2 : has_register 7574 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_2_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7574 result = eval_hfexpr_with_memory flat_memories comparison_2 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_2|exact suffix_2|exact nonregister_2|exact Step]. Qed.
Definition comparison_3 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1478)) (@Eref VarOrder.T (@Eid VarOrder.T 1523))).
Definition tail_3 := match straight_drop 8048 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_3 : straight_drop 8047 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7578 comparison_3) tail_3).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_3 : memory_suffix_safe flat_memories 7578 tail_3.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_3 : has_register 7578 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_3_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7578 result = eval_hfexpr_with_memory flat_memories comparison_3 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_3|exact suffix_3|exact nonregister_3|exact Step]. Qed.
Definition comparison_4 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1479)) (@Eref VarOrder.T (@Eid VarOrder.T 1524))).
Definition tail_4 := match straight_drop 8053 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_4 : straight_drop 8052 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7583 comparison_4) tail_4).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_4 : memory_suffix_safe flat_memories 7583 tail_4.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_4 : has_register 7583 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_4_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7583 result = eval_hfexpr_with_memory flat_memories comparison_4 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_4|exact suffix_4|exact nonregister_4|exact Step]. Qed.
Definition comparison_5 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1481)) (@Eref VarOrder.T (@Eid VarOrder.T 1526))).
Definition tail_5 := match straight_drop 8057 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_5 : straight_drop 8056 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7587 comparison_5) tail_5).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_5 : memory_suffix_safe flat_memories 7587 tail_5.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_5 : has_register 7587 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_5_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7587 result = eval_hfexpr_with_memory flat_memories comparison_5 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_5|exact suffix_5|exact nonregister_5|exact Step]. Qed.
Definition comparison_6 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1480)) (@Eref VarOrder.T (@Eid VarOrder.T 1525))).
Definition tail_6 := match straight_drop 8061 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_6 : straight_drop 8060 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7591 comparison_6) tail_6).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_6 : memory_suffix_safe flat_memories 7591 tail_6.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_6 : has_register 7591 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_6_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7591 result = eval_hfexpr_with_memory flat_memories comparison_6 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_6|exact suffix_6|exact nonregister_6|exact Step]. Qed.
Definition comparison_7 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1397)) (@Eref VarOrder.T (@Eid VarOrder.T 1559))).
Definition tail_7 := match straight_drop 8065 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_7 : straight_drop 8064 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7595 comparison_7) tail_7).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_7 : memory_suffix_safe flat_memories 7595 tail_7.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_7 : has_register 7595 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_7_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7595 result = eval_hfexpr_with_memory flat_memories comparison_7 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_7|exact suffix_7|exact nonregister_7|exact Step]. Qed.
Definition comparison_8 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1399)) (@Eref VarOrder.T (@Eid VarOrder.T 1597))).
Definition tail_8 := match straight_drop 8069 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_8 : straight_drop 8068 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7599 comparison_8) tail_8).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_8 : memory_suffix_safe flat_memories 7599 tail_8.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_8 : has_register 7599 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_8_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7599 result = eval_hfexpr_with_memory flat_memories comparison_8 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_8|exact suffix_8|exact nonregister_8|exact Step]. Qed.
Definition comparison_9 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1400)) (@Eref VarOrder.T (@Eid VarOrder.T 1598))).
Definition tail_9 := match straight_drop 8073 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_9 : straight_drop 8072 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7603 comparison_9) tail_9).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_9 : memory_suffix_safe flat_memories 7603 tail_9.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_9 : has_register 7603 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_9_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7603 result = eval_hfexpr_with_memory flat_memories comparison_9 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_9|exact suffix_9|exact nonregister_9|exact Step]. Qed.
Definition comparison_10 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1401)) (@Eref VarOrder.T (@Eid VarOrder.T 1599))).
Definition tail_10 := match straight_drop 8077 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_10 : straight_drop 8076 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7607 comparison_10) tail_10).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_10 : memory_suffix_safe flat_memories 7607 tail_10.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_10 : has_register 7607 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_10_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7607 result = eval_hfexpr_with_memory flat_memories comparison_10 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_10|exact suffix_10|exact nonregister_10|exact Step]. Qed.
Definition comparison_11 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1402)) (@Eref VarOrder.T (@Eid VarOrder.T 1600))).
Definition tail_11 := match straight_drop 8081 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_11 : straight_drop 8080 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7611 comparison_11) tail_11).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_11 : memory_suffix_safe flat_memories 7611 tail_11.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_11 : has_register 7611 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_11_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7611 result = eval_hfexpr_with_memory flat_memories comparison_11 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_11|exact suffix_11|exact nonregister_11|exact Step]. Qed.
Definition comparison_12 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1403)) (@Eref VarOrder.T (@Eid VarOrder.T 1601))).
Definition tail_12 := match straight_drop 8085 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_12 : straight_drop 8084 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7615 comparison_12) tail_12).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_12 : memory_suffix_safe flat_memories 7615 tail_12.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_12 : has_register 7615 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_12_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7615 result = eval_hfexpr_with_memory flat_memories comparison_12 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_12|exact suffix_12|exact nonregister_12|exact Step]. Qed.
Definition comparison_13 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1404)) (@Eref VarOrder.T (@Eid VarOrder.T 1602))).
Definition tail_13 := match straight_drop 8089 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_13 : straight_drop 8088 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7619 comparison_13) tail_13).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_13 : memory_suffix_safe flat_memories 7619 tail_13.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_13 : has_register 7619 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_13_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7619 result = eval_hfexpr_with_memory flat_memories comparison_13 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_13|exact suffix_13|exact nonregister_13|exact Step]. Qed.
Definition comparison_14 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1405)) (@Eref VarOrder.T (@Eid VarOrder.T 1603))).
Definition tail_14 := match straight_drop 8093 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_14 : straight_drop 8092 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7623 comparison_14) tail_14).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_14 : memory_suffix_safe flat_memories 7623 tail_14.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_14 : has_register 7623 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_14_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7623 result = eval_hfexpr_with_memory flat_memories comparison_14 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_14|exact suffix_14|exact nonregister_14|exact Step]. Qed.
Definition comparison_15 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1406)) (@Eref VarOrder.T (@Eid VarOrder.T 1604))).
Definition tail_15 := match straight_drop 8097 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_15 : straight_drop 8096 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7627 comparison_15) tail_15).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_15 : memory_suffix_safe flat_memories 7627 tail_15.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_15 : has_register 7627 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_15_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7627 result = eval_hfexpr_with_memory flat_memories comparison_15 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_15|exact suffix_15|exact nonregister_15|exact Step]. Qed.
Definition comparison_16 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1407)) (@Eref VarOrder.T (@Eid VarOrder.T 1605))).
Definition tail_16 := match straight_drop 8101 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_16 : straight_drop 8100 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7631 comparison_16) tail_16).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_16 : memory_suffix_safe flat_memories 7631 tail_16.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_16 : has_register 7631 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_16_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7631 result = eval_hfexpr_with_memory flat_memories comparison_16 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_16|exact suffix_16|exact nonregister_16|exact Step]. Qed.
Definition comparison_17 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1408)) (@Eref VarOrder.T (@Eid VarOrder.T 1606))).
Definition tail_17 := match straight_drop 8105 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_17 : straight_drop 8104 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7635 comparison_17) tail_17).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_17 : memory_suffix_safe flat_memories 7635 tail_17.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_17 : has_register 7635 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_17_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7635 result = eval_hfexpr_with_memory flat_memories comparison_17 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_17|exact suffix_17|exact nonregister_17|exact Step]. Qed.
Definition comparison_18 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1409)) (@Eref VarOrder.T (@Eid VarOrder.T 1607))).
Definition tail_18 := match straight_drop 8109 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_18 : straight_drop 8108 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7639 comparison_18) tail_18).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_18 : memory_suffix_safe flat_memories 7639 tail_18.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_18 : has_register 7639 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_18_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7639 result = eval_hfexpr_with_memory flat_memories comparison_18 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_18|exact suffix_18|exact nonregister_18|exact Step]. Qed.
Definition comparison_19 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1410)) (@Eref VarOrder.T (@Eid VarOrder.T 1608))).
Definition tail_19 := match straight_drop 8113 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_19 : straight_drop 8112 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7643 comparison_19) tail_19).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_19 : memory_suffix_safe flat_memories 7643 tail_19.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_19 : has_register 7643 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_19_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7643 result = eval_hfexpr_with_memory flat_memories comparison_19 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_19|exact suffix_19|exact nonregister_19|exact Step]. Qed.
Definition comparison_20 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1411)) (@Eref VarOrder.T (@Eid VarOrder.T 1609))).
Definition tail_20 := match straight_drop 8117 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_20 : straight_drop 8116 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7647 comparison_20) tail_20).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_20 : memory_suffix_safe flat_memories 7647 tail_20.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_20 : has_register 7647 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_20_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7647 result = eval_hfexpr_with_memory flat_memories comparison_20 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_20|exact suffix_20|exact nonregister_20|exact Step]. Qed.
Definition comparison_21 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1412)) (@Eref VarOrder.T (@Eid VarOrder.T 1610))).
Definition tail_21 := match straight_drop 8121 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_21 : straight_drop 8120 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7651 comparison_21) tail_21).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_21 : memory_suffix_safe flat_memories 7651 tail_21.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_21 : has_register 7651 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_21_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7651 result = eval_hfexpr_with_memory flat_memories comparison_21 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_21|exact suffix_21|exact nonregister_21|exact Step]. Qed.
Definition comparison_22 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1413)) (@Eref VarOrder.T (@Eid VarOrder.T 1611))).
Definition tail_22 := match straight_drop 8125 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_22 : straight_drop 8124 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7655 comparison_22) tail_22).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_22 : memory_suffix_safe flat_memories 7655 tail_22.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_22 : has_register 7655 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_22_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7655 result = eval_hfexpr_with_memory flat_memories comparison_22 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_22|exact suffix_22|exact nonregister_22|exact Step]. Qed.
Definition comparison_23 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1414)) (@Eref VarOrder.T (@Eid VarOrder.T 1612))).
Definition tail_23 := match straight_drop 8129 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_23 : straight_drop 8128 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7659 comparison_23) tail_23).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_23 : memory_suffix_safe flat_memories 7659 tail_23.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_23 : has_register 7659 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_23_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7659 result = eval_hfexpr_with_memory flat_memories comparison_23 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_23|exact suffix_23|exact nonregister_23|exact Step]. Qed.
Definition comparison_24 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1415)) (@Eref VarOrder.T (@Eid VarOrder.T 1613))).
Definition tail_24 := match straight_drop 8133 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_24 : straight_drop 8132 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7663 comparison_24) tail_24).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_24 : memory_suffix_safe flat_memories 7663 tail_24.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_24 : has_register 7663 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_24_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7663 result = eval_hfexpr_with_memory flat_memories comparison_24 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_24|exact suffix_24|exact nonregister_24|exact Step]. Qed.
Definition comparison_25 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1416)) (@Eref VarOrder.T (@Eid VarOrder.T 1614))).
Definition tail_25 := match straight_drop 8137 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_25 : straight_drop 8136 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7667 comparison_25) tail_25).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_25 : memory_suffix_safe flat_memories 7667 tail_25.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_25 : has_register 7667 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_25_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7667 result = eval_hfexpr_with_memory flat_memories comparison_25 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_25|exact suffix_25|exact nonregister_25|exact Step]. Qed.
Definition comparison_26 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1417)) (@Eref VarOrder.T (@Eid VarOrder.T 1615))).
Definition tail_26 := match straight_drop 8141 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_26 : straight_drop 8140 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7671 comparison_26) tail_26).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_26 : memory_suffix_safe flat_memories 7671 tail_26.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_26 : has_register 7671 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_26_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7671 result = eval_hfexpr_with_memory flat_memories comparison_26 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_26|exact suffix_26|exact nonregister_26|exact Step]. Qed.
Definition comparison_27 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1418)) (@Eref VarOrder.T (@Eid VarOrder.T 1616))).
Definition tail_27 := match straight_drop 8145 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_27 : straight_drop 8144 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7675 comparison_27) tail_27).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_27 : memory_suffix_safe flat_memories 7675 tail_27.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_27 : has_register 7675 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_27_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7675 result = eval_hfexpr_with_memory flat_memories comparison_27 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_27|exact suffix_27|exact nonregister_27|exact Step]. Qed.
Definition comparison_28 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1419)) (@Eref VarOrder.T (@Eid VarOrder.T 1617))).
Definition tail_28 := match straight_drop 8149 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_28 : straight_drop 8148 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7679 comparison_28) tail_28).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_28 : memory_suffix_safe flat_memories 7679 tail_28.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_28 : has_register 7679 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_28_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7679 result = eval_hfexpr_with_memory flat_memories comparison_28 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_28|exact suffix_28|exact nonregister_28|exact Step]. Qed.
Definition comparison_29 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1420)) (@Eref VarOrder.T (@Eid VarOrder.T 1618))).
Definition tail_29 := match straight_drop 8153 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_29 : straight_drop 8152 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7683 comparison_29) tail_29).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_29 : memory_suffix_safe flat_memories 7683 tail_29.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_29 : has_register 7683 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_29_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7683 result = eval_hfexpr_with_memory flat_memories comparison_29 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_29|exact suffix_29|exact nonregister_29|exact Step]. Qed.
Definition comparison_30 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1421)) (@Eref VarOrder.T (@Eid VarOrder.T 1619))).
Definition tail_30 := match straight_drop 8157 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_30 : straight_drop 8156 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7687 comparison_30) tail_30).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_30 : memory_suffix_safe flat_memories 7687 tail_30.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_30 : has_register 7687 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_30_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7687 result = eval_hfexpr_with_memory flat_memories comparison_30 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_30|exact suffix_30|exact nonregister_30|exact Step]. Qed.
Definition comparison_31 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1422)) (@Eref VarOrder.T (@Eid VarOrder.T 1620))).
Definition tail_31 := match straight_drop 8161 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_31 : straight_drop 8160 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7691 comparison_31) tail_31).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_31 : memory_suffix_safe flat_memories 7691 tail_31.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_31 : has_register 7691 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_31_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7691 result = eval_hfexpr_with_memory flat_memories comparison_31 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_31|exact suffix_31|exact nonregister_31|exact Step]. Qed.
Definition comparison_32 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1423)) (@Eref VarOrder.T (@Eid VarOrder.T 1621))).
Definition tail_32 := match straight_drop 8165 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_32 : straight_drop 8164 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7695 comparison_32) tail_32).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_32 : memory_suffix_safe flat_memories 7695 tail_32.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_32 : has_register 7695 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_32_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7695 result = eval_hfexpr_with_memory flat_memories comparison_32 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_32|exact suffix_32|exact nonregister_32|exact Step]. Qed.
Definition comparison_33 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1424)) (@Eref VarOrder.T (@Eid VarOrder.T 1622))).
Definition tail_33 := match straight_drop 8169 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_33 : straight_drop 8168 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7699 comparison_33) tail_33).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_33 : memory_suffix_safe flat_memories 7699 tail_33.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_33 : has_register 7699 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_33_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7699 result = eval_hfexpr_with_memory flat_memories comparison_33 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_33|exact suffix_33|exact nonregister_33|exact Step]. Qed.
Definition comparison_34 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1425)) (@Eref VarOrder.T (@Eid VarOrder.T 1623))).
Definition tail_34 := match straight_drop 8173 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_34 : straight_drop 8172 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7703 comparison_34) tail_34).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_34 : memory_suffix_safe flat_memories 7703 tail_34.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_34 : has_register 7703 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_34_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7703 result = eval_hfexpr_with_memory flat_memories comparison_34 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_34|exact suffix_34|exact nonregister_34|exact Step]. Qed.
Definition comparison_35 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1426)) (@Eref VarOrder.T (@Eid VarOrder.T 1624))).
Definition tail_35 := match straight_drop 8177 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_35 : straight_drop 8176 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7707 comparison_35) tail_35).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_35 : memory_suffix_safe flat_memories 7707 tail_35.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_35 : has_register 7707 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_35_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7707 result = eval_hfexpr_with_memory flat_memories comparison_35 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_35|exact suffix_35|exact nonregister_35|exact Step]. Qed.
Definition comparison_36 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1427)) (@Eref VarOrder.T (@Eid VarOrder.T 1625))).
Definition tail_36 := match straight_drop 8181 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_36 : straight_drop 8180 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7711 comparison_36) tail_36).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_36 : memory_suffix_safe flat_memories 7711 tail_36.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_36 : has_register 7711 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_36_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7711 result = eval_hfexpr_with_memory flat_memories comparison_36 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_36|exact suffix_36|exact nonregister_36|exact Step]. Qed.
Definition comparison_37 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1428)) (@Eref VarOrder.T (@Eid VarOrder.T 1626))).
Definition tail_37 := match straight_drop 8185 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_37 : straight_drop 8184 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7715 comparison_37) tail_37).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_37 : memory_suffix_safe flat_memories 7715 tail_37.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_37 : has_register 7715 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_37_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7715 result = eval_hfexpr_with_memory flat_memories comparison_37 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_37|exact suffix_37|exact nonregister_37|exact Step]. Qed.
Definition comparison_38 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1429)) (@Eref VarOrder.T (@Eid VarOrder.T 1627))).
Definition tail_38 := match straight_drop 8189 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_38 : straight_drop 8188 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7719 comparison_38) tail_38).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_38 : memory_suffix_safe flat_memories 7719 tail_38.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_38 : has_register 7719 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_38_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7719 result = eval_hfexpr_with_memory flat_memories comparison_38 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_38|exact suffix_38|exact nonregister_38|exact Step]. Qed.
Definition comparison_39 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1430)) (@Eref VarOrder.T (@Eid VarOrder.T 1628))).
Definition tail_39 := match straight_drop 8193 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_39 : straight_drop 8192 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7723 comparison_39) tail_39).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_39 : memory_suffix_safe flat_memories 7723 tail_39.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_39 : has_register 7723 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_39_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7723 result = eval_hfexpr_with_memory flat_memories comparison_39 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_39|exact suffix_39|exact nonregister_39|exact Step]. Qed.
Definition comparison_40 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1469)) (@Eref VarOrder.T (@Eid VarOrder.T 1667))).
Definition tail_40 := match straight_drop 8198 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_40 : straight_drop 8197 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7728 comparison_40) tail_40).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_40 : memory_suffix_safe flat_memories 7728 tail_40.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_40 : has_register 7728 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_40_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7728 result = eval_hfexpr_with_memory flat_memories comparison_40 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_40|exact suffix_40|exact nonregister_40|exact Step]. Qed.
Definition comparison_41 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1470)) (@Eref VarOrder.T (@Eid VarOrder.T 1668))).
Definition tail_41 := match straight_drop 8202 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_41 : straight_drop 8201 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7732 comparison_41) tail_41).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_41 : memory_suffix_safe flat_memories 7732 tail_41.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_41 : has_register 7732 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_41_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7732 result = eval_hfexpr_with_memory flat_memories comparison_41 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_41|exact suffix_41|exact nonregister_41|exact Step]. Qed.
Definition comparison_42 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1471)) (@Eref VarOrder.T (@Eid VarOrder.T 1669))).
Definition tail_42 := match straight_drop 8206 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_42 : straight_drop 8205 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7736 comparison_42) tail_42).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_42 : memory_suffix_safe flat_memories 7736 tail_42.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_42 : has_register 7736 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_42_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7736 result = eval_hfexpr_with_memory flat_memories comparison_42 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_42|exact suffix_42|exact nonregister_42|exact Step]. Qed.
Definition comparison_43 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1472)) (@Eref VarOrder.T (@Eid VarOrder.T 1670))).
Definition tail_43 := match straight_drop 8210 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_43 : straight_drop 8209 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7740 comparison_43) tail_43).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_43 : memory_suffix_safe flat_memories 7740 tail_43.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_43 : has_register 7740 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_43_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7740 result = eval_hfexpr_with_memory flat_memories comparison_43 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_43|exact suffix_43|exact nonregister_43|exact Step]. Qed.
Definition comparison_44 := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 1473)) (@Eref VarOrder.T (@Eid VarOrder.T 1671))).
Definition tail_44 := match straight_drop 8214 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma position_44 : straight_drop 8213 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 7744 comparison_44) tail_44).
Proof. vm_compute. reflexivity. Qed.
Lemma suffix_44 : memory_suffix_safe flat_memories 7744 tail_44.
Proof. apply memory_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma nonregister_44 : has_register 7744 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem comparison_44_full_iteration invalid old set_regs current result :
 value_iter_with_memory_policy invalid flat_memories old set_regs current flat_statements = Some result ->
 VM.find 7744 result = eval_hfexpr_with_memory flat_memories comparison_44 old old.
Proof. intro Step. eapply full_iteration_memory_node_equation;
 [exact position_44|exact suffix_44|exact nonregister_44|exact Step]. Qed.
Print Assumptions comparison_44_full_iteration.
