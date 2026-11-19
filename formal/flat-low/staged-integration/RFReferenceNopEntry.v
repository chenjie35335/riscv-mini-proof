Require Import CoreSocModel ComparisonNodes RFReferenceNopRelation X0ConcretePositionCertificate X0ConcreteSafetyCertificate SelectedNodeSafety FormalSuccessfulNodeEvaluation FormalTypedNodeEquation FormalGroundNodeEquation.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition rf_reference_entry_condition (index : nat) : hfexpr VarOrder.T :=
 match index with
 | 1%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 2%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 3%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 4%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 5%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 6%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 7%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 3) [::true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 8%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 9%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 10%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 11%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 12%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 13%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 14%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 15%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 4) [::true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 16%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 17%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 18%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 19%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 20%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 21%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 22%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 23%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 24%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 25%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 26%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 27%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 28%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 29%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 30%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::false; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | 31%nat => (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 3221)))
 | _ => @Econst VarOrder.T (Fuint 1) [::false]
 end.
Definition rf_reference_entry_expr index := @Emux VarOrder.T (rf_reference_entry_condition index)
 (@Eref VarOrder.T (@Eid VarOrder.T 3222)) (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat (Nat.sub 2177 index)))).
Definition rf_reference_entry_nodes : seq (VarOrder.T * hfexpr VarOrder.T) := [::(3224,rf_reference_entry_expr 1%nat);(3225,rf_reference_entry_expr 2%nat);(3226,rf_reference_entry_expr 3%nat);(3227,rf_reference_entry_expr 4%nat);(3228,rf_reference_entry_expr 5%nat);(3229,rf_reference_entry_expr 6%nat);(3230,rf_reference_entry_expr 7%nat);(3231,rf_reference_entry_expr 8%nat);(3232,rf_reference_entry_expr 9%nat);(3233,rf_reference_entry_expr 10%nat);(3234,rf_reference_entry_expr 11%nat);(3235,rf_reference_entry_expr 12%nat);(3236,rf_reference_entry_expr 13%nat);(3237,rf_reference_entry_expr 14%nat);(3238,rf_reference_entry_expr 15%nat);(3239,rf_reference_entry_expr 16%nat);(3240,rf_reference_entry_expr 17%nat);(3241,rf_reference_entry_expr 18%nat);(3242,rf_reference_entry_expr 19%nat);(3243,rf_reference_entry_expr 20%nat);(3244,rf_reference_entry_expr 21%nat);(3245,rf_reference_entry_expr 22%nat);(3246,rf_reference_entry_expr 23%nat);(3247,rf_reference_entry_expr 24%nat);(3248,rf_reference_entry_expr 25%nat);(3249,rf_reference_entry_expr 26%nat);(3250,rf_reference_entry_expr 27%nat);(3251,rf_reference_entry_expr 28%nat);(3252,rf_reference_entry_expr 29%nat);(3253,rf_reference_entry_expr 30%nat);(3254,rf_reference_entry_expr 31%nat);(3255,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 2177))))].
Definition rf_reference_entry_offsets : seq nat := [::3303%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat;0%nat].
Lemma rf_reference_entry_positions : select_node_offsets rf_reference_entry_offsets flat_statements = Some rf_reference_entry_nodes.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reference_entry_safety : selected_node_safety flat_memories flat_statements rf_reference_entry_offsets flat_statements = true.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_reference_entry_member index : (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 List.In (N.of_nat (Nat.add 3223 index),rf_reference_entry_expr index) rf_reference_entry_nodes.
Proof.
 intros Lower Upper.
 destruct index as [|index]. { lia. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 destruct index as [|index]. { vm_compute. tauto. }
 lia.
Qed.
Lemma rf_reference_entry_condition_false index mm old :
 (1 <= index)%coq_nat -> (index < 32)%coq_nat ->
 VM.find 3221 old = Some (Gval (Fuint 5) [::false;false;false;false;false]) ->
 eval_hfexpr_with_memory mm (rf_reference_entry_condition index) old old = Some (Gval (Fuint 1) [::false]).
Proof.
 intros Lower Upper Rd.
 destruct index as [|index]. { lia. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 destruct index as [|index]. { cbn [rf_reference_entry_condition eval_hfexpr_with_memory eval_href_with_memory]. rewrite Rd. vm_compute. reflexivity. }
 lia.
Qed.
Lemma rf_reference_entry_policy_irrelevant index policy site mm old :
 eval_hfexpr_validif_policy policy site mm (rf_reference_entry_expr index) old old =
 eval_hfexpr_with_memory mm (rf_reference_entry_expr index) old old.
Proof.
 do 32 (destruct index as [|index]; [reflexivity|]). reflexivity.
Qed.
Lemma rf_reference_condition_false_mux_extension mm old condition (yes no : VarOrder.T) base source :
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
 exists value, VM.find (N.of_nat (Nat.add 3223 index)) result = Some value /\ rf_reference_word_extension word value.
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
Theorem rf_reference_nop_x0_entry invalid old current result :
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
