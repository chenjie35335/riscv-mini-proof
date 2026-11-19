Require Import CoreSocModel ComparisonNodes FormalSuccessfulNode FormalTypedNodeEquation FormalTypedNodeFrames ScalarNodeFrames RegisterInvariants ComparisonConstantBitShape NormalizedBit NormalizedOr.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition legal_bool_9028_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Eref VarOrder.T (@Eid VarOrder.T 42)) (@Econst VarOrder.T (Fuint 1) [::false])).
Definition legal_bool_9028_tail := match straight_drop 9802 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9028_position : straight_drop 9801 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9028 legal_bool_9028_expr) legal_bool_9028_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9028_safe : formal_typed_suffix_safe flat_memories 9028 legal_bool_9028_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9028_nonregister : has_register 9028 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9028_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9028 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9028_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9028_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9028_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 42 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_right_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9028_position|exact legal_bool_9028_safe|exact legal_bool_9028_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9030_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9029))).
Definition legal_bool_9030_tail := match straight_drop 9804 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9030_position : straight_drop 9803 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9030 legal_bool_9030_expr) legal_bool_9030_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9030_safe : formal_typed_suffix_safe flat_memories 9030 legal_bool_9030_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9030_nonregister : has_register 9030 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9030_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9030 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9030_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9030_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9030_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9029 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9030_position|exact legal_bool_9030_safe|exact legal_bool_9030_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9032_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9031))).
Definition legal_bool_9032_tail := match straight_drop 9806 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9032_position : straight_drop 9805 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9032 legal_bool_9032_expr) legal_bool_9032_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9032_safe : formal_typed_suffix_safe flat_memories 9032 legal_bool_9032_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9032_nonregister : has_register 9032 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9032_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9032 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9032_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9032_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9032_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9031 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9032_position|exact legal_bool_9032_safe|exact legal_bool_9032_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9034_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9033))).
Definition legal_bool_9034_tail := match straight_drop 9808 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9034_position : straight_drop 9807 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9034 legal_bool_9034_expr) legal_bool_9034_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9034_safe : formal_typed_suffix_safe flat_memories 9034 legal_bool_9034_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9034_nonregister : has_register 9034 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9034_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9034 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9034_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9034_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9034_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9033 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9034_position|exact legal_bool_9034_safe|exact legal_bool_9034_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9036_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9035))).
Definition legal_bool_9036_tail := match straight_drop 9810 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9036_position : straight_drop 9809 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9036 legal_bool_9036_expr) legal_bool_9036_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9036_safe : formal_typed_suffix_safe flat_memories 9036 legal_bool_9036_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9036_nonregister : has_register 9036 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9036_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9036 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9036_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9036_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9036_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9035 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9036_position|exact legal_bool_9036_safe|exact legal_bool_9036_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9038_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9037))).
Definition legal_bool_9038_tail := match straight_drop 9812 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9038_position : straight_drop 9811 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9038 legal_bool_9038_expr) legal_bool_9038_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9038_safe : formal_typed_suffix_safe flat_memories 9038 legal_bool_9038_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9038_nonregister : has_register 9038 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9038_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9038 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9038_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9038_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9038_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9037 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9038_position|exact legal_bool_9038_safe|exact legal_bool_9038_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9040_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9039))).
Definition legal_bool_9040_tail := match straight_drop 9814 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9040_position : straight_drop 9813 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9040 legal_bool_9040_expr) legal_bool_9040_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9040_safe : formal_typed_suffix_safe flat_memories 9040 legal_bool_9040_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9040_nonregister : has_register 9040 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9040_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9040 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9040_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9040_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9040_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9039 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9040_position|exact legal_bool_9040_safe|exact legal_bool_9040_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9042_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9041))).
Definition legal_bool_9042_tail := match straight_drop 9816 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9042_position : straight_drop 9815 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9042 legal_bool_9042_expr) legal_bool_9042_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9042_safe : formal_typed_suffix_safe flat_memories 9042 legal_bool_9042_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9042_nonregister : has_register 9042 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9042_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9042 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9042_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9042_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9042_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9041 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9042_position|exact legal_bool_9042_safe|exact legal_bool_9042_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9044_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; false; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9043))).
Definition legal_bool_9044_tail := match straight_drop 9818 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9044_position : straight_drop 9817 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9044 legal_bool_9044_expr) legal_bool_9044_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9044_safe : formal_typed_suffix_safe flat_memories 9044 legal_bool_9044_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9044_nonregister : has_register 9044 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9044_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9044 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9044_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9044_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9044_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9043 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9044_position|exact legal_bool_9044_safe|exact legal_bool_9044_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9046_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; false; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9045))).
Definition legal_bool_9046_tail := match straight_drop 9820 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9046_position : straight_drop 9819 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9046 legal_bool_9046_expr) legal_bool_9046_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9046_safe : formal_typed_suffix_safe flat_memories 9046 legal_bool_9046_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9046_nonregister : has_register 9046 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9046_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9046 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9046_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9046_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9046_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9045 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9046_position|exact legal_bool_9046_safe|exact legal_bool_9046_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9048_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9047))).
Definition legal_bool_9048_tail := match straight_drop 9822 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9048_position : straight_drop 9821 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9048 legal_bool_9048_expr) legal_bool_9048_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9048_safe : formal_typed_suffix_safe flat_memories 9048 legal_bool_9048_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9048_nonregister : has_register 9048 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9048_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9048 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9048_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9048_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9048_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9047 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9048_position|exact legal_bool_9048_safe|exact legal_bool_9048_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9050_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 5) [::true; true; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9049))).
Definition legal_bool_9050_tail := match straight_drop 9824 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9050_position : straight_drop 9823 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9050 legal_bool_9050_expr) legal_bool_9050_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9050_safe : formal_typed_suffix_safe flat_memories 9050 legal_bool_9050_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9050_nonregister : has_register 9050 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9050_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9050 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9050_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9050_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9050_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9049 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9050_position|exact legal_bool_9050_safe|exact legal_bool_9050_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9051_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9030)) (@Eref VarOrder.T (@Eid VarOrder.T 9032))).
Definition legal_bool_9051_tail := match straight_drop 9825 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9051_position : straight_drop 9824 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9051 legal_bool_9051_expr) legal_bool_9051_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9051_safe : formal_typed_suffix_safe flat_memories 9051 legal_bool_9051_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9051_nonregister : has_register 9051 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9051_normalized invalid old current result :
 (exists value, VM.find 9030 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9032 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9051 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9051_expr old old = Some value).
 { cbn [legal_bool_9051_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9051_position|exact legal_bool_9051_safe|exact legal_bool_9051_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9052_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9051)) (@Eref VarOrder.T (@Eid VarOrder.T 9034))).
Definition legal_bool_9052_tail := match straight_drop 9826 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9052_position : straight_drop 9825 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9052 legal_bool_9052_expr) legal_bool_9052_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9052_safe : formal_typed_suffix_safe flat_memories 9052 legal_bool_9052_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9052_nonregister : has_register 9052 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9052_normalized invalid old current result :
 (exists value, VM.find 9051 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9034 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9052 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9052_expr old old = Some value).
 { cbn [legal_bool_9052_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9052_position|exact legal_bool_9052_safe|exact legal_bool_9052_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9053_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9052)) (@Eref VarOrder.T (@Eid VarOrder.T 9036))).
Definition legal_bool_9053_tail := match straight_drop 9827 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9053_position : straight_drop 9826 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9053 legal_bool_9053_expr) legal_bool_9053_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9053_safe : formal_typed_suffix_safe flat_memories 9053 legal_bool_9053_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9053_nonregister : has_register 9053 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9053_normalized invalid old current result :
 (exists value, VM.find 9052 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9036 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9053 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9053_expr old old = Some value).
 { cbn [legal_bool_9053_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9053_position|exact legal_bool_9053_safe|exact legal_bool_9053_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9054_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9053)) (@Eref VarOrder.T (@Eid VarOrder.T 9038))).
Definition legal_bool_9054_tail := match straight_drop 9828 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9054_position : straight_drop 9827 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9054 legal_bool_9054_expr) legal_bool_9054_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9054_safe : formal_typed_suffix_safe flat_memories 9054 legal_bool_9054_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9054_nonregister : has_register 9054 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9054_normalized invalid old current result :
 (exists value, VM.find 9053 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9038 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9054 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9054_expr old old = Some value).
 { cbn [legal_bool_9054_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9054_position|exact legal_bool_9054_safe|exact legal_bool_9054_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9055_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9054)) (@Eref VarOrder.T (@Eid VarOrder.T 9040))).
Definition legal_bool_9055_tail := match straight_drop 9829 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9055_position : straight_drop 9828 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9055 legal_bool_9055_expr) legal_bool_9055_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9055_safe : formal_typed_suffix_safe flat_memories 9055 legal_bool_9055_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9055_nonregister : has_register 9055 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9055_normalized invalid old current result :
 (exists value, VM.find 9054 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9040 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9055 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9055_expr old old = Some value).
 { cbn [legal_bool_9055_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9055_position|exact legal_bool_9055_safe|exact legal_bool_9055_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9056_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9055)) (@Eref VarOrder.T (@Eid VarOrder.T 9042))).
Definition legal_bool_9056_tail := match straight_drop 9830 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9056_position : straight_drop 9829 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9056 legal_bool_9056_expr) legal_bool_9056_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9056_safe : formal_typed_suffix_safe flat_memories 9056 legal_bool_9056_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9056_nonregister : has_register 9056 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9056_normalized invalid old current result :
 (exists value, VM.find 9055 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9042 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9056 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9056_expr old old = Some value).
 { cbn [legal_bool_9056_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9056_position|exact legal_bool_9056_safe|exact legal_bool_9056_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9057_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9056)) (@Eref VarOrder.T (@Eid VarOrder.T 9044))).
Definition legal_bool_9057_tail := match straight_drop 9831 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9057_position : straight_drop 9830 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9057 legal_bool_9057_expr) legal_bool_9057_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9057_safe : formal_typed_suffix_safe flat_memories 9057 legal_bool_9057_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9057_nonregister : has_register 9057 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9057_normalized invalid old current result :
 (exists value, VM.find 9056 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9044 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9057 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9057_expr old old = Some value).
 { cbn [legal_bool_9057_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9057_position|exact legal_bool_9057_safe|exact legal_bool_9057_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9058_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9057)) (@Eref VarOrder.T (@Eid VarOrder.T 9046))).
Definition legal_bool_9058_tail := match straight_drop 9832 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9058_position : straight_drop 9831 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9058 legal_bool_9058_expr) legal_bool_9058_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9058_safe : formal_typed_suffix_safe flat_memories 9058 legal_bool_9058_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9058_nonregister : has_register 9058 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9058_normalized invalid old current result :
 (exists value, VM.find 9057 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9046 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9058 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9058_expr old old = Some value).
 { cbn [legal_bool_9058_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9058_position|exact legal_bool_9058_safe|exact legal_bool_9058_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9059_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9058)) (@Eref VarOrder.T (@Eid VarOrder.T 9048))).
Definition legal_bool_9059_tail := match straight_drop 9833 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9059_position : straight_drop 9832 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9059 legal_bool_9059_expr) legal_bool_9059_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9059_safe : formal_typed_suffix_safe flat_memories 9059 legal_bool_9059_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9059_nonregister : has_register 9059 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9059_normalized invalid old current result :
 (exists value, VM.find 9058 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9048 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9059 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9059_expr old old = Some value).
 { cbn [legal_bool_9059_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9059_position|exact legal_bool_9059_safe|exact legal_bool_9059_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9060_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9059)) (@Eref VarOrder.T (@Eid VarOrder.T 9050))).
Definition legal_bool_9060_tail := match straight_drop 9834 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9060_position : straight_drop 9833 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9060 legal_bool_9060_expr) legal_bool_9060_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9060_safe : formal_typed_suffix_safe flat_memories 9060 legal_bool_9060_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9060_nonregister : has_register 9060 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9060_normalized invalid old current result :
 (exists value, VM.find 9059 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9050 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9060 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9060_expr old old = Some value).
 { cbn [legal_bool_9060_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9060_position|exact legal_bool_9060_safe|exact legal_bool_9060_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9062_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9061))).
Definition legal_bool_9062_tail := match straight_drop 9836 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9062_position : straight_drop 9835 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9062 legal_bool_9062_expr) legal_bool_9062_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9062_safe : formal_typed_suffix_safe flat_memories 9062 legal_bool_9062_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9062_nonregister : has_register 9062 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9062_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9062 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9062_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9062_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9062_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9061 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9062_position|exact legal_bool_9062_safe|exact legal_bool_9062_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9064_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9063))).
Definition legal_bool_9064_tail := match straight_drop 9838 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9064_position : straight_drop 9837 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9064 legal_bool_9064_expr) legal_bool_9064_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9064_safe : formal_typed_suffix_safe flat_memories 9064 legal_bool_9064_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9064_nonregister : has_register 9064 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9064_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9064 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9064_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9064_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9064_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9063 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9064_position|exact legal_bool_9064_safe|exact legal_bool_9064_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9066_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9065))).
Definition legal_bool_9066_tail := match straight_drop 9840 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9066_position : straight_drop 9839 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9066 legal_bool_9066_expr) legal_bool_9066_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9066_safe : formal_typed_suffix_safe flat_memories 9066 legal_bool_9066_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9066_nonregister : has_register 9066 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9066_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9066 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9066_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9066_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9066_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9065 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9066_position|exact legal_bool_9066_safe|exact legal_bool_9066_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9068_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9067))).
Definition legal_bool_9068_tail := match straight_drop 9842 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9068_position : straight_drop 9841 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9068 legal_bool_9068_expr) legal_bool_9068_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9068_safe : formal_typed_suffix_safe flat_memories 9068 legal_bool_9068_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9068_nonregister : has_register 9068 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9068_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9068 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9068_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9068_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9068_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9067 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9068_position|exact legal_bool_9068_safe|exact legal_bool_9068_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9070_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9069))).
Definition legal_bool_9070_tail := match straight_drop 9844 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9070_position : straight_drop 9843 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9070 legal_bool_9070_expr) legal_bool_9070_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9070_safe : formal_typed_suffix_safe flat_memories 9070 legal_bool_9070_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9070_nonregister : has_register 9070 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9070_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9070 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9070_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9070_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9070_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9069 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9070_position|exact legal_bool_9070_safe|exact legal_bool_9070_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9072_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9071))).
Definition legal_bool_9072_tail := match straight_drop 9846 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9072_position : straight_drop 9845 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9072 legal_bool_9072_expr) legal_bool_9072_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9072_safe : formal_typed_suffix_safe flat_memories 9072 legal_bool_9072_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9072_nonregister : has_register 9072 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9072_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9072 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9072_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9072_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9072_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9071 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9072_position|exact legal_bool_9072_safe|exact legal_bool_9072_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9074_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; true; true; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9073))).
Definition legal_bool_9074_tail := match straight_drop 9848 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9074_position : straight_drop 9847 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9074 legal_bool_9074_expr) legal_bool_9074_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9074_safe : formal_typed_suffix_safe flat_memories 9074 legal_bool_9074_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9074_nonregister : has_register 9074 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9074_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9074 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9074_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9074_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9074_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9073 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9074_position|exact legal_bool_9074_safe|exact legal_bool_9074_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9076_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9075))).
Definition legal_bool_9076_tail := match straight_drop 9850 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9076_position : straight_drop 9849 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9076 legal_bool_9076_expr) legal_bool_9076_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9076_safe : formal_typed_suffix_safe flat_memories 9076 legal_bool_9076_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9076_nonregister : has_register 9076 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9076_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9076 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9076_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9076_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9076_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9075 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9076_position|exact legal_bool_9076_safe|exact legal_bool_9076_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9078_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9077))).
Definition legal_bool_9078_tail := match straight_drop 9852 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9078_position : straight_drop 9851 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9078 legal_bool_9078_expr) legal_bool_9078_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9078_safe : formal_typed_suffix_safe flat_memories 9078 legal_bool_9078_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9078_nonregister : has_register 9078 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9078_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9078 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9078_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9078_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9078_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9077 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9078_position|exact legal_bool_9078_safe|exact legal_bool_9078_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9080_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 31) [::true; true; false; false; true; true; false; false; false; false; false; false; true; false; true; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9079))).
Definition legal_bool_9080_tail := match straight_drop 9854 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9080_position : straight_drop 9853 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9080 legal_bool_9080_expr) legal_bool_9080_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9080_safe : formal_typed_suffix_safe flat_memories 9080 legal_bool_9080_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9080_nonregister : has_register 9080 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9080_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9080 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9080_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9080_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9080_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9079 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9080_position|exact legal_bool_9080_safe|exact legal_bool_9080_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9081_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9062)) (@Eref VarOrder.T (@Eid VarOrder.T 9064))).
Definition legal_bool_9081_tail := match straight_drop 9855 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9081_position : straight_drop 9854 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9081 legal_bool_9081_expr) legal_bool_9081_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9081_safe : formal_typed_suffix_safe flat_memories 9081 legal_bool_9081_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9081_nonregister : has_register 9081 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9081_normalized invalid old current result :
 (exists value, VM.find 9062 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9064 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9081 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9081_expr old old = Some value).
 { cbn [legal_bool_9081_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9081_position|exact legal_bool_9081_safe|exact legal_bool_9081_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9082_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9081)) (@Eref VarOrder.T (@Eid VarOrder.T 9066))).
Definition legal_bool_9082_tail := match straight_drop 9856 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9082_position : straight_drop 9855 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9082 legal_bool_9082_expr) legal_bool_9082_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9082_safe : formal_typed_suffix_safe flat_memories 9082 legal_bool_9082_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9082_nonregister : has_register 9082 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9082_normalized invalid old current result :
 (exists value, VM.find 9081 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9066 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9082 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9082_expr old old = Some value).
 { cbn [legal_bool_9082_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9082_position|exact legal_bool_9082_safe|exact legal_bool_9082_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9083_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9082)) (@Eref VarOrder.T (@Eid VarOrder.T 9068))).
Definition legal_bool_9083_tail := match straight_drop 9857 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9083_position : straight_drop 9856 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9083 legal_bool_9083_expr) legal_bool_9083_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9083_safe : formal_typed_suffix_safe flat_memories 9083 legal_bool_9083_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9083_nonregister : has_register 9083 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9083_normalized invalid old current result :
 (exists value, VM.find 9082 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9068 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9083 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9083_expr old old = Some value).
 { cbn [legal_bool_9083_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9083_position|exact legal_bool_9083_safe|exact legal_bool_9083_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9084_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9083)) (@Eref VarOrder.T (@Eid VarOrder.T 9070))).
Definition legal_bool_9084_tail := match straight_drop 9858 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9084_position : straight_drop 9857 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9084 legal_bool_9084_expr) legal_bool_9084_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9084_safe : formal_typed_suffix_safe flat_memories 9084 legal_bool_9084_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9084_nonregister : has_register 9084 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9084_normalized invalid old current result :
 (exists value, VM.find 9083 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9070 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9084 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9084_expr old old = Some value).
 { cbn [legal_bool_9084_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9084_position|exact legal_bool_9084_safe|exact legal_bool_9084_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9085_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9084)) (@Eref VarOrder.T (@Eid VarOrder.T 9072))).
Definition legal_bool_9085_tail := match straight_drop 9859 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9085_position : straight_drop 9858 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9085 legal_bool_9085_expr) legal_bool_9085_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9085_safe : formal_typed_suffix_safe flat_memories 9085 legal_bool_9085_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9085_nonregister : has_register 9085 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9085_normalized invalid old current result :
 (exists value, VM.find 9084 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9072 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9085 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9085_expr old old = Some value).
 { cbn [legal_bool_9085_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9085_position|exact legal_bool_9085_safe|exact legal_bool_9085_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9086_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9085)) (@Eref VarOrder.T (@Eid VarOrder.T 9074))).
Definition legal_bool_9086_tail := match straight_drop 9860 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9086_position : straight_drop 9859 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9086 legal_bool_9086_expr) legal_bool_9086_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9086_safe : formal_typed_suffix_safe flat_memories 9086 legal_bool_9086_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9086_nonregister : has_register 9086 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9086_normalized invalid old current result :
 (exists value, VM.find 9085 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9074 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9086 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9086_expr old old = Some value).
 { cbn [legal_bool_9086_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9086_position|exact legal_bool_9086_safe|exact legal_bool_9086_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9087_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9086)) (@Eref VarOrder.T (@Eid VarOrder.T 9076))).
Definition legal_bool_9087_tail := match straight_drop 9861 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9087_position : straight_drop 9860 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9087 legal_bool_9087_expr) legal_bool_9087_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9087_safe : formal_typed_suffix_safe flat_memories 9087 legal_bool_9087_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9087_nonregister : has_register 9087 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9087_normalized invalid old current result :
 (exists value, VM.find 9086 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9076 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9087 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9087_expr old old = Some value).
 { cbn [legal_bool_9087_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9087_position|exact legal_bool_9087_safe|exact legal_bool_9087_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9088_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9087)) (@Eref VarOrder.T (@Eid VarOrder.T 9078))).
Definition legal_bool_9088_tail := match straight_drop 9862 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9088_position : straight_drop 9861 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9088 legal_bool_9088_expr) legal_bool_9088_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9088_safe : formal_typed_suffix_safe flat_memories 9088 legal_bool_9088_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9088_nonregister : has_register 9088 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9088_normalized invalid old current result :
 (exists value, VM.find 9087 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9078 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9088 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9088_expr old old = Some value).
 { cbn [legal_bool_9088_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9088_position|exact legal_bool_9088_safe|exact legal_bool_9088_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9089_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9088)) (@Eref VarOrder.T (@Eid VarOrder.T 9080))).
Definition legal_bool_9089_tail := match straight_drop 9863 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9089_position : straight_drop 9862 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9089 legal_bool_9089_expr) legal_bool_9089_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9089_safe : formal_typed_suffix_safe flat_memories 9089 legal_bool_9089_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9089_nonregister : has_register 9089 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9089_normalized invalid old current result :
 (exists value, VM.find 9088 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9080 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9089 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9089_expr old old = Some value).
 { cbn [legal_bool_9089_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9089_position|exact legal_bool_9089_safe|exact legal_bool_9089_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9090_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9060)) (@Eref VarOrder.T (@Eid VarOrder.T 9089))).
Definition legal_bool_9090_tail := match straight_drop 9864 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9090_position : straight_drop 9863 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9090 legal_bool_9090_expr) legal_bool_9090_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9090_safe : formal_typed_suffix_safe flat_memories 9090 legal_bool_9090_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9090_nonregister : has_register 9090 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9090_normalized invalid old current result :
 (exists value, VM.find 9060 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9089 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9090 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9090_expr old old = Some value).
 { cbn [legal_bool_9090_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9090_position|exact legal_bool_9090_safe|exact legal_bool_9090_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9092_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; true; true; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9091))).
Definition legal_bool_9092_tail := match straight_drop 9866 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9092_position : straight_drop 9865 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9092 legal_bool_9092_expr) legal_bool_9092_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9092_safe : formal_typed_suffix_safe flat_memories 9092 legal_bool_9092_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9092_nonregister : has_register 9092 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9092_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9092 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9092_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9092_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9092_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9091 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9092_position|exact legal_bool_9092_safe|exact legal_bool_9092_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9094_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; true; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9093))).
Definition legal_bool_9094_tail := match straight_drop 9868 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9094_position : straight_drop 9867 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9094 legal_bool_9094_expr) legal_bool_9094_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9094_safe : formal_typed_suffix_safe flat_memories 9094 legal_bool_9094_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9094_nonregister : has_register 9094 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9094_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9094 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9094_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9094_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9094_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9093 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9094_position|exact legal_bool_9094_safe|exact legal_bool_9094_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9096_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 7) [::true; true; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9095))).
Definition legal_bool_9096_tail := match straight_drop 9870 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9096_position : straight_drop 9869 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9096 legal_bool_9096_expr) legal_bool_9096_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9096_safe : formal_typed_suffix_safe flat_memories 9096 legal_bool_9096_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9096_nonregister : has_register 9096 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9096_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9096 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9096_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9096_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9096_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9095 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9096_position|exact legal_bool_9096_safe|exact legal_bool_9096_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9098_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; true; true; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9097))).
Definition legal_bool_9098_tail := match straight_drop 9872 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9098_position : straight_drop 9871 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9098 legal_bool_9098_expr) legal_bool_9098_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9098_safe : formal_typed_suffix_safe flat_memories 9098 legal_bool_9098_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9098_nonregister : has_register 9098 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9098_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9098 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9098_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9098_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9098_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9097 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9098_position|exact legal_bool_9098_safe|exact legal_bool_9098_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9100_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9099))).
Definition legal_bool_9100_tail := match straight_drop 9874 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9100_position : straight_drop 9873 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9100 legal_bool_9100_expr) legal_bool_9100_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9100_safe : formal_typed_suffix_safe flat_memories 9100 legal_bool_9100_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9100_nonregister : has_register 9100 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9100_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9100 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9100_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9100_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9100_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9099 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9100_position|exact legal_bool_9100_safe|exact legal_bool_9100_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9102_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; false; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9101))).
Definition legal_bool_9102_tail := match straight_drop 9876 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9102_position : straight_drop 9875 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9102 legal_bool_9102_expr) legal_bool_9102_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9102_safe : formal_typed_suffix_safe flat_memories 9102 legal_bool_9102_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9102_nonregister : has_register 9102 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9102_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9102 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9102_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9102_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9102_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9101 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9102_position|exact legal_bool_9102_safe|exact legal_bool_9102_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9104_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9103))).
Definition legal_bool_9104_tail := match straight_drop 9878 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9104_position : straight_drop 9877 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9104 legal_bool_9104_expr) legal_bool_9104_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9104_safe : formal_typed_suffix_safe flat_memories 9104 legal_bool_9104_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9104_nonregister : has_register 9104 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9104_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9104 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9104_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9104_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9104_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9103 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9104_position|exact legal_bool_9104_safe|exact legal_bool_9104_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9106_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; true; true; false; false; false; false; false; true; true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9105))).
Definition legal_bool_9106_tail := match straight_drop 9880 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9106_position : straight_drop 9879 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9106 legal_bool_9106_expr) legal_bool_9106_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9106_safe : formal_typed_suffix_safe flat_memories 9106 legal_bool_9106_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9106_nonregister : has_register 9106 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9106_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9106 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9106_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9106_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9106_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9105 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9106_position|exact legal_bool_9106_safe|exact legal_bool_9106_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9107_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9092)) (@Eref VarOrder.T (@Eid VarOrder.T 9094))).
Definition legal_bool_9107_tail := match straight_drop 9881 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9107_position : straight_drop 9880 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9107 legal_bool_9107_expr) legal_bool_9107_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9107_safe : formal_typed_suffix_safe flat_memories 9107 legal_bool_9107_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9107_nonregister : has_register 9107 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9107_normalized invalid old current result :
 (exists value, VM.find 9092 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9094 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9107 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9107_expr old old = Some value).
 { cbn [legal_bool_9107_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9107_position|exact legal_bool_9107_safe|exact legal_bool_9107_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9108_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9107)) (@Eref VarOrder.T (@Eid VarOrder.T 9096))).
Definition legal_bool_9108_tail := match straight_drop 9882 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9108_position : straight_drop 9881 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9108 legal_bool_9108_expr) legal_bool_9108_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9108_safe : formal_typed_suffix_safe flat_memories 9108 legal_bool_9108_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9108_nonregister : has_register 9108 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9108_normalized invalid old current result :
 (exists value, VM.find 9107 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9096 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9108 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9108_expr old old = Some value).
 { cbn [legal_bool_9108_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9108_position|exact legal_bool_9108_safe|exact legal_bool_9108_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9109_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9108)) (@Eref VarOrder.T (@Eid VarOrder.T 9098))).
Definition legal_bool_9109_tail := match straight_drop 9883 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9109_position : straight_drop 9882 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9109 legal_bool_9109_expr) legal_bool_9109_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9109_safe : formal_typed_suffix_safe flat_memories 9109 legal_bool_9109_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9109_nonregister : has_register 9109 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9109_normalized invalid old current result :
 (exists value, VM.find 9108 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9098 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9109 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9109_expr old old = Some value).
 { cbn [legal_bool_9109_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9109_position|exact legal_bool_9109_safe|exact legal_bool_9109_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9110_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9109)) (@Eref VarOrder.T (@Eid VarOrder.T 9100))).
Definition legal_bool_9110_tail := match straight_drop 9884 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9110_position : straight_drop 9883 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9110 legal_bool_9110_expr) legal_bool_9110_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9110_safe : formal_typed_suffix_safe flat_memories 9110 legal_bool_9110_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9110_nonregister : has_register 9110 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9110_normalized invalid old current result :
 (exists value, VM.find 9109 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9100 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9110 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9110_expr old old = Some value).
 { cbn [legal_bool_9110_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9110_position|exact legal_bool_9110_safe|exact legal_bool_9110_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9111_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9110)) (@Eref VarOrder.T (@Eid VarOrder.T 9102))).
Definition legal_bool_9111_tail := match straight_drop 9885 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9111_position : straight_drop 9884 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9111 legal_bool_9111_expr) legal_bool_9111_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9111_safe : formal_typed_suffix_safe flat_memories 9111 legal_bool_9111_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9111_nonregister : has_register 9111 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9111_normalized invalid old current result :
 (exists value, VM.find 9110 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9102 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9111 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9111_expr old old = Some value).
 { cbn [legal_bool_9111_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9111_position|exact legal_bool_9111_safe|exact legal_bool_9111_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9112_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9111)) (@Eref VarOrder.T (@Eid VarOrder.T 9104))).
Definition legal_bool_9112_tail := match straight_drop 9886 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9112_position : straight_drop 9885 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9112 legal_bool_9112_expr) legal_bool_9112_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9112_safe : formal_typed_suffix_safe flat_memories 9112 legal_bool_9112_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9112_nonregister : has_register 9112 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9112_normalized invalid old current result :
 (exists value, VM.find 9111 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9104 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9112 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9112_expr old old = Some value).
 { cbn [legal_bool_9112_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9112_position|exact legal_bool_9112_safe|exact legal_bool_9112_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9113_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9112)) (@Eref VarOrder.T (@Eid VarOrder.T 9106))).
Definition legal_bool_9113_tail := match straight_drop 9887 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9113_position : straight_drop 9886 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9113 legal_bool_9113_expr) legal_bool_9113_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9113_safe : formal_typed_suffix_safe flat_memories 9113 legal_bool_9113_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9113_nonregister : has_register 9113 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9113_normalized invalid old current result :
 (exists value, VM.find 9112 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9106 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9113 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9113_expr old old = Some value).
 { cbn [legal_bool_9113_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9113_position|exact legal_bool_9113_safe|exact legal_bool_9113_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9114_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9090)) (@Eref VarOrder.T (@Eid VarOrder.T 9113))).
Definition legal_bool_9114_tail := match straight_drop 9888 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9114_position : straight_drop 9887 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9114 legal_bool_9114_expr) legal_bool_9114_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9114_safe : formal_typed_suffix_safe flat_memories 9114 legal_bool_9114_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9114_nonregister : has_register 9114 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9114_normalized invalid old current result :
 (exists value, VM.find 9090 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9113 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9114 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9114_expr old old = Some value).
 { cbn [legal_bool_9114_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9114_position|exact legal_bool_9114_safe|exact legal_bool_9114_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9116_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 2) [::true; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9115))).
Definition legal_bool_9116_tail := match straight_drop 9890 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9116_position : straight_drop 9889 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9116 legal_bool_9116_expr) legal_bool_9116_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9116_safe : formal_typed_suffix_safe flat_memories 9116 legal_bool_9116_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9116_nonregister : has_register 9116 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9116_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9116 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9116_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9116_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9116_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9115 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9116_position|exact legal_bool_9116_safe|exact legal_bool_9116_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9118_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9117))).
Definition legal_bool_9118_tail := match straight_drop 9892 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9118_position : straight_drop 9891 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9118 legal_bool_9118_expr) legal_bool_9118_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9118_safe : formal_typed_suffix_safe flat_memories 9118 legal_bool_9118_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9118_nonregister : has_register 9118 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9118_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9118 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9118_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9118_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9118_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9117 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9118_position|exact legal_bool_9118_safe|exact legal_bool_9118_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9120_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9119))).
Definition legal_bool_9120_tail := match straight_drop 9894 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9120_position : straight_drop 9893 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9120 legal_bool_9120_expr) legal_bool_9120_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9120_safe : formal_typed_suffix_safe flat_memories 9120 legal_bool_9120_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9120_nonregister : has_register 9120 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9120_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9120 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9120_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9120_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9120_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9119 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9120_position|exact legal_bool_9120_safe|exact legal_bool_9120_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9122_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; false; false; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9121))).
Definition legal_bool_9122_tail := match straight_drop 9896 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9122_position : straight_drop 9895 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9122 legal_bool_9122_expr) legal_bool_9122_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9122_safe : formal_typed_suffix_safe flat_memories 9122 legal_bool_9122_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9122_nonregister : has_register 9122 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9122_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9122 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9122_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9122_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9122_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9121 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9122_position|exact legal_bool_9122_safe|exact legal_bool_9122_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9124_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 15) [::true; true; false; false; false; false; false; false; false; false; false; false; true; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9123))).
Definition legal_bool_9124_tail := match straight_drop 9898 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9124_position : straight_drop 9897 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9124 legal_bool_9124_expr) legal_bool_9124_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9124_safe : formal_typed_suffix_safe flat_memories 9124 legal_bool_9124_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9124_nonregister : has_register 9124 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9124_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9124 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9124_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9124_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9124_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9123 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9124_position|exact legal_bool_9124_safe|exact legal_bool_9124_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9126_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 6) [::true; true; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9125))).
Definition legal_bool_9126_tail := match straight_drop 9900 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9126_position : straight_drop 9899 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9126 legal_bool_9126_expr) legal_bool_9126_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9126_safe : formal_typed_suffix_safe flat_memories 9126 legal_bool_9126_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9126_nonregister : has_register 9126 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9126_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9126 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9126_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9126_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9126_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9125 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9126_position|exact legal_bool_9126_safe|exact legal_bool_9126_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9128_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 13) [::true; true; false; false; false; true; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9127))).
Definition legal_bool_9128_tail := match straight_drop 9902 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9128_position : straight_drop 9901 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9128 legal_bool_9128_expr) legal_bool_9128_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9128_safe : formal_typed_suffix_safe flat_memories 9128 legal_bool_9128_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9128_nonregister : has_register 9128 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9128_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9128 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9128_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9128_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9128_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9127 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9128_position|exact legal_bool_9128_safe|exact legal_bool_9128_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9130_expr := (@Eprim_binop VarOrder.T (Bcomp Beq) (@Econst VarOrder.T (Fuint 14) [::true; true; false; false; false; true; false; false; false; false; false; false; false; true]) (@Eref VarOrder.T (@Eid VarOrder.T 9129))).
Definition legal_bool_9130_tail := match straight_drop 9904 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9130_position : straight_drop 9903 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9130 legal_bool_9130_expr) legal_bool_9130_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9130_safe : formal_typed_suffix_safe flat_memories 9130 legal_bool_9130_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9130_nonregister : has_register 9130 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9130_normalized invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9130 result = Some value /\ normalized_bit value.
Proof.
 intro Step.
 destruct (formal_successful_node _ _ _ _ _ invalid flat_memories old false current result legal_bool_9130_position Step) as [value Eval].
 change (eval_hfexpr_with_memory flat_memories legal_bool_9130_expr old old = Some value) in Eval.
 assert (Normal : normalized_bit value).
 { cbn [legal_bool_9130_expr eval_hfexpr_with_memory eval_href_with_memory] in Eval.
   destruct (VM.find 9129 old) as [source|]; [|discriminate Eval].
   eapply comparison_uint_constant_left_normalized; exact Eval. }
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9130_position|exact legal_bool_9130_safe|exact legal_bool_9130_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9131_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9116)) (@Eref VarOrder.T (@Eid VarOrder.T 9118))).
Definition legal_bool_9131_tail := match straight_drop 9905 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9131_position : straight_drop 9904 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9131 legal_bool_9131_expr) legal_bool_9131_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9131_safe : formal_typed_suffix_safe flat_memories 9131 legal_bool_9131_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9131_nonregister : has_register 9131 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9131_normalized invalid old current result :
 (exists value, VM.find 9116 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9118 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9131 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9131_expr old old = Some value).
 { cbn [legal_bool_9131_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9131_position|exact legal_bool_9131_safe|exact legal_bool_9131_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9132_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9131)) (@Eref VarOrder.T (@Eid VarOrder.T 9120))).
Definition legal_bool_9132_tail := match straight_drop 9906 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9132_position : straight_drop 9905 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9132 legal_bool_9132_expr) legal_bool_9132_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9132_safe : formal_typed_suffix_safe flat_memories 9132 legal_bool_9132_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9132_nonregister : has_register 9132 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9132_normalized invalid old current result :
 (exists value, VM.find 9131 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9120 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9132 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9132_expr old old = Some value).
 { cbn [legal_bool_9132_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9132_position|exact legal_bool_9132_safe|exact legal_bool_9132_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9133_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9132)) (@Eref VarOrder.T (@Eid VarOrder.T 9122))).
Definition legal_bool_9133_tail := match straight_drop 9907 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9133_position : straight_drop 9906 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9133 legal_bool_9133_expr) legal_bool_9133_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9133_safe : formal_typed_suffix_safe flat_memories 9133 legal_bool_9133_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9133_nonregister : has_register 9133 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9133_normalized invalid old current result :
 (exists value, VM.find 9132 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9122 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9133 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9133_expr old old = Some value).
 { cbn [legal_bool_9133_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9133_position|exact legal_bool_9133_safe|exact legal_bool_9133_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9134_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9133)) (@Eref VarOrder.T (@Eid VarOrder.T 9124))).
Definition legal_bool_9134_tail := match straight_drop 9908 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9134_position : straight_drop 9907 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9134 legal_bool_9134_expr) legal_bool_9134_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9134_safe : formal_typed_suffix_safe flat_memories 9134 legal_bool_9134_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9134_nonregister : has_register 9134 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9134_normalized invalid old current result :
 (exists value, VM.find 9133 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9124 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9134 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9134_expr old old = Some value).
 { cbn [legal_bool_9134_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9134_position|exact legal_bool_9134_safe|exact legal_bool_9134_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9135_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9134)) (@Eref VarOrder.T (@Eid VarOrder.T 9126))).
Definition legal_bool_9135_tail := match straight_drop 9909 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9135_position : straight_drop 9908 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9135 legal_bool_9135_expr) legal_bool_9135_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9135_safe : formal_typed_suffix_safe flat_memories 9135 legal_bool_9135_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9135_nonregister : has_register 9135 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9135_normalized invalid old current result :
 (exists value, VM.find 9134 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9126 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9135 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9135_expr old old = Some value).
 { cbn [legal_bool_9135_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9135_position|exact legal_bool_9135_safe|exact legal_bool_9135_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9136_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9135)) (@Eref VarOrder.T (@Eid VarOrder.T 9128))).
Definition legal_bool_9136_tail := match straight_drop 9910 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9136_position : straight_drop 9909 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9136 legal_bool_9136_expr) legal_bool_9136_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9136_safe : formal_typed_suffix_safe flat_memories 9136 legal_bool_9136_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9136_nonregister : has_register 9136 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9136_normalized invalid old current result :
 (exists value, VM.find 9135 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9128 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9136 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9136_expr old old = Some value).
 { cbn [legal_bool_9136_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9136_position|exact legal_bool_9136_safe|exact legal_bool_9136_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9137_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9136)) (@Eref VarOrder.T (@Eid VarOrder.T 9130))).
Definition legal_bool_9137_tail := match straight_drop 9911 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9137_position : straight_drop 9910 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9137 legal_bool_9137_expr) legal_bool_9137_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9137_safe : formal_typed_suffix_safe flat_memories 9137 legal_bool_9137_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9137_nonregister : has_register 9137 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9137_normalized invalid old current result :
 (exists value, VM.find 9136 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9130 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9137 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9137_expr old old = Some value).
 { cbn [legal_bool_9137_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9137_position|exact legal_bool_9137_safe|exact legal_bool_9137_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9138_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9114)) (@Eref VarOrder.T (@Eid VarOrder.T 9137))).
Definition legal_bool_9138_tail := match straight_drop 9912 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9138_position : straight_drop 9911 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9138 legal_bool_9138_expr) legal_bool_9138_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9138_safe : formal_typed_suffix_safe flat_memories 9138 legal_bool_9138_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9138_nonregister : has_register 9138 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9138_normalized invalid old current result :
 (exists value, VM.find 9114 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9137 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9138 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9138_expr old old = Some value).
 { cbn [legal_bool_9138_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9138_position|exact legal_bool_9138_safe|exact legal_bool_9138_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Definition legal_bool_9139_expr := (@Eprim_binop VarOrder.T Bor (@Eref VarOrder.T (@Eid VarOrder.T 9028)) (@Eref VarOrder.T (@Eid VarOrder.T 9138))).
Definition legal_bool_9139_tail := match straight_drop 9913 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma legal_bool_9139_position : straight_drop 9912 flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T 9139 legal_bool_9139_expr) legal_bool_9139_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma legal_bool_9139_safe : formal_typed_suffix_safe flat_memories 9139 legal_bool_9139_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma legal_bool_9139_nonregister : has_register 9139 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem legal_bool_9139_normalized invalid old current result :
 (exists value, VM.find 9028 old = Some value /\ normalized_bit value) ->
 (exists value, VM.find 9138 old = Some value /\ normalized_bit value) ->
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value, VM.find 9139 result = Some value /\ normalized_bit value.
Proof.
 intros [left [Left NL]] [right [Right NR]] Step.
 set (value := normalized_or_value left right).
 assert (Eval : eval_hfexpr_with_memory flat_memories legal_bool_9139_expr old old = Some value).
 { cbn [legal_bool_9139_expr eval_hfexpr_with_memory eval_href_with_memory]. rewrite Left Right.
   exact (normalized_or_total left right NL NR). }
 pose proof (normalized_or_normal left right NL NR) as Normal.
 change (normalized_bit value) in Normal.
 exists value. split; [|exact Normal].
 eapply formal_combinational_known_node;
 [exact legal_bool_9139_position|exact legal_bool_9139_safe|exact legal_bool_9139_nonregister|exact Eval|destruct Normal; reflexivity|exact Step].
Qed.
Print Assumptions legal_bool_9139_normalized.
