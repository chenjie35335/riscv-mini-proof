Require Import CoreSocModel ComparisonNodes.
From Coq Require Import ZArith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var FMaps.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths
 Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths
 Semantics_with_implicit_widths Semantics_with_memory.

(* The four expressions below are checked against the generated AST. *)
Fixpoint top_level_node (id : VarOrder.T) (stmts : HiF.hfstmt_seq) : option HiF.hfexpr :=
 match stmts with
 | Qnil => None
 | Qcons (Snode name expression) tail =>
   if id == name then Some expression else top_level_node id tail
 | Qcons _ tail => top_level_node id tail end.

Definition rf_addr_ref : HiF.href := @Eid VarOrder.T (N.of_nat 785).
Definition rf_enable_ref : HiF.href := @Eid VarOrder.T (N.of_nat 784).
Definition rf_zero_expr : HiF.hfexpr := @Econst VarOrder.T (Fuint 1) [:: false].
Definition rf_addr_nonzero_expr : HiF.hfexpr :=
 @Eprim_unop VarOrder.T Uorr (@Eref VarOrder.T rf_addr_ref).
Definition rf_write_guard_expr : HiF.hfexpr :=
 @Eprim_binop VarOrder.T Band (@Eref VarOrder.T rf_enable_ref)
   (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat 953))).
Definition rf_x0_selected_expr : HiF.hfexpr :=
 @Emux VarOrder.T
   (@Eprim_binop VarOrder.T (Bcomp Beq) rf_zero_expr (@Eref VarOrder.T rf_addr_ref))
   (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat 988))) rf_zero_expr.
Definition rf_x0_output_expr : HiF.hfexpr :=
 @Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat 954)))
   (@Eref VarOrder.T (@Eid VarOrder.T (N.of_nat 989))) rf_zero_expr.

Lemma rf_addr_node_exact : top_level_node (N.of_nat 953) flat_statements = Some rf_addr_nonzero_expr.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_guard_node_exact : top_level_node (N.of_nat 954) flat_statements = Some rf_write_guard_expr.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_selected_node_exact : top_level_node (N.of_nat 989) flat_statements = Some rf_x0_selected_expr.
Proof. vm_compute. reflexivity. Qed.
Lemma rf_output_node_exact : top_level_node (N.of_nat 1053) flat_statements = Some rf_x0_output_expr.
Proof. vm_compute. reflexivity. Qed.

Definition rf_zero32 := Gval (Fuint 32) (zeros 32).

Lemma rf_x0_output_disabled env :
 VM.find (N.of_nat 954) env = Some (Gval (Fuint 1) [::false]) ->
 eval_type_of_ref (@Eid VarOrder.T (N.of_nat 989)) env = Some (Gtyp (Fuint 32)) ->
 eval_hfexpr rf_x0_output_expr env env = Some rf_zero32.
Proof.
 intros Guard SelectedType.
 cbn [rf_x0_output_expr eval_hfexpr eval_href]. rewrite Guard.
 cbn [is_zero rf_zero_expr eval_hfexpr].
 unfold eval_type_of_expr. cbn [type_of_expr'].
 rewrite SelectedType. reflexivity.
Qed.

Lemma rf_x0_output_enabled env :
 VM.find (N.of_nat 954) env = Some (Gval (Fuint 1) [::true]) ->
 VM.find (N.of_nat 989) env = Some rf_zero32 ->
 eval_hfexpr rf_x0_output_expr env env = Some rf_zero32.
Proof.
 intros Guard Selected.
 cbn [rf_x0_output_expr eval_hfexpr eval_href]. rewrite Guard.
 cbn [is_zero rf_zero_expr eval_hfexpr eval_href]. rewrite Selected. reflexivity.
Qed.

(* This environment contains exactly the inputs read by the selected cone.
   It is not asserted to be a reachable CoreSoc state. The theorem below
   establishes its combinational arithmetic before proving propagation. *)
Definition rf_x0_inputs (enable : bool) (address data : bits) : VM.t hvalue :=
 VM.add (N.of_nat 988) (Gval (Fuint 32) data)
  (VM.add (N.of_nat 784) (Gval (Fuint 1) [::enable])
   (VM.add (N.of_nat 785) (Gval (Fuint 5) address) (VM.empty hvalue))).

Definition rf_x0_cone (enable : bool) (address data : bits) : option hvalue :=
 let inputs := rf_x0_inputs enable address data in
 match eval_hfexpr rf_addr_nonzero_expr inputs inputs with
 | Some addr_nonzero =>
   let after_addr := VM.add (N.of_nat 953) addr_nonzero inputs in
   match eval_hfexpr rf_write_guard_expr after_addr after_addr,
         eval_hfexpr rf_x0_selected_expr after_addr after_addr with
   | Some guard, Some selected =>
     let ready := VM.add (N.of_nat 989) selected (VM.add (N.of_nat 954) guard after_addr) in
     eval_hfexpr rf_x0_output_expr ready ready
   | _, _ => None end
 | None => None end.

Theorem rf_x0_cone_five_bits enable b0 b1 b2 b3 b4 data :
 rf_x0_cone enable [::b0; b1; b2; b3; b4] data = Some rf_zero32.
Proof.
 destruct enable, b0, b1, b2, b3, b4; vm_compute; reflexivity.
Qed.

Theorem rf_x0_cone_any_address enable address data :
 size address = 5 -> rf_x0_cone enable address data = Some rf_zero32.
Proof.
 intro Width.
 destruct address as [|b0 address]; [discriminate Width|].
 destruct address as [|b1 address]; [discriminate Width|].
 destruct address as [|b2 address]; [discriminate Width|].
 destruct address as [|b3 address]; [discriminate Width|].
 destruct address as [|b4 address]; [discriminate Width|].
 destruct address as [|extra address].
 - apply rf_x0_cone_five_bits.
 - cbn [size] in Width. lia.
Qed.

Corollary rf_x0_cone_formal_words enable (address : symbolic_word 5) (data : symbolic_word 32) :
 rf_x0_cone enable (proj1_sig address) (proj1_sig data) = Some rf_zero32.
Proof. apply rf_x0_cone_any_address. exact (proj2_sig address). Qed.

Print Assumptions rf_x0_cone_formal_words.

Lemma rf_addr_value env address :
 eval_href rf_addr_ref env env = Some (Gval (Fuint 5) address) ->
 eval_hfexpr rf_addr_nonzero_expr env env =
 Some (Gval (Fuint 1) [::foldr orb false address]).
Proof.
 intro Address.
 change ((match eval_href rf_addr_ref env env with
   | Some value => eval_unop Uorr value | None => None end) =
   Some (Gval (Fuint 1) [::foldr orb false address])).
 rewrite Address. reflexivity.
Qed.

Lemma rf_guard_value env enable nonzero :
 eval_href rf_enable_ref env env = Some (Gval (Fuint 1) [::enable]) ->
 VM.find (N.of_nat 953) env = Some (Gval (Fuint 1) [::nonzero]) ->
 eval_hfexpr rf_write_guard_expr env env = Some (Gval (Fuint 1) [::enable && nonzero]).
Proof.
 intros Enable Nonzero.
 change ((match eval_href rf_enable_ref env env, VM.find (N.of_nat 953) env with
   | Some value_left, Some value_right => eval_binop Band value_left value_right | _, _ => None end) =
   Some (Gval (Fuint 1) [::enable && nonzero])).
 rewrite Enable Nonzero. destruct enable, nonzero; vm_compute; reflexivity.
Qed.

Definition rf_selected_bits address data :=
 if is_zero address then zext_to 32 (take 32 data) else zeros 32.

Lemma rf_selected_value_five_bits env b0 b1 b2 b3 b4 data :
 eval_href rf_addr_ref env env = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find (N.of_nat 988) env = Some (Gval (Fuint 32) data) ->
 eval_hfexpr rf_x0_selected_expr env env =
 Some (Gval (Fuint 32) (rf_selected_bits [::b0;b1;b2;b3;b4] data)).
Proof.
 intros Address Data.
 unfold rf_x0_selected_expr. cbn [eval_hfexpr]. rewrite Address.
 cbn [rf_zero_expr eval_hfexpr].
 destruct b0, b1, b2, b3, b4;
   cbn [eval_binop eval_binop_basic absorbing_bit refine_boolean_result];
   cbn [is_zero eval_hfexpr eval_href];
   unfold eval_type_of_expr; cbn [type_of_expr' eval_type_of_ref];
   rewrite Data; reflexivity.
Qed.

Theorem rf_coherent_x0_five_bits env enable b0 b1 b2 b3 b4 data :
 eval_href rf_enable_ref env env = Some (Gval (Fuint 1) [::enable]) ->
 eval_href rf_addr_ref env env = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 VM.find (N.of_nat 988) env = Some (Gval (Fuint 32) data) ->
 VM.find (N.of_nat 953) env = eval_hfexpr rf_addr_nonzero_expr env env ->
 VM.find (N.of_nat 954) env = eval_hfexpr rf_write_guard_expr env env ->
 VM.find (N.of_nat 989) env = eval_hfexpr rf_x0_selected_expr env env ->
 eval_hfexpr rf_x0_output_expr env env = Some rf_zero32.
Proof.
 intros Enable Address Data Reduction Guard Selected.
 rewrite (rf_addr_value env _ Address) in Reduction.
 rewrite (rf_guard_value env enable _ Enable Reduction) in Guard.
 rewrite (rf_selected_value_five_bits env b0 b1 b2 b3 b4 data Address Data) in Selected.
 destruct enable, b0, b1, b2, b3, b4;
   cbn [foldr andb orb rf_selected_bits is_zero] in Guard, Selected;
   first [apply rf_x0_output_enabled; [exact Guard|exact Selected] |
     apply rf_x0_output_disabled; [exact Guard|
       cbn [eval_type_of_ref]; rewrite Selected; reflexivity]].
Qed.

Theorem rf_coherent_x0 env enable address data :
 size address = 5 ->
 eval_href rf_enable_ref env env = Some (Gval (Fuint 1) [::enable]) ->
 eval_href rf_addr_ref env env = Some (Gval (Fuint 5) address) ->
 VM.find (N.of_nat 988) env = Some (Gval (Fuint 32) data) ->
 VM.find (N.of_nat 953) env = eval_hfexpr rf_addr_nonzero_expr env env ->
 VM.find (N.of_nat 954) env = eval_hfexpr rf_write_guard_expr env env ->
 VM.find (N.of_nat 989) env = eval_hfexpr rf_x0_selected_expr env env ->
 eval_hfexpr rf_x0_output_expr env env = Some rf_zero32.
Proof.
 intro Width.
 destruct address as [|b0 address]; [discriminate Width|].
 destruct address as [|b1 address]; [discriminate Width|].
 destruct address as [|b2 address]; [discriminate Width|].
 destruct address as [|b3 address]; [discriminate Width|].
 destruct address as [|b4 address]; [discriminate Width|].
 destruct address as [|extra address].
 - apply rf_coherent_x0_five_bits.
 - cbn [size] in Width. lia.
Qed.

Print Assumptions rf_coherent_x0.

(* Equations to be obtained from a whole-module iteration. They deliberately
   use the previous iteration's environment, as the production evaluator does. *)
Definition rf_x0_round (before after : VM.t hvalue) :=
 VM.find (N.of_nat 953) after = eval_hfexpr rf_addr_nonzero_expr before before /\
 VM.find (N.of_nat 954) after = eval_hfexpr rf_write_guard_expr before before /\
 VM.find (N.of_nat 989) after = eval_hfexpr rf_x0_selected_expr before before /\
 VM.find (N.of_nat 1053) after = eval_hfexpr rf_x0_output_expr before before.

Theorem rf_x0_after_three_rounds_five_bits first second third fourth enable b0 b1 b2 b3 b4 data :
 eval_href rf_addr_ref first first = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 eval_href rf_addr_ref second second = Some (Gval (Fuint 5) [::b0;b1;b2;b3;b4]) ->
 eval_href rf_enable_ref second second = Some (Gval (Fuint 1) [::enable]) ->
 VM.find (N.of_nat 988) second = Some (Gval (Fuint 32) data) ->
 rf_x0_round first second -> rf_x0_round second third -> rf_x0_round third fourth ->
 VM.find (N.of_nat 1053) fourth = Some rf_zero32.
Proof.
 intros AddressFirst AddressSecond Enable Data
   [Reduction _] [_ [Guard [Selected _]]] [_ [_ [_ Output]]].
 rewrite (rf_addr_value first _ AddressFirst) in Reduction.
 rewrite (rf_guard_value second enable _ Enable Reduction) in Guard.
 rewrite (rf_selected_value_five_bits second b0 b1 b2 b3 b4 data AddressSecond Data) in Selected.
 rewrite Output.
 destruct enable, b0, b1, b2, b3, b4;
   cbn [foldr andb orb rf_selected_bits is_zero] in Guard, Selected;
   first [apply rf_x0_output_enabled; [exact Guard|exact Selected] |
     apply rf_x0_output_disabled; [exact Guard|
       cbn [eval_type_of_ref]; rewrite Selected; reflexivity]].
Qed.

Theorem rf_x0_after_three_rounds first second third fourth enable address data :
 size address = 5 ->
 eval_href rf_addr_ref first first = Some (Gval (Fuint 5) address) ->
 eval_href rf_addr_ref second second = Some (Gval (Fuint 5) address) ->
 eval_href rf_enable_ref second second = Some (Gval (Fuint 1) [::enable]) ->
 VM.find (N.of_nat 988) second = Some (Gval (Fuint 32) data) ->
 rf_x0_round first second -> rf_x0_round second third -> rf_x0_round third fourth ->
 VM.find (N.of_nat 1053) fourth = Some rf_zero32.
Proof.
 intro Width.
 destruct address as [|b0 address]; [discriminate Width|].
 destruct address as [|b1 address]; [discriminate Width|].
 destruct address as [|b2 address]; [discriminate Width|].
 destruct address as [|b3 address]; [discriminate Width|].
 destruct address as [|b4 address]; [discriminate Width|].
 destruct address as [|extra address].
 - apply rf_x0_after_three_rounds_five_bits.
 - cbn [size] in Width. lia.
Qed.

Print Assumptions rf_x0_after_three_rounds.
