Require Import FormalRFResetPropagation CoreSocModel ComparisonNodes JointRegisterCommits6 JointRegisterExpressionCertificates FormalUIntRegisterUnaryCommitSource ConcreteGroundUIntAdapt.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Lemma front_pc_resize_sized width bits :
 size bits = width -> zext_to width (take width bits) = bits.
Proof.
 intro Size. rewrite -Size take_size. unfold zext_to. rewrite subnn. unfold zext. rewrite cats0. reflexivity.
Qed.
Theorem front_pc_normal_commit invalid old current result old_value bits reset_bits :
 VM.find 7749 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 65 old = Some (Gval (Fuint 1) [::false]) ->
 VM.find 7800 old = Some (Gval (Fuint 33) bits) -> size bits = 33%nat ->
 VM.find 8159 old = Some (Gval (Fuint 32) reset_bits) ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7749 result = Some (Gval (Fuint 32) (take 32 bits)).
Proof.
 intros Old Typed Reset Input Size Other Step.
 destruct (formal_committed_uint_register_unary_observation 8255 flat_statements joint_register_7749_decl
 joint_register_7749_mid joint_register_7749_tail 7749 joint_register_7749_reg (Uextr 31 0)
 (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 65)) (@Eref VarOrder.T (@Eid VarOrder.T 8159)) (@Eref VarOrder.T (@Eid VarOrder.T 7800)))
 invalid flat_memories old current result old_value 32 joint_register_7749_position joint_register_7749_split
 joint_register_7749_straight joint_register_7749_mid_safe joint_register_7749_tail_safe Old Typed joint_register_7749_identity Step)
 as [source [value [Source [Adapt Value]]]].
 cbn [eval_hfexpr_validif_policy eval_href_validif_policy] in Source.
 rewrite Reset in Source. cbn [is_zero eval_hfexpr_validif_policy eval_href_validif_policy] in Source.
 rewrite Input in Source. unfold eval_type_of_expr in Source.
 cbn [type_of_expr' eval_type_of_ref] in Source. rewrite Other in Source.
 cbn [is_zero option_map make_ftype_explicit type_of_val extend_hvalue_as_type ftype_mux fgtyp_mux adapt_hvalue_as_type eval_unop] in Source.
 assert (Zero : is_zero [::false] = true) by (vm_compute; reflexivity).
 assert (Max : maxn 33 32 = 33%nat) by (vm_compute; reflexivity).
 rewrite Zero Max in Source.
 assert (Range : (0 <= 31 < 33)%nat = true) by (vm_compute; reflexivity).
 rewrite Range subn0 drop0 in Source.
 change (Some (Gval (Fuint 32) (take 32 (zext_to 33 (take 33 bits)))) = Some source) in Source.
 rewrite (front_pc_resize_sized 33 bits Size) in Source. inversion Source; subst source.
 assert (LowSize : size (take 32 bits) = 32%nat).
 { rewrite size_take Size. reflexivity. }
 rewrite (sized_uint_adapt_identity 32 (take 32 bits) LowSize) in Adapt.
 inversion Adapt; subst value. exact Value.
Qed.
Print Assumptions front_pc_normal_commit.
