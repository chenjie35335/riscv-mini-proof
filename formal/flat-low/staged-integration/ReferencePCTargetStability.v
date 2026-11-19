Require Import CoreSocModel ComparisonNodes SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceControlGroundOperations ReferenceControlGroundExpressions ReferenceControlNodeGeneric ReferenceControlStabilityHistory.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition ref_pc_target_nodes : seq(VarOrder.T*hfexpr VarOrder.T) := [::(6309,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6310,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6309))));(6315,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2966)) (@Eref VarOrder.T (@Eid VarOrder.T 6310)) (@Eref VarOrder.T (@Eid VarOrder.T 2812))));(6326,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2357)) (@Eref VarOrder.T (@Eid VarOrder.T 6315)) (@Eref VarOrder.T (@Eid VarOrder.T 2812))));(6335,(@Eref VarOrder.T (@Eid VarOrder.T 2209)));(6336,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6335)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6337,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6336))));(6338,(@Eprim_unop VarOrder.T (Uextr 31 1) (@Eref VarOrder.T (@Eid VarOrder.T 6337))));(6339,(@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 6338)) (@Econst VarOrder.T (Fuint 1) [::false])));(6347,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2949)) (@Eref VarOrder.T (@Eid VarOrder.T 6339)) (@Eref VarOrder.T (@Eid VarOrder.T 6326))));(6360,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2010)) (@Eref VarOrder.T (@Eid VarOrder.T 6347)) (@Eref VarOrder.T (@Eid VarOrder.T 6326))));(6369,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6370,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6369))));(6374,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2929)) (@Eref VarOrder.T (@Eid VarOrder.T 6370)) (@Eref VarOrder.T (@Eid VarOrder.T 6360))));(6378,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2912)) (@Eref VarOrder.T (@Eid VarOrder.T 6374)) (@Eref VarOrder.T (@Eid VarOrder.T 6360))));(6388,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2004)) (@Eref VarOrder.T (@Eid VarOrder.T 6378)) (@Eref VarOrder.T (@Eid VarOrder.T 6360))));(6393,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6394,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6393))));(6398,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2909)) (@Eref VarOrder.T (@Eid VarOrder.T 6394)) (@Eref VarOrder.T (@Eid VarOrder.T 6388))));(6402,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2892)) (@Eref VarOrder.T (@Eid VarOrder.T 6398)) (@Eref VarOrder.T (@Eid VarOrder.T 6388))));(6412,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1998)) (@Eref VarOrder.T (@Eid VarOrder.T 6402)) (@Eref VarOrder.T (@Eid VarOrder.T 6388))));(6417,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6418,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6417))));(6422,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2889)) (@Eref VarOrder.T (@Eid VarOrder.T 6418)) (@Eref VarOrder.T (@Eid VarOrder.T 6412))));(6426,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2872)) (@Eref VarOrder.T (@Eid VarOrder.T 6422)) (@Eref VarOrder.T (@Eid VarOrder.T 6412))));(6436,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1992)) (@Eref VarOrder.T (@Eid VarOrder.T 6426)) (@Eref VarOrder.T (@Eid VarOrder.T 6412))));(6441,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6442,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6441))));(6446,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2867)) (@Eref VarOrder.T (@Eid VarOrder.T 6442)) (@Eref VarOrder.T (@Eid VarOrder.T 6436))));(6450,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2850)) (@Eref VarOrder.T (@Eid VarOrder.T 6446)) (@Eref VarOrder.T (@Eid VarOrder.T 6436))));(6460,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1986)) (@Eref VarOrder.T (@Eid VarOrder.T 6450)) (@Eref VarOrder.T (@Eid VarOrder.T 6436))));(6465,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6466,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6465))));(6470,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2847)) (@Eref VarOrder.T (@Eid VarOrder.T 6466)) (@Eref VarOrder.T (@Eid VarOrder.T 6460))));(6474,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2830)) (@Eref VarOrder.T (@Eid VarOrder.T 6470)) (@Eref VarOrder.T (@Eid VarOrder.T 6460))));(6484,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1980)) (@Eref VarOrder.T (@Eid VarOrder.T 6474)) (@Eref VarOrder.T (@Eid VarOrder.T 6460))));(6489,(@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))));(6490,(@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6489))));(6494,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2825)) (@Eref VarOrder.T (@Eid VarOrder.T 6490)) (@Eref VarOrder.T (@Eid VarOrder.T 6484))));(6498,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2806)) (@Eref VarOrder.T (@Eid VarOrder.T 6494)) (@Eref VarOrder.T (@Eid VarOrder.T 6484))));(6508,(@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1974)) (@Eref VarOrder.T (@Eid VarOrder.T 6498)) (@Eref VarOrder.T (@Eid VarOrder.T 6484))))].
Definition ref_pc_target_offsets := [::6388%nat;0%nat;4%nat;10%nat;8%nat;0%nat;0%nat;0%nat;0%nat;7%nat;12%nat;8%nat;0%nat;3%nat;3%nat;9%nat;4%nat;0%nat;3%nat;3%nat;9%nat;4%nat;0%nat;3%nat;3%nat;9%nat;4%nat;0%nat;3%nat;3%nat;9%nat;4%nat;0%nat;3%nat;3%nat;9%nat;4%nat;0%nat;3%nat;3%nat;9%nat].
Definition ref_pc_target_cuts : seq VarOrder.T := [::1974;1980;1986;1992;1998;2004;2010;2209;2357;2552;2806;2812;2825;2830;2847;2850;2867;2872;2889;2892;2909;2912;2929;2949;2966].
Definition ref_pc_target_ranks := [::1%nat;2%nat;3%nat;4%nat;1%nat;2%nat;3%nat;4%nat;5%nat;6%nat;7%nat;1%nat;2%nat;8%nat;9%nat;10%nat;1%nat;2%nat;11%nat;12%nat;13%nat;1%nat;2%nat;14%nat;15%nat;16%nat;1%nat;2%nat;17%nat;18%nat;19%nat;1%nat;2%nat;20%nat;21%nat;22%nat;1%nat;2%nat;23%nat;24%nat;25%nat].
Definition ref_pc_target_dependencies : seq(seq VarOrder.T) := [::[::2552;2812];[::6309];[::2812;2966;6310];[::2357;2812;6315];[::2209];[::2552;6335];[::6336];[::6337];[::6338];[::2949;6326;6339];[::2010;6326;6347];[::2552;2812];[::6369];[::2929;6360;6370];[::2912;6360;6374];[::2004;6360;6378];[::2552;2812];[::6393];[::2909;6388;6394];[::2892;6388;6398];[::1998;6388;6402];[::2552;2812];[::6417];[::2889;6412;6418];[::2872;6412;6422];[::1992;6412;6426];[::2552;2812];[::6441];[::2867;6436;6442];[::2850;6436;6446];[::1986;6436;6450];[::2552;2812];[::6465];[::2847;6460;6466];[::2830;6460;6470];[::1980;6460;6474];[::2552;2812];[::6489];[::2825;6484;6490];[::2806;6484;6494];[::1974;6484;6498]].
Definition ref_pc_target_node i :=fst(nth(0,@Econst VarOrder.T(Fuint 1)[::false])ref_pc_target_nodes i).
Definition ref_pc_target_expression i :=snd(nth(0,@Econst VarOrder.T(Fuint 1)[::false])ref_pc_target_nodes i).
Definition ref_pc_target_rank i :=nth 0%nat ref_pc_target_ranks i.
Definition ref_pc_target_refs i :=nth [::]ref_pc_target_dependencies i.
Lemma ref_pc_target_positions :select_node_offsets ref_pc_target_offsets flat_statements=Some ref_pc_target_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma ref_pc_target_safety :selected_node_safety flat_memories flat_statements ref_pc_target_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma ref_pc_target_ready i old :(i<41)%coq_nat ->
 (forall node,List.In node(ref_pc_target_refs i) ->exists value ground,VM.find node old=Some value /\type_of_val value=Gtyp ground) ->
 reference_control_ready old(ref_pc_target_expression i).
Proof. intro Bound.
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6309)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2966)) (@Eref VarOrder.T (@Eid VarOrder.T 6310)) (@Eref VarOrder.T (@Eid VarOrder.T 2812)))). apply rc_mux. { destruct(Values 6310 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 2812 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2357)) (@Eref VarOrder.T (@Eid VarOrder.T 6315)) (@Eref VarOrder.T (@Eid VarOrder.T 2812)))). apply rc_mux. { destruct(Values 6315 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 2812 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eref VarOrder.T (@Eid VarOrder.T 2209))). destruct(Values 2209 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6335)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6336)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Uextr 31 1) (@Eref VarOrder.T (@Eid VarOrder.T 6337)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Bcat (@Eref VarOrder.T (@Eid VarOrder.T 6338)) (@Econst VarOrder.T (Fuint 1) [::false]))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2949)) (@Eref VarOrder.T (@Eid VarOrder.T 6339)) (@Eref VarOrder.T (@Eid VarOrder.T 6326)))). apply rc_mux. { destruct(Values 6339 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6326 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2010)) (@Eref VarOrder.T (@Eid VarOrder.T 6347)) (@Eref VarOrder.T (@Eid VarOrder.T 6326)))). apply rc_mux. { destruct(Values 6347 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6326 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6369)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2929)) (@Eref VarOrder.T (@Eid VarOrder.T 6370)) (@Eref VarOrder.T (@Eid VarOrder.T 6360)))). apply rc_mux. { destruct(Values 6370 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6360 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2912)) (@Eref VarOrder.T (@Eid VarOrder.T 6374)) (@Eref VarOrder.T (@Eid VarOrder.T 6360)))). apply rc_mux. { destruct(Values 6374 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6360 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2004)) (@Eref VarOrder.T (@Eid VarOrder.T 6378)) (@Eref VarOrder.T (@Eid VarOrder.T 6360)))). apply rc_mux. { destruct(Values 6378 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6360 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6393)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2909)) (@Eref VarOrder.T (@Eid VarOrder.T 6394)) (@Eref VarOrder.T (@Eid VarOrder.T 6388)))). apply rc_mux. { destruct(Values 6394 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6388 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2892)) (@Eref VarOrder.T (@Eid VarOrder.T 6398)) (@Eref VarOrder.T (@Eid VarOrder.T 6388)))). apply rc_mux. { destruct(Values 6398 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6388 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1998)) (@Eref VarOrder.T (@Eid VarOrder.T 6402)) (@Eref VarOrder.T (@Eid VarOrder.T 6388)))). apply rc_mux. { destruct(Values 6402 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6388 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6417)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2889)) (@Eref VarOrder.T (@Eid VarOrder.T 6418)) (@Eref VarOrder.T (@Eid VarOrder.T 6412)))). apply rc_mux. { destruct(Values 6418 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6412 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2872)) (@Eref VarOrder.T (@Eid VarOrder.T 6422)) (@Eref VarOrder.T (@Eid VarOrder.T 6412)))). apply rc_mux. { destruct(Values 6422 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6412 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1992)) (@Eref VarOrder.T (@Eid VarOrder.T 6426)) (@Eref VarOrder.T (@Eid VarOrder.T 6412)))). apply rc_mux. { destruct(Values 6426 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6412 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6441)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2867)) (@Eref VarOrder.T (@Eid VarOrder.T 6442)) (@Eref VarOrder.T (@Eid VarOrder.T 6436)))). apply rc_mux. { destruct(Values 6442 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6436 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2850)) (@Eref VarOrder.T (@Eid VarOrder.T 6446)) (@Eref VarOrder.T (@Eid VarOrder.T 6436)))). apply rc_mux. { destruct(Values 6446 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6436 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1986)) (@Eref VarOrder.T (@Eid VarOrder.T 6450)) (@Eref VarOrder.T (@Eid VarOrder.T 6436)))). apply rc_mux. { destruct(Values 6450 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6436 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6465)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2847)) (@Eref VarOrder.T (@Eid VarOrder.T 6466)) (@Eref VarOrder.T (@Eid VarOrder.T 6460)))). apply rc_mux. { destruct(Values 6466 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6460 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2830)) (@Eref VarOrder.T (@Eid VarOrder.T 6470)) (@Eref VarOrder.T (@Eid VarOrder.T 6460)))). apply rc_mux. { destruct(Values 6470 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6460 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1980)) (@Eref VarOrder.T (@Eid VarOrder.T 6474)) (@Eref VarOrder.T (@Eid VarOrder.T 6460)))). apply rc_mux. { destruct(Values 6474 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6460 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 2812)) (@Eref VarOrder.T (@Eid VarOrder.T 2552)))). apply rc_binary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6489)))). apply rc_unary. }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2825)) (@Eref VarOrder.T (@Eid VarOrder.T 6490)) (@Eref VarOrder.T (@Eid VarOrder.T 6484)))). apply rc_mux. { destruct(Values 6490 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6484 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2806)) (@Eref VarOrder.T (@Eid VarOrder.T 6494)) (@Eref VarOrder.T (@Eid VarOrder.T 6484)))). apply rc_mux. { destruct(Values 6494 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6484 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 destruct i as[|i]. { intro Values. change(reference_control_ready old (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1974)) (@Eref VarOrder.T (@Eid VarOrder.T 6498)) (@Eref VarOrder.T (@Eid VarOrder.T 6484)))). apply rc_mux. { destruct(Values 6498 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } { destruct(Values 6484 ltac:(vm_compute;tauto))as[value[ground[Value Typed]]]. eapply rc_ref;[exact Value|exists ground;exact Typed]. } }
 lia. Qed.
Lemma ref_pc_target_eval_equal i inputs path left right :(i<41)%coq_nat ->
 (forall node,List.In node(ref_pc_target_refs i) ->VM.find node left=VM.find node right) ->
 forall site,eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(ref_pc_target_expression i)left left=
 eval_hfexpr_validif_policy(isolated_validif_policy(formal_invalid_policy inputs path))site flat_memories(ref_pc_target_expression i)right right.
Proof. intro Bound.
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6309 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6309 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2812 ltac:(vm_compute;tauto)) (Equal 2966 ltac:(vm_compute;tauto)) (Equal 6310 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2812 ltac:(vm_compute;tauto)) ?(Equal 2966 ltac:(vm_compute;tauto)) ?(Equal 6310 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2357 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)) (Equal 6315 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2357 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)) ?(Equal 6315 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2209 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2209 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 6335 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 6335 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6336 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6336 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6337 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6337 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6338 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6338 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2949 ltac:(vm_compute;tauto)) (Equal 6326 ltac:(vm_compute;tauto)) (Equal 6339 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2949 ltac:(vm_compute;tauto)) ?(Equal 6326 ltac:(vm_compute;tauto)) ?(Equal 6339 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2010 ltac:(vm_compute;tauto)) (Equal 6326 ltac:(vm_compute;tauto)) (Equal 6347 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2010 ltac:(vm_compute;tauto)) ?(Equal 6326 ltac:(vm_compute;tauto)) ?(Equal 6347 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6369 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6369 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2929 ltac:(vm_compute;tauto)) (Equal 6360 ltac:(vm_compute;tauto)) (Equal 6370 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2929 ltac:(vm_compute;tauto)) ?(Equal 6360 ltac:(vm_compute;tauto)) ?(Equal 6370 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2912 ltac:(vm_compute;tauto)) (Equal 6360 ltac:(vm_compute;tauto)) (Equal 6374 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2912 ltac:(vm_compute;tauto)) ?(Equal 6360 ltac:(vm_compute;tauto)) ?(Equal 6374 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2004 ltac:(vm_compute;tauto)) (Equal 6360 ltac:(vm_compute;tauto)) (Equal 6378 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2004 ltac:(vm_compute;tauto)) ?(Equal 6360 ltac:(vm_compute;tauto)) ?(Equal 6378 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6393 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6393 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2909 ltac:(vm_compute;tauto)) (Equal 6388 ltac:(vm_compute;tauto)) (Equal 6394 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2909 ltac:(vm_compute;tauto)) ?(Equal 6388 ltac:(vm_compute;tauto)) ?(Equal 6394 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2892 ltac:(vm_compute;tauto)) (Equal 6388 ltac:(vm_compute;tauto)) (Equal 6398 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2892 ltac:(vm_compute;tauto)) ?(Equal 6388 ltac:(vm_compute;tauto)) ?(Equal 6398 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 1998 ltac:(vm_compute;tauto)) (Equal 6388 ltac:(vm_compute;tauto)) (Equal 6402 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 1998 ltac:(vm_compute;tauto)) ?(Equal 6388 ltac:(vm_compute;tauto)) ?(Equal 6402 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6417 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6417 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2889 ltac:(vm_compute;tauto)) (Equal 6412 ltac:(vm_compute;tauto)) (Equal 6418 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2889 ltac:(vm_compute;tauto)) ?(Equal 6412 ltac:(vm_compute;tauto)) ?(Equal 6418 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2872 ltac:(vm_compute;tauto)) (Equal 6412 ltac:(vm_compute;tauto)) (Equal 6422 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2872 ltac:(vm_compute;tauto)) ?(Equal 6412 ltac:(vm_compute;tauto)) ?(Equal 6422 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 1992 ltac:(vm_compute;tauto)) (Equal 6412 ltac:(vm_compute;tauto)) (Equal 6426 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 1992 ltac:(vm_compute;tauto)) ?(Equal 6412 ltac:(vm_compute;tauto)) ?(Equal 6426 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6441 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6441 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2867 ltac:(vm_compute;tauto)) (Equal 6436 ltac:(vm_compute;tauto)) (Equal 6442 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2867 ltac:(vm_compute;tauto)) ?(Equal 6436 ltac:(vm_compute;tauto)) ?(Equal 6442 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2850 ltac:(vm_compute;tauto)) (Equal 6436 ltac:(vm_compute;tauto)) (Equal 6446 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2850 ltac:(vm_compute;tauto)) ?(Equal 6436 ltac:(vm_compute;tauto)) ?(Equal 6446 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 1986 ltac:(vm_compute;tauto)) (Equal 6436 ltac:(vm_compute;tauto)) (Equal 6450 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 1986 ltac:(vm_compute;tauto)) ?(Equal 6436 ltac:(vm_compute;tauto)) ?(Equal 6450 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6465 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6465 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2847 ltac:(vm_compute;tauto)) (Equal 6460 ltac:(vm_compute;tauto)) (Equal 6466 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2847 ltac:(vm_compute;tauto)) ?(Equal 6460 ltac:(vm_compute;tauto)) ?(Equal 6466 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2830 ltac:(vm_compute;tauto)) (Equal 6460 ltac:(vm_compute;tauto)) (Equal 6470 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2830 ltac:(vm_compute;tauto)) ?(Equal 6460 ltac:(vm_compute;tauto)) ?(Equal 6470 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 1980 ltac:(vm_compute;tauto)) (Equal 6460 ltac:(vm_compute;tauto)) (Equal 6474 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 1980 ltac:(vm_compute;tauto)) ?(Equal 6460 ltac:(vm_compute;tauto)) ?(Equal 6474 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2552 ltac:(vm_compute;tauto)) (Equal 2812 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2552 ltac:(vm_compute;tauto)) ?(Equal 2812 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 6489 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 6489 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2825 ltac:(vm_compute;tauto)) (Equal 6484 ltac:(vm_compute;tauto)) (Equal 6490 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2825 ltac:(vm_compute;tauto)) ?(Equal 6484 ltac:(vm_compute;tauto)) ?(Equal 6490 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 2806 ltac:(vm_compute;tauto)) (Equal 6484 ltac:(vm_compute;tauto)) (Equal 6494 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 2806 ltac:(vm_compute;tauto)) ?(Equal 6484 ltac:(vm_compute;tauto)) ?(Equal 6494 ltac:(vm_compute;tauto)).
 reflexivity. }
 destruct i as[|i]. { intros Equal site. cbn[ref_pc_target_expression ref_pc_target_nodes nth snd eval_hfexpr_validif_policy eval_href_validif_policy eval_type_of_expr type_of_expr' eval_type_of_ref].
 rewrite (Equal 1974 ltac:(vm_compute;tauto)) (Equal 6484 ltac:(vm_compute;tauto)) (Equal 6498 ltac:(vm_compute;tauto)). unfold eval_type_of_expr;cbn[type_of_expr' eval_type_of_ref];rewrite ?(Equal 1974 ltac:(vm_compute;tauto)) ?(Equal 6484 ltac:(vm_compute;tauto)) ?(Equal 6498 ltac:(vm_compute;tauto)).
 reflexivity. }
 lia. Qed.
Lemma ref_pc_target_predecessors i node :(i<41)%coq_nat ->List.In node(ref_pc_target_refs i) ->
 List.In node ref_pc_target_cuts \/ exists j,(j<i)%coq_nat /\(j<41)%coq_nat /\ref_pc_target_node j=node /\(ref_pc_target_rank j<ref_pc_target_rank i)%coq_nat.
Proof. intro Bound.
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 0%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 1%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 2%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 4%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 5%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 6%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 7%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 8%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 3%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 9%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 11%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 12%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 13%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 10%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 14%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 16%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 17%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 18%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 15%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 19%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 21%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 22%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 23%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 20%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 24%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 26%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 27%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 28%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 25%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 29%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 31%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 30%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 32%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 30%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 33%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 30%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 34%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - right;exists 36%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 37%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 38%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 destruct i as[|i]. { cbn[ref_pc_target_refs ref_pc_target_dependencies nth List.In]. intro Member.
 destruct Member as[<-|Member].
 - left;vm_compute;tauto.
 destruct Member as[<-|Member].
 - right;exists 35%nat;vm_compute;repeat split;try reflexivity;lia.
 destruct Member as[<-|Member].
 - right;exists 39%nat;vm_compute;repeat split;try reflexivity;lia.
 contradiction. }
 lia. Qed.
(* Shared batched history. *)
