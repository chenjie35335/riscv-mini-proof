Require Import CoreSocModel StagedFlatCircuitIteration StagedFlatObservation FormalAssertionDischarge AssertionInstances ComparisonTruth.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths Firrtl_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top flat_statements flat_memories.
Theorem observed_assertion_0_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7567))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1474 1519) ->
 generated_assert_m0_0_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_0_at_top states)). rewrite State.
 apply (assertion_0_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_1_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7569))) (@Eref VarOrder.T (@Eid VarOrder.T 7572))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1475 1520) ->
 generated_assert_m0_1_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_1_at_top states)). rewrite State.
 apply (assertion_1_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_2_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7569))) (@Eref VarOrder.T (@Eid VarOrder.T 7576))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1476 1521) ->
 generated_assert_m0_2_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_2_at_top states)). rewrite State.
 apply (assertion_2_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_3_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7580))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1478 1523) ->
 generated_assert_m0_3_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_3_at_top states)). rewrite State.
 apply (assertion_3_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_4_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7582))) (@Eref VarOrder.T (@Eid VarOrder.T 7585))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1479 1524) ->
 generated_assert_m0_4_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_4_at_top states)). rewrite State.
 apply (assertion_4_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_5_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7582))) (@Eref VarOrder.T (@Eid VarOrder.T 7589))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1481 1526) ->
 generated_assert_m0_5_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_5_at_top states)). rewrite State.
 apply (assertion_5_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_6_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7582))) (@Eref VarOrder.T (@Eid VarOrder.T 7593))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1480 1525) ->
 generated_assert_m0_6_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_6_at_top states)). rewrite State.
 apply (assertion_6_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_7_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7597))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1397 1559) ->
 generated_assert_m0_7_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_7_at_top states)). rewrite State.
 apply (assertion_7_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_8_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7601))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1399 1597) ->
 generated_assert_m0_8_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_8_at_top states)). rewrite State.
 apply (assertion_8_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_9_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7605))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1400 1598) ->
 generated_assert_m0_9_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_9_at_top states)). rewrite State.
 apply (assertion_9_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_10_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7609))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1401 1599) ->
 generated_assert_m0_10_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_10_at_top states)). rewrite State.
 apply (assertion_10_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_11_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7613))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1402 1600) ->
 generated_assert_m0_11_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_11_at_top states)). rewrite State.
 apply (assertion_11_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_12_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7617))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1403 1601) ->
 generated_assert_m0_12_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_12_at_top states)). rewrite State.
 apply (assertion_12_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_13_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7621))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1404 1602) ->
 generated_assert_m0_13_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_13_at_top states)). rewrite State.
 apply (assertion_13_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_14_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7625))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1405 1603) ->
 generated_assert_m0_14_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_14_at_top states)). rewrite State.
 apply (assertion_14_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_15_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7629))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1406 1604) ->
 generated_assert_m0_15_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_15_at_top states)). rewrite State.
 apply (assertion_15_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_16_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7633))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1407 1605) ->
 generated_assert_m0_16_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_16_at_top states)). rewrite State.
 apply (assertion_16_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_17_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7637))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1408 1606) ->
 generated_assert_m0_17_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_17_at_top states)). rewrite State.
 apply (assertion_17_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_18_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7641))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1409 1607) ->
 generated_assert_m0_18_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_18_at_top states)). rewrite State.
 apply (assertion_18_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_19_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7645))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1410 1608) ->
 generated_assert_m0_19_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_19_at_top states)). rewrite State.
 apply (assertion_19_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_20_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7649))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1411 1609) ->
 generated_assert_m0_20_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_20_at_top states)). rewrite State.
 apply (assertion_20_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_21_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7653))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1412 1610) ->
 generated_assert_m0_21_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_21_at_top states)). rewrite State.
 apply (assertion_21_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_22_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7657))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1413 1611) ->
 generated_assert_m0_22_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_22_at_top states)). rewrite State.
 apply (assertion_22_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_23_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7661))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1414 1612) ->
 generated_assert_m0_23_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_23_at_top states)). rewrite State.
 apply (assertion_23_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_24_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7665))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1415 1613) ->
 generated_assert_m0_24_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_24_at_top states)). rewrite State.
 apply (assertion_24_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_25_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7669))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1416 1614) ->
 generated_assert_m0_25_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_25_at_top states)). rewrite State.
 apply (assertion_25_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_26_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7673))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1417 1615) ->
 generated_assert_m0_26_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_26_at_top states)). rewrite State.
 apply (assertion_26_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_27_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7677))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1418 1616) ->
 generated_assert_m0_27_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_27_at_top states)). rewrite State.
 apply (assertion_27_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_28_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7681))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1419 1617) ->
 generated_assert_m0_28_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_28_at_top states)). rewrite State.
 apply (assertion_28_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_29_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7685))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1420 1618) ->
 generated_assert_m0_29_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_29_at_top states)). rewrite State.
 apply (assertion_29_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_30_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7689))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1421 1619) ->
 generated_assert_m0_30_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_30_at_top states)). rewrite State.
 apply (assertion_30_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_31_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7693))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1422 1620) ->
 generated_assert_m0_31_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_31_at_top states)). rewrite State.
 apply (assertion_31_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_32_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7697))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1423 1621) ->
 generated_assert_m0_32_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_32_at_top states)). rewrite State.
 apply (assertion_32_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_33_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7701))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1424 1622) ->
 generated_assert_m0_33_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_33_at_top states)). rewrite State.
 apply (assertion_33_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_34_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7705))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1425 1623) ->
 generated_assert_m0_34_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_34_at_top states)). rewrite State.
 apply (assertion_34_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_35_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7709))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1426 1624) ->
 generated_assert_m0_35_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_35_at_top states)). rewrite State.
 apply (assertion_35_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_36_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7713))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1427 1625) ->
 generated_assert_m0_36_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_36_at_top states)). rewrite State.
 apply (assertion_36_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_37_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7717))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1428 1626) ->
 generated_assert_m0_37_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_37_at_top states)). rewrite State.
 apply (assertion_37_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_38_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7721))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1429 1627) ->
 generated_assert_m0_38_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_38_at_top states)). rewrite State.
 apply (assertion_38_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_39_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) (@Eref VarOrder.T (@Eid VarOrder.T 7725))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1430 1628) ->
 generated_assert_m0_39_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_39_at_top states)). rewrite State.
 apply (assertion_39_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_40_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7730))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1469 1667) ->
 generated_assert_m0_40_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_40_at_top states)). rewrite State.
 apply (assertion_40_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_41_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7734))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1470 1668) ->
 generated_assert_m0_41_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_41_at_top states)). rewrite State.
 apply (assertion_41_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_42_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7738))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1471 1669) ->
 generated_assert_m0_42_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_42_at_top states)). rewrite State.
 apply (assertion_42_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_43_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7742))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1472 1670) ->
 generated_assert_m0_43_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_43_at_top states)). rewrite State.
 apply (assertion_43_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Theorem observed_assertion_44_from_agreement memory inputs k states :
 generated_observe memory inputs k = Some states ->
 (forall committed initial previous old next,
 generated_run memory inputs k = Some committed ->
 circuit_initial_map_with_memory generated_modules generated_top (Some committed)
   (formal_external_inputs (generated_observation_input inputs k)) = Some initial ->
 circuit_formal_iterations generated_modules generated_top (generated_observation_input inputs k) 9258 initial = Some previous ->
 SVM.find nil previous = Some old ->
 formal_value_iter (formal_invalid_policy (generated_observation_input inputs k) nil) flat_memories old false old flat_statements = Some next ->
 SVM.find nil states = Some next ->
 generated_expr_true (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Eprim_binop VarOrder.T Band (@Econst VarOrder.T (Fuint 1) [::true]) (@Eref VarOrder.T (@Eid VarOrder.T 7727))) (@Eref VarOrder.T (@Eid VarOrder.T 7746))) (@Econst VarOrder.T (Fuint 1) [::true])) next -> comparison_inputs_agree old 1473 1671) ->
 generated_assert_m0_44_all states.
Proof.
 intros Observe Agree.
 destruct (observed_last_iteration memory inputs k states Observe)
 as [committed [initial [previous [old [next [Run [Prepare [Prefix [Old [Step State]]]]]]]]]].
 apply (proj2 (assertion_44_at_top states)). rewrite State.
 apply (assertion_44_from_enabled_agreement _ old old next Step).
 exact (Agree committed initial previous old next Run Prepare Prefix Old Step State).
Qed.
Print Assumptions observed_assertion_44_from_agreement.
