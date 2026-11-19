Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalDeclaredConnectionCongruence FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants ScalarSinkTypes DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_control_wire_1786_decl := match straight_drop 1866 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1786_mid := take_statements 6167 reference_control_wire_1786_decl.
Definition reference_control_wire_1786_tail := match straight_drop 8034 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1786_position : straight_drop 1865 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1786 (Gtyp (Fuint 2))) reference_control_wire_1786_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1786_split : reference_control_wire_1786_decl = statement_append reference_control_wire_1786_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1786) (@Eref VarOrder.T (@Eid VarOrder.T 7368))) reference_control_wire_1786_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1786_straight : straight_statements reference_control_wire_1786_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1786_mid_safe : formal_typed_suffix_safe flat_memories 1786 reference_control_wire_1786_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1786_tail_safe : formal_typed_suffix_safe flat_memories 1786 reference_control_wire_1786_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1786_nonregister : has_register 1786 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1786_congruent invalid left right next_left next_right :
 VM.find 7368 left = VM.find 7368 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1786 next_left = VM.find 1786 next_right.
Proof. exact (declared_connection_congruence 1865 flat_statements reference_control_wire_1786_decl reference_control_wire_1786_mid reference_control_wire_1786_tail 1786 7368 2 invalid flat_memories left right next_left next_right reference_control_wire_1786_position reference_control_wire_1786_split reference_control_wire_1786_straight reference_control_wire_1786_mid_safe reference_control_wire_1786_tail_safe reference_control_wire_1786_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1786_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1786 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1865 flat_statements reference_control_wire_1786_decl reference_control_wire_1786_mid reference_control_wire_1786_tail 1786 7368 2 invalid flat_memories old current result reference_control_wire_1786_position reference_control_wire_1786_split reference_control_wire_1786_straight reference_control_wire_1786_mid_safe reference_control_wire_1786_tail_safe reference_control_wire_1786_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 2). split; [exact Value|]. exact (adapted_uint_result_type source 2 value Adapt).
Qed.
Theorem reference_control_wire_65_congruent invalid left right next_left next_right :
 VM.find 24 left = VM.find 24 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 65 next_left = VM.find 65 next_right.
Proof. exact (declared_connection_congruence 42 flat_statements joint_update_connection_65_decl joint_update_connection_65_mid joint_update_connection_65_tail 65 24 1 invalid flat_memories left right next_left next_right joint_update_connection_65_position joint_update_connection_65_split joint_update_connection_65_straight joint_update_connection_65_mid_safe joint_update_connection_65_tail_safe joint_update_connection_65_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_65_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 65 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 42 flat_statements joint_update_connection_65_decl joint_update_connection_65_mid joint_update_connection_65_tail 65 24 1 invalid flat_memories old current result joint_update_connection_65_position joint_update_connection_65_split joint_update_connection_65_straight joint_update_connection_65_mid_safe joint_update_connection_65_tail_safe joint_update_connection_65_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Definition reference_control_wire_1516_decl := match straight_drop 1596 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1516_mid := take_statements 6623 reference_control_wire_1516_decl.
Definition reference_control_wire_1516_tail := match straight_drop 8220 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1516_position : straight_drop 1595 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1516 (Gtyp (Fuint 32))) reference_control_wire_1516_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1516_split : reference_control_wire_1516_decl = statement_append reference_control_wire_1516_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1516) (@Eref VarOrder.T (@Eid VarOrder.T 1396))) reference_control_wire_1516_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1516_straight : straight_statements reference_control_wire_1516_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1516_mid_safe : formal_typed_suffix_safe flat_memories 1516 reference_control_wire_1516_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1516_tail_safe : formal_typed_suffix_safe flat_memories 1516 reference_control_wire_1516_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1516_nonregister : has_register 1516 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1516_congruent invalid left right next_left next_right :
 VM.find 1396 left = VM.find 1396 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1516 next_left = VM.find 1516 next_right.
Proof. exact (declared_connection_congruence 1595 flat_statements reference_control_wire_1516_decl reference_control_wire_1516_mid reference_control_wire_1516_tail 1516 1396 32 invalid flat_memories left right next_left next_right reference_control_wire_1516_position reference_control_wire_1516_split reference_control_wire_1516_straight reference_control_wire_1516_mid_safe reference_control_wire_1516_tail_safe reference_control_wire_1516_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1516_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1516 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1595 flat_statements reference_control_wire_1516_decl reference_control_wire_1516_mid reference_control_wire_1516_tail 1516 1396 32 invalid flat_memories old current result reference_control_wire_1516_position reference_control_wire_1516_split reference_control_wire_1516_straight reference_control_wire_1516_mid_safe reference_control_wire_1516_tail_safe reference_control_wire_1516_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Theorem reference_control_wire_33_congruent invalid left right next_left next_right :
 VM.find 9216 left = VM.find 9216 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 33 next_left = VM.find 33 next_right.
Proof. exact (declared_connection_congruence 10 flat_statements data_address_connection_33_decl data_address_connection_33_mid data_address_connection_33_tail 33 9216 1 invalid flat_memories left right next_left next_right data_address_connection_33_position data_address_connection_33_split data_address_connection_33_straight data_address_connection_33_mid_safe data_address_connection_33_tail_safe data_address_connection_33_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_33_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 33 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 10 flat_statements data_address_connection_33_decl data_address_connection_33_mid data_address_connection_33_tail 33 9216 1 invalid flat_memories old current result data_address_connection_33_position data_address_connection_33_split data_address_connection_33_straight data_address_connection_33_mid_safe data_address_connection_33_tail_safe data_address_connection_33_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Theorem reference_control_wire_40_congruent invalid left right next_left next_right :
 VM.find 9218 left = VM.find 9218 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 40 next_left = VM.find 40 next_right.
Proof. exact (declared_connection_congruence 17 flat_statements data_address_connection_40_decl data_address_connection_40_mid data_address_connection_40_tail 40 9218 1 invalid flat_memories left right next_left next_right data_address_connection_40_position data_address_connection_40_split data_address_connection_40_straight data_address_connection_40_mid_safe data_address_connection_40_tail_safe data_address_connection_40_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_40_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 40 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 17 flat_statements data_address_connection_40_decl data_address_connection_40_mid data_address_connection_40_tail 40 9218 1 invalid flat_memories old current result data_address_connection_40_position data_address_connection_40_split data_address_connection_40_straight data_address_connection_40_mid_safe data_address_connection_40_tail_safe data_address_connection_40_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Definition reference_control_wire_1706_decl := match straight_drop 1786 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1706_mid := take_statements 6175 reference_control_wire_1706_decl.
Definition reference_control_wire_1706_tail := match straight_drop 7962 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1706_position : straight_drop 1785 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1706 (Gtyp (Fuint 32))) reference_control_wire_1706_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1706_split : reference_control_wire_1706_decl = statement_append reference_control_wire_1706_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1706) (@Eref VarOrder.T (@Eid VarOrder.T 1516))) reference_control_wire_1706_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1706_straight : straight_statements reference_control_wire_1706_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1706_mid_safe : formal_typed_suffix_safe flat_memories 1706 reference_control_wire_1706_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1706_tail_safe : formal_typed_suffix_safe flat_memories 1706 reference_control_wire_1706_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1706_nonregister : has_register 1706 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1706_congruent invalid left right next_left next_right :
 VM.find 1516 left = VM.find 1516 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1706 next_left = VM.find 1706 next_right.
Proof. exact (declared_connection_congruence 1785 flat_statements reference_control_wire_1706_decl reference_control_wire_1706_mid reference_control_wire_1706_tail 1706 1516 32 invalid flat_memories left right next_left next_right reference_control_wire_1706_position reference_control_wire_1706_split reference_control_wire_1706_straight reference_control_wire_1706_mid_safe reference_control_wire_1706_tail_safe reference_control_wire_1706_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1706_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1706 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1785 flat_statements reference_control_wire_1706_decl reference_control_wire_1706_mid reference_control_wire_1706_tail 1706 1516 32 invalid flat_memories old current result reference_control_wire_1706_position reference_control_wire_1706_split reference_control_wire_1706_straight reference_control_wire_1706_mid_safe reference_control_wire_1706_tail_safe reference_control_wire_1706_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Theorem reference_control_wire_74_congruent invalid left right next_left next_right :
 VM.find 33 left = VM.find 33 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 74 next_left = VM.find 74 next_right.
Proof. exact (declared_connection_congruence 51 flat_statements data_address_connection_74_decl data_address_connection_74_mid data_address_connection_74_tail 74 33 1 invalid flat_memories left right next_left next_right data_address_connection_74_position data_address_connection_74_split data_address_connection_74_straight data_address_connection_74_mid_safe data_address_connection_74_tail_safe data_address_connection_74_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_74_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 74 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 51 flat_statements data_address_connection_74_decl data_address_connection_74_mid data_address_connection_74_tail 74 33 1 invalid flat_memories old current result data_address_connection_74_position data_address_connection_74_split data_address_connection_74_straight data_address_connection_74_mid_safe data_address_connection_74_tail_safe data_address_connection_74_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Theorem reference_control_wire_81_congruent invalid left right next_left next_right :
 VM.find 40 left = VM.find 40 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 81 next_left = VM.find 81 next_right.
Proof. exact (declared_connection_congruence 58 flat_statements data_address_connection_81_decl data_address_connection_81_mid data_address_connection_81_tail 81 40 1 invalid flat_memories left right next_left next_right data_address_connection_81_position data_address_connection_81_split data_address_connection_81_straight data_address_connection_81_mid_safe data_address_connection_81_tail_safe data_address_connection_81_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_81_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 81 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 58 flat_statements data_address_connection_81_decl data_address_connection_81_mid data_address_connection_81_tail 81 40 1 invalid flat_memories old current result data_address_connection_81_position data_address_connection_81_split data_address_connection_81_straight data_address_connection_81_mid_safe data_address_connection_81_tail_safe data_address_connection_81_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Definition reference_control_wire_1395_decl := match straight_drop 1475 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1395_mid := take_statements 7408 reference_control_wire_1395_decl.
Definition reference_control_wire_1395_tail := match straight_drop 8884 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1395_position : straight_drop 1474 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1395 (Gtyp (Fuint 1))) reference_control_wire_1395_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1395_split : reference_control_wire_1395_decl = statement_append reference_control_wire_1395_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1395) (@Eref VarOrder.T (@Eid VarOrder.T 7956))) reference_control_wire_1395_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1395_straight : straight_statements reference_control_wire_1395_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1395_mid_safe : formal_typed_suffix_safe flat_memories 1395 reference_control_wire_1395_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1395_tail_safe : formal_typed_suffix_safe flat_memories 1395 reference_control_wire_1395_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1395_nonregister : has_register 1395 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1395_congruent invalid left right next_left next_right :
 VM.find 7956 left = VM.find 7956 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1395 next_left = VM.find 1395 next_right.
Proof. exact (declared_connection_congruence 1474 flat_statements reference_control_wire_1395_decl reference_control_wire_1395_mid reference_control_wire_1395_tail 1395 7956 1 invalid flat_memories left right next_left next_right reference_control_wire_1395_position reference_control_wire_1395_split reference_control_wire_1395_straight reference_control_wire_1395_mid_safe reference_control_wire_1395_tail_safe reference_control_wire_1395_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1395_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1395 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1474 flat_statements reference_control_wire_1395_decl reference_control_wire_1395_mid reference_control_wire_1395_tail 1395 7956 1 invalid flat_memories old current result reference_control_wire_1395_position reference_control_wire_1395_split reference_control_wire_1395_straight reference_control_wire_1395_mid_safe reference_control_wire_1395_tail_safe reference_control_wire_1395_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Definition reference_control_wire_1517_decl := match straight_drop 1597 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1517_mid := take_statements 6623 reference_control_wire_1517_decl.
Definition reference_control_wire_1517_tail := match straight_drop 8221 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1517_position : straight_drop 1596 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1517 (Gtyp (Fuint 1))) reference_control_wire_1517_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1517_split : reference_control_wire_1517_decl = statement_append reference_control_wire_1517_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1517) (@Eref VarOrder.T (@Eid VarOrder.T 1395))) reference_control_wire_1517_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1517_straight : straight_statements reference_control_wire_1517_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1517_mid_safe : formal_typed_suffix_safe flat_memories 1517 reference_control_wire_1517_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1517_tail_safe : formal_typed_suffix_safe flat_memories 1517 reference_control_wire_1517_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1517_nonregister : has_register 1517 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1517_congruent invalid left right next_left next_right :
 VM.find 1395 left = VM.find 1395 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1517 next_left = VM.find 1517 next_right.
Proof. exact (declared_connection_congruence 1596 flat_statements reference_control_wire_1517_decl reference_control_wire_1517_mid reference_control_wire_1517_tail 1517 1395 1 invalid flat_memories left right next_left next_right reference_control_wire_1517_position reference_control_wire_1517_split reference_control_wire_1517_straight reference_control_wire_1517_mid_safe reference_control_wire_1517_tail_safe reference_control_wire_1517_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1517_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1517 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1596 flat_statements reference_control_wire_1517_decl reference_control_wire_1517_mid reference_control_wire_1517_tail 1517 1395 1 invalid flat_memories old current result reference_control_wire_1517_position reference_control_wire_1517_split reference_control_wire_1517_straight reference_control_wire_1517_mid_safe reference_control_wire_1517_tail_safe reference_control_wire_1517_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Definition reference_control_wire_1707_decl := match straight_drop 1787 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1707_mid := take_statements 6175 reference_control_wire_1707_decl.
Definition reference_control_wire_1707_tail := match straight_drop 7963 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1707_position : straight_drop 1786 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1707 (Gtyp (Fuint 1))) reference_control_wire_1707_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1707_split : reference_control_wire_1707_decl = statement_append reference_control_wire_1707_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1707) (@Eref VarOrder.T (@Eid VarOrder.T 1517))) reference_control_wire_1707_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1707_straight : straight_statements reference_control_wire_1707_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1707_mid_safe : formal_typed_suffix_safe flat_memories 1707 reference_control_wire_1707_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1707_tail_safe : formal_typed_suffix_safe flat_memories 1707 reference_control_wire_1707_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1707_nonregister : has_register 1707 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1707_congruent invalid left right next_left next_right :
 VM.find 1517 left = VM.find 1517 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1707 next_left = VM.find 1707 next_right.
Proof. exact (declared_connection_congruence 1786 flat_statements reference_control_wire_1707_decl reference_control_wire_1707_mid reference_control_wire_1707_tail 1707 1517 1 invalid flat_memories left right next_left next_right reference_control_wire_1707_position reference_control_wire_1707_split reference_control_wire_1707_straight reference_control_wire_1707_mid_safe reference_control_wire_1707_tail_safe reference_control_wire_1707_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1707_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1707 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1786 flat_statements reference_control_wire_1707_decl reference_control_wire_1707_mid reference_control_wire_1707_tail 1707 1517 1 invalid flat_memories old current result reference_control_wire_1707_position reference_control_wire_1707_split reference_control_wire_1707_straight reference_control_wire_1707_mid_safe reference_control_wire_1707_tail_safe reference_control_wire_1707_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
