Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalDeclaredConnectionCongruence FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants ScalarSinkTypes DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem reference_control_wire_24_congruent invalid left right next_left next_right :
 VM.find 1 left = VM.find 1 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 24 next_left = VM.find 24 next_right.
Proof. exact (declared_connection_congruence 1 flat_statements joint_update_connection_24_decl joint_update_connection_24_mid joint_update_connection_24_tail 24 1 1 invalid flat_memories left right next_left next_right joint_update_connection_24_position joint_update_connection_24_split joint_update_connection_24_straight joint_update_connection_24_mid_safe joint_update_connection_24_tail_safe joint_update_connection_24_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_24_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 24 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1 flat_statements joint_update_connection_24_decl joint_update_connection_24_mid joint_update_connection_24_tail 24 1 1 invalid flat_memories old current result joint_update_connection_24_position joint_update_connection_24_split joint_update_connection_24_straight joint_update_connection_24_mid_safe joint_update_connection_24_tail_safe joint_update_connection_24_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 1). split; [exact Value|]. exact (adapted_uint_result_type source 1 value Adapt).
Qed.
Definition reference_control_wire_1396_decl := match straight_drop 1476 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1396_mid := take_statements 7408 reference_control_wire_1396_decl.
Definition reference_control_wire_1396_tail := match straight_drop 8885 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1396_position : straight_drop 1475 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1396 (Gtyp (Fuint 32))) reference_control_wire_1396_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1396_split : reference_control_wire_1396_decl = statement_append reference_control_wire_1396_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1396) (@Eref VarOrder.T (@Eid VarOrder.T 7750))) reference_control_wire_1396_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1396_straight : straight_statements reference_control_wire_1396_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1396_mid_safe : formal_typed_suffix_safe flat_memories 1396 reference_control_wire_1396_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1396_tail_safe : formal_typed_suffix_safe flat_memories 1396 reference_control_wire_1396_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1396_nonregister : has_register 1396 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1396_congruent invalid left right next_left next_right :
 VM.find 7750 left = VM.find 7750 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1396 next_left = VM.find 1396 next_right.
Proof. exact (declared_connection_congruence 1475 flat_statements reference_control_wire_1396_decl reference_control_wire_1396_mid reference_control_wire_1396_tail 1396 7750 32 invalid flat_memories left right next_left next_right reference_control_wire_1396_position reference_control_wire_1396_split reference_control_wire_1396_straight reference_control_wire_1396_mid_safe reference_control_wire_1396_tail_safe reference_control_wire_1396_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1396_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1396 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1475 flat_statements reference_control_wire_1396_decl reference_control_wire_1396_mid reference_control_wire_1396_tail 1396 7750 32 invalid flat_memories old current result reference_control_wire_1396_position reference_control_wire_1396_split reference_control_wire_1396_straight reference_control_wire_1396_mid_safe reference_control_wire_1396_tail_safe reference_control_wire_1396_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1717_decl := match straight_drop 1797 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1717_mid := take_statements 6167 reference_control_wire_1717_decl.
Definition reference_control_wire_1717_tail := match straight_drop 7965 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1717_position : straight_drop 1796 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1717 (Gtyp (Fuint 32))) reference_control_wire_1717_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1717_split : reference_control_wire_1717_decl = statement_append reference_control_wire_1717_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1717) (@Eref VarOrder.T (@Eid VarOrder.T 7299))) reference_control_wire_1717_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1717_straight : straight_statements reference_control_wire_1717_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1717_mid_safe : formal_typed_suffix_safe flat_memories 1717 reference_control_wire_1717_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1717_tail_safe : formal_typed_suffix_safe flat_memories 1717 reference_control_wire_1717_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1717_nonregister : has_register 1717 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1717_congruent invalid left right next_left next_right :
 VM.find 7299 left = VM.find 7299 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1717 next_left = VM.find 1717 next_right.
Proof. exact (declared_connection_congruence 1796 flat_statements reference_control_wire_1717_decl reference_control_wire_1717_mid reference_control_wire_1717_tail 1717 7299 32 invalid flat_memories left right next_left next_right reference_control_wire_1717_position reference_control_wire_1717_split reference_control_wire_1717_straight reference_control_wire_1717_mid_safe reference_control_wire_1717_tail_safe reference_control_wire_1717_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1717_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1717 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1796 flat_statements reference_control_wire_1717_decl reference_control_wire_1717_mid reference_control_wire_1717_tail 1717 7299 32 invalid flat_memories old current result reference_control_wire_1717_position reference_control_wire_1717_split reference_control_wire_1717_straight reference_control_wire_1717_mid_safe reference_control_wire_1717_tail_safe reference_control_wire_1717_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1718_decl := match straight_drop 1798 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1718_mid := take_statements 6167 reference_control_wire_1718_decl.
Definition reference_control_wire_1718_tail := match straight_drop 7966 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1718_position : straight_drop 1797 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1718 (Gtyp (Fuint 32))) reference_control_wire_1718_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1718_split : reference_control_wire_1718_decl = statement_append reference_control_wire_1718_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1718) (@Eref VarOrder.T (@Eid VarOrder.T 7300))) reference_control_wire_1718_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1718_straight : straight_statements reference_control_wire_1718_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1718_mid_safe : formal_typed_suffix_safe flat_memories 1718 reference_control_wire_1718_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1718_tail_safe : formal_typed_suffix_safe flat_memories 1718 reference_control_wire_1718_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1718_nonregister : has_register 1718 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1718_congruent invalid left right next_left next_right :
 VM.find 7300 left = VM.find 7300 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1718 next_left = VM.find 1718 next_right.
Proof. exact (declared_connection_congruence 1797 flat_statements reference_control_wire_1718_decl reference_control_wire_1718_mid reference_control_wire_1718_tail 1718 7300 32 invalid flat_memories left right next_left next_right reference_control_wire_1718_position reference_control_wire_1718_split reference_control_wire_1718_straight reference_control_wire_1718_mid_safe reference_control_wire_1718_tail_safe reference_control_wire_1718_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1718_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1718 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1797 flat_statements reference_control_wire_1718_decl reference_control_wire_1718_mid reference_control_wire_1718_tail 1718 7300 32 invalid flat_memories old current result reference_control_wire_1718_position reference_control_wire_1718_split reference_control_wire_1718_straight reference_control_wire_1718_mid_safe reference_control_wire_1718_tail_safe reference_control_wire_1718_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1719_decl := match straight_drop 1799 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1719_mid := take_statements 6167 reference_control_wire_1719_decl.
Definition reference_control_wire_1719_tail := match straight_drop 7967 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1719_position : straight_drop 1798 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1719 (Gtyp (Fuint 32))) reference_control_wire_1719_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1719_split : reference_control_wire_1719_decl = statement_append reference_control_wire_1719_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1719) (@Eref VarOrder.T (@Eid VarOrder.T 7301))) reference_control_wire_1719_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1719_straight : straight_statements reference_control_wire_1719_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1719_mid_safe : formal_typed_suffix_safe flat_memories 1719 reference_control_wire_1719_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1719_tail_safe : formal_typed_suffix_safe flat_memories 1719 reference_control_wire_1719_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1719_nonregister : has_register 1719 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1719_congruent invalid left right next_left next_right :
 VM.find 7301 left = VM.find 7301 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1719 next_left = VM.find 1719 next_right.
Proof. exact (declared_connection_congruence 1798 flat_statements reference_control_wire_1719_decl reference_control_wire_1719_mid reference_control_wire_1719_tail 1719 7301 32 invalid flat_memories left right next_left next_right reference_control_wire_1719_position reference_control_wire_1719_split reference_control_wire_1719_straight reference_control_wire_1719_mid_safe reference_control_wire_1719_tail_safe reference_control_wire_1719_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1719_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1719 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1798 flat_statements reference_control_wire_1719_decl reference_control_wire_1719_mid reference_control_wire_1719_tail 1719 7301 32 invalid flat_memories old current result reference_control_wire_1719_position reference_control_wire_1719_split reference_control_wire_1719_straight reference_control_wire_1719_mid_safe reference_control_wire_1719_tail_safe reference_control_wire_1719_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1720_decl := match straight_drop 1800 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1720_mid := take_statements 6167 reference_control_wire_1720_decl.
Definition reference_control_wire_1720_tail := match straight_drop 7968 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1720_position : straight_drop 1799 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1720 (Gtyp (Fuint 32))) reference_control_wire_1720_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1720_split : reference_control_wire_1720_decl = statement_append reference_control_wire_1720_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1720) (@Eref VarOrder.T (@Eid VarOrder.T 7302))) reference_control_wire_1720_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1720_straight : straight_statements reference_control_wire_1720_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1720_mid_safe : formal_typed_suffix_safe flat_memories 1720 reference_control_wire_1720_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1720_tail_safe : formal_typed_suffix_safe flat_memories 1720 reference_control_wire_1720_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1720_nonregister : has_register 1720 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1720_congruent invalid left right next_left next_right :
 VM.find 7302 left = VM.find 7302 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1720 next_left = VM.find 1720 next_right.
Proof. exact (declared_connection_congruence 1799 flat_statements reference_control_wire_1720_decl reference_control_wire_1720_mid reference_control_wire_1720_tail 1720 7302 32 invalid flat_memories left right next_left next_right reference_control_wire_1720_position reference_control_wire_1720_split reference_control_wire_1720_straight reference_control_wire_1720_mid_safe reference_control_wire_1720_tail_safe reference_control_wire_1720_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1720_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1720 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1799 flat_statements reference_control_wire_1720_decl reference_control_wire_1720_mid reference_control_wire_1720_tail 1720 7302 32 invalid flat_memories old current result reference_control_wire_1720_position reference_control_wire_1720_split reference_control_wire_1720_straight reference_control_wire_1720_mid_safe reference_control_wire_1720_tail_safe reference_control_wire_1720_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1721_decl := match straight_drop 1801 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1721_mid := take_statements 6167 reference_control_wire_1721_decl.
Definition reference_control_wire_1721_tail := match straight_drop 7969 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1721_position : straight_drop 1800 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1721 (Gtyp (Fuint 32))) reference_control_wire_1721_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1721_split : reference_control_wire_1721_decl = statement_append reference_control_wire_1721_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1721) (@Eref VarOrder.T (@Eid VarOrder.T 7303))) reference_control_wire_1721_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1721_straight : straight_statements reference_control_wire_1721_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1721_mid_safe : formal_typed_suffix_safe flat_memories 1721 reference_control_wire_1721_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1721_tail_safe : formal_typed_suffix_safe flat_memories 1721 reference_control_wire_1721_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1721_nonregister : has_register 1721 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1721_congruent invalid left right next_left next_right :
 VM.find 7303 left = VM.find 7303 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1721 next_left = VM.find 1721 next_right.
Proof. exact (declared_connection_congruence 1800 flat_statements reference_control_wire_1721_decl reference_control_wire_1721_mid reference_control_wire_1721_tail 1721 7303 32 invalid flat_memories left right next_left next_right reference_control_wire_1721_position reference_control_wire_1721_split reference_control_wire_1721_straight reference_control_wire_1721_mid_safe reference_control_wire_1721_tail_safe reference_control_wire_1721_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1721_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1721 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1800 flat_statements reference_control_wire_1721_decl reference_control_wire_1721_mid reference_control_wire_1721_tail 1721 7303 32 invalid flat_memories old current result reference_control_wire_1721_position reference_control_wire_1721_split reference_control_wire_1721_straight reference_control_wire_1721_mid_safe reference_control_wire_1721_tail_safe reference_control_wire_1721_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1722_decl := match straight_drop 1802 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1722_mid := take_statements 6167 reference_control_wire_1722_decl.
Definition reference_control_wire_1722_tail := match straight_drop 7970 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1722_position : straight_drop 1801 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1722 (Gtyp (Fuint 32))) reference_control_wire_1722_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1722_split : reference_control_wire_1722_decl = statement_append reference_control_wire_1722_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1722) (@Eref VarOrder.T (@Eid VarOrder.T 7304))) reference_control_wire_1722_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1722_straight : straight_statements reference_control_wire_1722_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1722_mid_safe : formal_typed_suffix_safe flat_memories 1722 reference_control_wire_1722_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1722_tail_safe : formal_typed_suffix_safe flat_memories 1722 reference_control_wire_1722_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1722_nonregister : has_register 1722 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1722_congruent invalid left right next_left next_right :
 VM.find 7304 left = VM.find 7304 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1722 next_left = VM.find 1722 next_right.
Proof. exact (declared_connection_congruence 1801 flat_statements reference_control_wire_1722_decl reference_control_wire_1722_mid reference_control_wire_1722_tail 1722 7304 32 invalid flat_memories left right next_left next_right reference_control_wire_1722_position reference_control_wire_1722_split reference_control_wire_1722_straight reference_control_wire_1722_mid_safe reference_control_wire_1722_tail_safe reference_control_wire_1722_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1722_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1722 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1801 flat_statements reference_control_wire_1722_decl reference_control_wire_1722_mid reference_control_wire_1722_tail 1722 7304 32 invalid flat_memories old current result reference_control_wire_1722_position reference_control_wire_1722_split reference_control_wire_1722_straight reference_control_wire_1722_mid_safe reference_control_wire_1722_tail_safe reference_control_wire_1722_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1723_decl := match straight_drop 1803 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1723_mid := take_statements 6167 reference_control_wire_1723_decl.
Definition reference_control_wire_1723_tail := match straight_drop 7971 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1723_position : straight_drop 1802 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1723 (Gtyp (Fuint 32))) reference_control_wire_1723_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1723_split : reference_control_wire_1723_decl = statement_append reference_control_wire_1723_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1723) (@Eref VarOrder.T (@Eid VarOrder.T 7305))) reference_control_wire_1723_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1723_straight : straight_statements reference_control_wire_1723_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1723_mid_safe : formal_typed_suffix_safe flat_memories 1723 reference_control_wire_1723_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1723_tail_safe : formal_typed_suffix_safe flat_memories 1723 reference_control_wire_1723_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1723_nonregister : has_register 1723 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1723_congruent invalid left right next_left next_right :
 VM.find 7305 left = VM.find 7305 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1723 next_left = VM.find 1723 next_right.
Proof. exact (declared_connection_congruence 1802 flat_statements reference_control_wire_1723_decl reference_control_wire_1723_mid reference_control_wire_1723_tail 1723 7305 32 invalid flat_memories left right next_left next_right reference_control_wire_1723_position reference_control_wire_1723_split reference_control_wire_1723_straight reference_control_wire_1723_mid_safe reference_control_wire_1723_tail_safe reference_control_wire_1723_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1723_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1723 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1802 flat_statements reference_control_wire_1723_decl reference_control_wire_1723_mid reference_control_wire_1723_tail 1723 7305 32 invalid flat_memories old current result reference_control_wire_1723_position reference_control_wire_1723_split reference_control_wire_1723_straight reference_control_wire_1723_mid_safe reference_control_wire_1723_tail_safe reference_control_wire_1723_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1724_decl := match straight_drop 1804 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1724_mid := take_statements 6167 reference_control_wire_1724_decl.
Definition reference_control_wire_1724_tail := match straight_drop 7972 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1724_position : straight_drop 1803 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1724 (Gtyp (Fuint 32))) reference_control_wire_1724_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1724_split : reference_control_wire_1724_decl = statement_append reference_control_wire_1724_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1724) (@Eref VarOrder.T (@Eid VarOrder.T 7306))) reference_control_wire_1724_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1724_straight : straight_statements reference_control_wire_1724_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1724_mid_safe : formal_typed_suffix_safe flat_memories 1724 reference_control_wire_1724_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1724_tail_safe : formal_typed_suffix_safe flat_memories 1724 reference_control_wire_1724_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1724_nonregister : has_register 1724 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1724_congruent invalid left right next_left next_right :
 VM.find 7306 left = VM.find 7306 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1724 next_left = VM.find 1724 next_right.
Proof. exact (declared_connection_congruence 1803 flat_statements reference_control_wire_1724_decl reference_control_wire_1724_mid reference_control_wire_1724_tail 1724 7306 32 invalid flat_memories left right next_left next_right reference_control_wire_1724_position reference_control_wire_1724_split reference_control_wire_1724_straight reference_control_wire_1724_mid_safe reference_control_wire_1724_tail_safe reference_control_wire_1724_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1724_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1724 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1803 flat_statements reference_control_wire_1724_decl reference_control_wire_1724_mid reference_control_wire_1724_tail 1724 7306 32 invalid flat_memories old current result reference_control_wire_1724_position reference_control_wire_1724_split reference_control_wire_1724_straight reference_control_wire_1724_mid_safe reference_control_wire_1724_tail_safe reference_control_wire_1724_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1725_decl := match straight_drop 1805 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1725_mid := take_statements 6167 reference_control_wire_1725_decl.
Definition reference_control_wire_1725_tail := match straight_drop 7973 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1725_position : straight_drop 1804 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1725 (Gtyp (Fuint 32))) reference_control_wire_1725_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1725_split : reference_control_wire_1725_decl = statement_append reference_control_wire_1725_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1725) (@Eref VarOrder.T (@Eid VarOrder.T 7307))) reference_control_wire_1725_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1725_straight : straight_statements reference_control_wire_1725_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1725_mid_safe : formal_typed_suffix_safe flat_memories 1725 reference_control_wire_1725_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1725_tail_safe : formal_typed_suffix_safe flat_memories 1725 reference_control_wire_1725_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1725_nonregister : has_register 1725 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1725_congruent invalid left right next_left next_right :
 VM.find 7307 left = VM.find 7307 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1725 next_left = VM.find 1725 next_right.
Proof. exact (declared_connection_congruence 1804 flat_statements reference_control_wire_1725_decl reference_control_wire_1725_mid reference_control_wire_1725_tail 1725 7307 32 invalid flat_memories left right next_left next_right reference_control_wire_1725_position reference_control_wire_1725_split reference_control_wire_1725_straight reference_control_wire_1725_mid_safe reference_control_wire_1725_tail_safe reference_control_wire_1725_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1725_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1725 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1804 flat_statements reference_control_wire_1725_decl reference_control_wire_1725_mid reference_control_wire_1725_tail 1725 7307 32 invalid flat_memories old current result reference_control_wire_1725_position reference_control_wire_1725_split reference_control_wire_1725_straight reference_control_wire_1725_mid_safe reference_control_wire_1725_tail_safe reference_control_wire_1725_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1726_decl := match straight_drop 1806 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1726_mid := take_statements 6167 reference_control_wire_1726_decl.
Definition reference_control_wire_1726_tail := match straight_drop 7974 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1726_position : straight_drop 1805 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1726 (Gtyp (Fuint 32))) reference_control_wire_1726_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1726_split : reference_control_wire_1726_decl = statement_append reference_control_wire_1726_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1726) (@Eref VarOrder.T (@Eid VarOrder.T 7308))) reference_control_wire_1726_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1726_straight : straight_statements reference_control_wire_1726_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1726_mid_safe : formal_typed_suffix_safe flat_memories 1726 reference_control_wire_1726_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1726_tail_safe : formal_typed_suffix_safe flat_memories 1726 reference_control_wire_1726_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1726_nonregister : has_register 1726 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1726_congruent invalid left right next_left next_right :
 VM.find 7308 left = VM.find 7308 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1726 next_left = VM.find 1726 next_right.
Proof. exact (declared_connection_congruence 1805 flat_statements reference_control_wire_1726_decl reference_control_wire_1726_mid reference_control_wire_1726_tail 1726 7308 32 invalid flat_memories left right next_left next_right reference_control_wire_1726_position reference_control_wire_1726_split reference_control_wire_1726_straight reference_control_wire_1726_mid_safe reference_control_wire_1726_tail_safe reference_control_wire_1726_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1726_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1726 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1805 flat_statements reference_control_wire_1726_decl reference_control_wire_1726_mid reference_control_wire_1726_tail 1726 7308 32 invalid flat_memories old current result reference_control_wire_1726_position reference_control_wire_1726_split reference_control_wire_1726_straight reference_control_wire_1726_mid_safe reference_control_wire_1726_tail_safe reference_control_wire_1726_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
