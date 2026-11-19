Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalDeclaredConnectionCongruence FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants ScalarSinkTypes DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_control_wire_1727_decl := match straight_drop 1807 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1727_mid := take_statements 6167 reference_control_wire_1727_decl.
Definition reference_control_wire_1727_tail := match straight_drop 7975 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1727_position : straight_drop 1806 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1727 (Gtyp (Fuint 32))) reference_control_wire_1727_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1727_split : reference_control_wire_1727_decl = statement_append reference_control_wire_1727_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1727) (@Eref VarOrder.T (@Eid VarOrder.T 7309))) reference_control_wire_1727_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1727_straight : straight_statements reference_control_wire_1727_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1727_mid_safe : formal_typed_suffix_safe flat_memories 1727 reference_control_wire_1727_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1727_tail_safe : formal_typed_suffix_safe flat_memories 1727 reference_control_wire_1727_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1727_nonregister : has_register 1727 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1727_congruent invalid left right next_left next_right :
 VM.find 7309 left = VM.find 7309 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1727 next_left = VM.find 1727 next_right.
Proof. exact (declared_connection_congruence 1806 flat_statements reference_control_wire_1727_decl reference_control_wire_1727_mid reference_control_wire_1727_tail 1727 7309 32 invalid flat_memories left right next_left next_right reference_control_wire_1727_position reference_control_wire_1727_split reference_control_wire_1727_straight reference_control_wire_1727_mid_safe reference_control_wire_1727_tail_safe reference_control_wire_1727_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1727_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1727 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1806 flat_statements reference_control_wire_1727_decl reference_control_wire_1727_mid reference_control_wire_1727_tail 1727 7309 32 invalid flat_memories old current result reference_control_wire_1727_position reference_control_wire_1727_split reference_control_wire_1727_straight reference_control_wire_1727_mid_safe reference_control_wire_1727_tail_safe reference_control_wire_1727_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1728_decl := match straight_drop 1808 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1728_mid := take_statements 6167 reference_control_wire_1728_decl.
Definition reference_control_wire_1728_tail := match straight_drop 7976 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1728_position : straight_drop 1807 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1728 (Gtyp (Fuint 32))) reference_control_wire_1728_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1728_split : reference_control_wire_1728_decl = statement_append reference_control_wire_1728_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1728) (@Eref VarOrder.T (@Eid VarOrder.T 7310))) reference_control_wire_1728_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1728_straight : straight_statements reference_control_wire_1728_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1728_mid_safe : formal_typed_suffix_safe flat_memories 1728 reference_control_wire_1728_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1728_tail_safe : formal_typed_suffix_safe flat_memories 1728 reference_control_wire_1728_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1728_nonregister : has_register 1728 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1728_congruent invalid left right next_left next_right :
 VM.find 7310 left = VM.find 7310 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1728 next_left = VM.find 1728 next_right.
Proof. exact (declared_connection_congruence 1807 flat_statements reference_control_wire_1728_decl reference_control_wire_1728_mid reference_control_wire_1728_tail 1728 7310 32 invalid flat_memories left right next_left next_right reference_control_wire_1728_position reference_control_wire_1728_split reference_control_wire_1728_straight reference_control_wire_1728_mid_safe reference_control_wire_1728_tail_safe reference_control_wire_1728_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1728_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1728 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1807 flat_statements reference_control_wire_1728_decl reference_control_wire_1728_mid reference_control_wire_1728_tail 1728 7310 32 invalid flat_memories old current result reference_control_wire_1728_position reference_control_wire_1728_split reference_control_wire_1728_straight reference_control_wire_1728_mid_safe reference_control_wire_1728_tail_safe reference_control_wire_1728_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1729_decl := match straight_drop 1809 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1729_mid := take_statements 6167 reference_control_wire_1729_decl.
Definition reference_control_wire_1729_tail := match straight_drop 7977 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1729_position : straight_drop 1808 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1729 (Gtyp (Fuint 32))) reference_control_wire_1729_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1729_split : reference_control_wire_1729_decl = statement_append reference_control_wire_1729_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1729) (@Eref VarOrder.T (@Eid VarOrder.T 7311))) reference_control_wire_1729_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1729_straight : straight_statements reference_control_wire_1729_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1729_mid_safe : formal_typed_suffix_safe flat_memories 1729 reference_control_wire_1729_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1729_tail_safe : formal_typed_suffix_safe flat_memories 1729 reference_control_wire_1729_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1729_nonregister : has_register 1729 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1729_congruent invalid left right next_left next_right :
 VM.find 7311 left = VM.find 7311 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1729 next_left = VM.find 1729 next_right.
Proof. exact (declared_connection_congruence 1808 flat_statements reference_control_wire_1729_decl reference_control_wire_1729_mid reference_control_wire_1729_tail 1729 7311 32 invalid flat_memories left right next_left next_right reference_control_wire_1729_position reference_control_wire_1729_split reference_control_wire_1729_straight reference_control_wire_1729_mid_safe reference_control_wire_1729_tail_safe reference_control_wire_1729_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1729_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1729 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1808 flat_statements reference_control_wire_1729_decl reference_control_wire_1729_mid reference_control_wire_1729_tail 1729 7311 32 invalid flat_memories old current result reference_control_wire_1729_position reference_control_wire_1729_split reference_control_wire_1729_straight reference_control_wire_1729_mid_safe reference_control_wire_1729_tail_safe reference_control_wire_1729_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1730_decl := match straight_drop 1810 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1730_mid := take_statements 6167 reference_control_wire_1730_decl.
Definition reference_control_wire_1730_tail := match straight_drop 7978 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1730_position : straight_drop 1809 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1730 (Gtyp (Fuint 32))) reference_control_wire_1730_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1730_split : reference_control_wire_1730_decl = statement_append reference_control_wire_1730_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1730) (@Eref VarOrder.T (@Eid VarOrder.T 7312))) reference_control_wire_1730_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1730_straight : straight_statements reference_control_wire_1730_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1730_mid_safe : formal_typed_suffix_safe flat_memories 1730 reference_control_wire_1730_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1730_tail_safe : formal_typed_suffix_safe flat_memories 1730 reference_control_wire_1730_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1730_nonregister : has_register 1730 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1730_congruent invalid left right next_left next_right :
 VM.find 7312 left = VM.find 7312 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1730 next_left = VM.find 1730 next_right.
Proof. exact (declared_connection_congruence 1809 flat_statements reference_control_wire_1730_decl reference_control_wire_1730_mid reference_control_wire_1730_tail 1730 7312 32 invalid flat_memories left right next_left next_right reference_control_wire_1730_position reference_control_wire_1730_split reference_control_wire_1730_straight reference_control_wire_1730_mid_safe reference_control_wire_1730_tail_safe reference_control_wire_1730_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1730_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1730 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1809 flat_statements reference_control_wire_1730_decl reference_control_wire_1730_mid reference_control_wire_1730_tail 1730 7312 32 invalid flat_memories old current result reference_control_wire_1730_position reference_control_wire_1730_split reference_control_wire_1730_straight reference_control_wire_1730_mid_safe reference_control_wire_1730_tail_safe reference_control_wire_1730_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1731_decl := match straight_drop 1811 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1731_mid := take_statements 6167 reference_control_wire_1731_decl.
Definition reference_control_wire_1731_tail := match straight_drop 7979 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1731_position : straight_drop 1810 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1731 (Gtyp (Fuint 32))) reference_control_wire_1731_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1731_split : reference_control_wire_1731_decl = statement_append reference_control_wire_1731_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1731) (@Eref VarOrder.T (@Eid VarOrder.T 7313))) reference_control_wire_1731_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1731_straight : straight_statements reference_control_wire_1731_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1731_mid_safe : formal_typed_suffix_safe flat_memories 1731 reference_control_wire_1731_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1731_tail_safe : formal_typed_suffix_safe flat_memories 1731 reference_control_wire_1731_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1731_nonregister : has_register 1731 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1731_congruent invalid left right next_left next_right :
 VM.find 7313 left = VM.find 7313 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1731 next_left = VM.find 1731 next_right.
Proof. exact (declared_connection_congruence 1810 flat_statements reference_control_wire_1731_decl reference_control_wire_1731_mid reference_control_wire_1731_tail 1731 7313 32 invalid flat_memories left right next_left next_right reference_control_wire_1731_position reference_control_wire_1731_split reference_control_wire_1731_straight reference_control_wire_1731_mid_safe reference_control_wire_1731_tail_safe reference_control_wire_1731_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1731_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1731 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1810 flat_statements reference_control_wire_1731_decl reference_control_wire_1731_mid reference_control_wire_1731_tail 1731 7313 32 invalid flat_memories old current result reference_control_wire_1731_position reference_control_wire_1731_split reference_control_wire_1731_straight reference_control_wire_1731_mid_safe reference_control_wire_1731_tail_safe reference_control_wire_1731_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1732_decl := match straight_drop 1812 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1732_mid := take_statements 6167 reference_control_wire_1732_decl.
Definition reference_control_wire_1732_tail := match straight_drop 7980 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1732_position : straight_drop 1811 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1732 (Gtyp (Fuint 32))) reference_control_wire_1732_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1732_split : reference_control_wire_1732_decl = statement_append reference_control_wire_1732_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1732) (@Eref VarOrder.T (@Eid VarOrder.T 7314))) reference_control_wire_1732_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1732_straight : straight_statements reference_control_wire_1732_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1732_mid_safe : formal_typed_suffix_safe flat_memories 1732 reference_control_wire_1732_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1732_tail_safe : formal_typed_suffix_safe flat_memories 1732 reference_control_wire_1732_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1732_nonregister : has_register 1732 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1732_congruent invalid left right next_left next_right :
 VM.find 7314 left = VM.find 7314 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1732 next_left = VM.find 1732 next_right.
Proof. exact (declared_connection_congruence 1811 flat_statements reference_control_wire_1732_decl reference_control_wire_1732_mid reference_control_wire_1732_tail 1732 7314 32 invalid flat_memories left right next_left next_right reference_control_wire_1732_position reference_control_wire_1732_split reference_control_wire_1732_straight reference_control_wire_1732_mid_safe reference_control_wire_1732_tail_safe reference_control_wire_1732_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1732_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1732 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1811 flat_statements reference_control_wire_1732_decl reference_control_wire_1732_mid reference_control_wire_1732_tail 1732 7314 32 invalid flat_memories old current result reference_control_wire_1732_position reference_control_wire_1732_split reference_control_wire_1732_straight reference_control_wire_1732_mid_safe reference_control_wire_1732_tail_safe reference_control_wire_1732_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1733_decl := match straight_drop 1813 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1733_mid := take_statements 6167 reference_control_wire_1733_decl.
Definition reference_control_wire_1733_tail := match straight_drop 7981 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1733_position : straight_drop 1812 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1733 (Gtyp (Fuint 32))) reference_control_wire_1733_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1733_split : reference_control_wire_1733_decl = statement_append reference_control_wire_1733_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1733) (@Eref VarOrder.T (@Eid VarOrder.T 7315))) reference_control_wire_1733_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1733_straight : straight_statements reference_control_wire_1733_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1733_mid_safe : formal_typed_suffix_safe flat_memories 1733 reference_control_wire_1733_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1733_tail_safe : formal_typed_suffix_safe flat_memories 1733 reference_control_wire_1733_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1733_nonregister : has_register 1733 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1733_congruent invalid left right next_left next_right :
 VM.find 7315 left = VM.find 7315 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1733 next_left = VM.find 1733 next_right.
Proof. exact (declared_connection_congruence 1812 flat_statements reference_control_wire_1733_decl reference_control_wire_1733_mid reference_control_wire_1733_tail 1733 7315 32 invalid flat_memories left right next_left next_right reference_control_wire_1733_position reference_control_wire_1733_split reference_control_wire_1733_straight reference_control_wire_1733_mid_safe reference_control_wire_1733_tail_safe reference_control_wire_1733_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1733_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1733 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1812 flat_statements reference_control_wire_1733_decl reference_control_wire_1733_mid reference_control_wire_1733_tail 1733 7315 32 invalid flat_memories old current result reference_control_wire_1733_position reference_control_wire_1733_split reference_control_wire_1733_straight reference_control_wire_1733_mid_safe reference_control_wire_1733_tail_safe reference_control_wire_1733_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1734_decl := match straight_drop 1814 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1734_mid := take_statements 6167 reference_control_wire_1734_decl.
Definition reference_control_wire_1734_tail := match straight_drop 7982 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1734_position : straight_drop 1813 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1734 (Gtyp (Fuint 32))) reference_control_wire_1734_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1734_split : reference_control_wire_1734_decl = statement_append reference_control_wire_1734_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1734) (@Eref VarOrder.T (@Eid VarOrder.T 7316))) reference_control_wire_1734_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1734_straight : straight_statements reference_control_wire_1734_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1734_mid_safe : formal_typed_suffix_safe flat_memories 1734 reference_control_wire_1734_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1734_tail_safe : formal_typed_suffix_safe flat_memories 1734 reference_control_wire_1734_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1734_nonregister : has_register 1734 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1734_congruent invalid left right next_left next_right :
 VM.find 7316 left = VM.find 7316 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1734 next_left = VM.find 1734 next_right.
Proof. exact (declared_connection_congruence 1813 flat_statements reference_control_wire_1734_decl reference_control_wire_1734_mid reference_control_wire_1734_tail 1734 7316 32 invalid flat_memories left right next_left next_right reference_control_wire_1734_position reference_control_wire_1734_split reference_control_wire_1734_straight reference_control_wire_1734_mid_safe reference_control_wire_1734_tail_safe reference_control_wire_1734_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1734_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1734 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1813 flat_statements reference_control_wire_1734_decl reference_control_wire_1734_mid reference_control_wire_1734_tail 1734 7316 32 invalid flat_memories old current result reference_control_wire_1734_position reference_control_wire_1734_split reference_control_wire_1734_straight reference_control_wire_1734_mid_safe reference_control_wire_1734_tail_safe reference_control_wire_1734_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1735_decl := match straight_drop 1815 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1735_mid := take_statements 6167 reference_control_wire_1735_decl.
Definition reference_control_wire_1735_tail := match straight_drop 7983 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1735_position : straight_drop 1814 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1735 (Gtyp (Fuint 32))) reference_control_wire_1735_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1735_split : reference_control_wire_1735_decl = statement_append reference_control_wire_1735_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1735) (@Eref VarOrder.T (@Eid VarOrder.T 7317))) reference_control_wire_1735_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1735_straight : straight_statements reference_control_wire_1735_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1735_mid_safe : formal_typed_suffix_safe flat_memories 1735 reference_control_wire_1735_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1735_tail_safe : formal_typed_suffix_safe flat_memories 1735 reference_control_wire_1735_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1735_nonregister : has_register 1735 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1735_congruent invalid left right next_left next_right :
 VM.find 7317 left = VM.find 7317 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1735 next_left = VM.find 1735 next_right.
Proof. exact (declared_connection_congruence 1814 flat_statements reference_control_wire_1735_decl reference_control_wire_1735_mid reference_control_wire_1735_tail 1735 7317 32 invalid flat_memories left right next_left next_right reference_control_wire_1735_position reference_control_wire_1735_split reference_control_wire_1735_straight reference_control_wire_1735_mid_safe reference_control_wire_1735_tail_safe reference_control_wire_1735_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1735_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1735 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1814 flat_statements reference_control_wire_1735_decl reference_control_wire_1735_mid reference_control_wire_1735_tail 1735 7317 32 invalid flat_memories old current result reference_control_wire_1735_position reference_control_wire_1735_split reference_control_wire_1735_straight reference_control_wire_1735_mid_safe reference_control_wire_1735_tail_safe reference_control_wire_1735_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1736_decl := match straight_drop 1816 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1736_mid := take_statements 6167 reference_control_wire_1736_decl.
Definition reference_control_wire_1736_tail := match straight_drop 7984 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1736_position : straight_drop 1815 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1736 (Gtyp (Fuint 32))) reference_control_wire_1736_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1736_split : reference_control_wire_1736_decl = statement_append reference_control_wire_1736_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1736) (@Eref VarOrder.T (@Eid VarOrder.T 7318))) reference_control_wire_1736_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1736_straight : straight_statements reference_control_wire_1736_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1736_mid_safe : formal_typed_suffix_safe flat_memories 1736 reference_control_wire_1736_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1736_tail_safe : formal_typed_suffix_safe flat_memories 1736 reference_control_wire_1736_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1736_nonregister : has_register 1736 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1736_congruent invalid left right next_left next_right :
 VM.find 7318 left = VM.find 7318 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1736 next_left = VM.find 1736 next_right.
Proof. exact (declared_connection_congruence 1815 flat_statements reference_control_wire_1736_decl reference_control_wire_1736_mid reference_control_wire_1736_tail 1736 7318 32 invalid flat_memories left right next_left next_right reference_control_wire_1736_position reference_control_wire_1736_split reference_control_wire_1736_straight reference_control_wire_1736_mid_safe reference_control_wire_1736_tail_safe reference_control_wire_1736_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1736_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1736 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1815 flat_statements reference_control_wire_1736_decl reference_control_wire_1736_mid reference_control_wire_1736_tail 1736 7318 32 invalid flat_memories old current result reference_control_wire_1736_position reference_control_wire_1736_split reference_control_wire_1736_straight reference_control_wire_1736_mid_safe reference_control_wire_1736_tail_safe reference_control_wire_1736_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1737_decl := match straight_drop 1817 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1737_mid := take_statements 6167 reference_control_wire_1737_decl.
Definition reference_control_wire_1737_tail := match straight_drop 7985 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1737_position : straight_drop 1816 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1737 (Gtyp (Fuint 32))) reference_control_wire_1737_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1737_split : reference_control_wire_1737_decl = statement_append reference_control_wire_1737_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1737) (@Eref VarOrder.T (@Eid VarOrder.T 7319))) reference_control_wire_1737_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1737_straight : straight_statements reference_control_wire_1737_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1737_mid_safe : formal_typed_suffix_safe flat_memories 1737 reference_control_wire_1737_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1737_tail_safe : formal_typed_suffix_safe flat_memories 1737 reference_control_wire_1737_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1737_nonregister : has_register 1737 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1737_congruent invalid left right next_left next_right :
 VM.find 7319 left = VM.find 7319 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1737 next_left = VM.find 1737 next_right.
Proof. exact (declared_connection_congruence 1816 flat_statements reference_control_wire_1737_decl reference_control_wire_1737_mid reference_control_wire_1737_tail 1737 7319 32 invalid flat_memories left right next_left next_right reference_control_wire_1737_position reference_control_wire_1737_split reference_control_wire_1737_straight reference_control_wire_1737_mid_safe reference_control_wire_1737_tail_safe reference_control_wire_1737_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1737_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1737 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1816 flat_statements reference_control_wire_1737_decl reference_control_wire_1737_mid reference_control_wire_1737_tail 1737 7319 32 invalid flat_memories old current result reference_control_wire_1737_position reference_control_wire_1737_split reference_control_wire_1737_straight reference_control_wire_1737_mid_safe reference_control_wire_1737_tail_safe reference_control_wire_1737_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1738_decl := match straight_drop 1818 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1738_mid := take_statements 6167 reference_control_wire_1738_decl.
Definition reference_control_wire_1738_tail := match straight_drop 7986 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1738_position : straight_drop 1817 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1738 (Gtyp (Fuint 32))) reference_control_wire_1738_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1738_split : reference_control_wire_1738_decl = statement_append reference_control_wire_1738_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1738) (@Eref VarOrder.T (@Eid VarOrder.T 7320))) reference_control_wire_1738_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1738_straight : straight_statements reference_control_wire_1738_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1738_mid_safe : formal_typed_suffix_safe flat_memories 1738 reference_control_wire_1738_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1738_tail_safe : formal_typed_suffix_safe flat_memories 1738 reference_control_wire_1738_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1738_nonregister : has_register 1738 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1738_congruent invalid left right next_left next_right :
 VM.find 7320 left = VM.find 7320 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1738 next_left = VM.find 1738 next_right.
Proof. exact (declared_connection_congruence 1817 flat_statements reference_control_wire_1738_decl reference_control_wire_1738_mid reference_control_wire_1738_tail 1738 7320 32 invalid flat_memories left right next_left next_right reference_control_wire_1738_position reference_control_wire_1738_split reference_control_wire_1738_straight reference_control_wire_1738_mid_safe reference_control_wire_1738_tail_safe reference_control_wire_1738_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1738_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1738 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1817 flat_statements reference_control_wire_1738_decl reference_control_wire_1738_mid reference_control_wire_1738_tail 1738 7320 32 invalid flat_memories old current result reference_control_wire_1738_position reference_control_wire_1738_split reference_control_wire_1738_straight reference_control_wire_1738_mid_safe reference_control_wire_1738_tail_safe reference_control_wire_1738_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
