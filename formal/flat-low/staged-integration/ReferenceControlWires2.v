Require Import CoreSocModel ComparisonNodes FormalDeclaredConnection FormalDeclaredConnectionObservation FormalDeclaredConnectionCongruence FormalStatementSegments FormalTypedNodeFrames FormalTypedNodeEquation ScalarNodeFrames RegisterInvariants ScalarSinkTypes DataAddressConnectionCertificates JointUpdateConnectionCertificates.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition reference_control_wire_1739_decl := match straight_drop 1819 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1739_mid := take_statements 6167 reference_control_wire_1739_decl.
Definition reference_control_wire_1739_tail := match straight_drop 7987 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1739_position : straight_drop 1818 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1739 (Gtyp (Fuint 32))) reference_control_wire_1739_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1739_split : reference_control_wire_1739_decl = statement_append reference_control_wire_1739_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1739) (@Eref VarOrder.T (@Eid VarOrder.T 7321))) reference_control_wire_1739_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1739_straight : straight_statements reference_control_wire_1739_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1739_mid_safe : formal_typed_suffix_safe flat_memories 1739 reference_control_wire_1739_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1739_tail_safe : formal_typed_suffix_safe flat_memories 1739 reference_control_wire_1739_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1739_nonregister : has_register 1739 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1739_congruent invalid left right next_left next_right :
 VM.find 7321 left = VM.find 7321 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1739 next_left = VM.find 1739 next_right.
Proof. exact (declared_connection_congruence 1818 flat_statements reference_control_wire_1739_decl reference_control_wire_1739_mid reference_control_wire_1739_tail 1739 7321 32 invalid flat_memories left right next_left next_right reference_control_wire_1739_position reference_control_wire_1739_split reference_control_wire_1739_straight reference_control_wire_1739_mid_safe reference_control_wire_1739_tail_safe reference_control_wire_1739_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1739_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1739 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1818 flat_statements reference_control_wire_1739_decl reference_control_wire_1739_mid reference_control_wire_1739_tail 1739 7321 32 invalid flat_memories old current result reference_control_wire_1739_position reference_control_wire_1739_split reference_control_wire_1739_straight reference_control_wire_1739_mid_safe reference_control_wire_1739_tail_safe reference_control_wire_1739_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1740_decl := match straight_drop 1820 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1740_mid := take_statements 6167 reference_control_wire_1740_decl.
Definition reference_control_wire_1740_tail := match straight_drop 7988 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1740_position : straight_drop 1819 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1740 (Gtyp (Fuint 32))) reference_control_wire_1740_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1740_split : reference_control_wire_1740_decl = statement_append reference_control_wire_1740_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1740) (@Eref VarOrder.T (@Eid VarOrder.T 7322))) reference_control_wire_1740_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1740_straight : straight_statements reference_control_wire_1740_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1740_mid_safe : formal_typed_suffix_safe flat_memories 1740 reference_control_wire_1740_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1740_tail_safe : formal_typed_suffix_safe flat_memories 1740 reference_control_wire_1740_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1740_nonregister : has_register 1740 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1740_congruent invalid left right next_left next_right :
 VM.find 7322 left = VM.find 7322 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1740 next_left = VM.find 1740 next_right.
Proof. exact (declared_connection_congruence 1819 flat_statements reference_control_wire_1740_decl reference_control_wire_1740_mid reference_control_wire_1740_tail 1740 7322 32 invalid flat_memories left right next_left next_right reference_control_wire_1740_position reference_control_wire_1740_split reference_control_wire_1740_straight reference_control_wire_1740_mid_safe reference_control_wire_1740_tail_safe reference_control_wire_1740_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1740_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1740 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1819 flat_statements reference_control_wire_1740_decl reference_control_wire_1740_mid reference_control_wire_1740_tail 1740 7322 32 invalid flat_memories old current result reference_control_wire_1740_position reference_control_wire_1740_split reference_control_wire_1740_straight reference_control_wire_1740_mid_safe reference_control_wire_1740_tail_safe reference_control_wire_1740_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1741_decl := match straight_drop 1821 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1741_mid := take_statements 6167 reference_control_wire_1741_decl.
Definition reference_control_wire_1741_tail := match straight_drop 7989 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1741_position : straight_drop 1820 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1741 (Gtyp (Fuint 32))) reference_control_wire_1741_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1741_split : reference_control_wire_1741_decl = statement_append reference_control_wire_1741_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1741) (@Eref VarOrder.T (@Eid VarOrder.T 7323))) reference_control_wire_1741_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1741_straight : straight_statements reference_control_wire_1741_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1741_mid_safe : formal_typed_suffix_safe flat_memories 1741 reference_control_wire_1741_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1741_tail_safe : formal_typed_suffix_safe flat_memories 1741 reference_control_wire_1741_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1741_nonregister : has_register 1741 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1741_congruent invalid left right next_left next_right :
 VM.find 7323 left = VM.find 7323 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1741 next_left = VM.find 1741 next_right.
Proof. exact (declared_connection_congruence 1820 flat_statements reference_control_wire_1741_decl reference_control_wire_1741_mid reference_control_wire_1741_tail 1741 7323 32 invalid flat_memories left right next_left next_right reference_control_wire_1741_position reference_control_wire_1741_split reference_control_wire_1741_straight reference_control_wire_1741_mid_safe reference_control_wire_1741_tail_safe reference_control_wire_1741_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1741_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1741 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1820 flat_statements reference_control_wire_1741_decl reference_control_wire_1741_mid reference_control_wire_1741_tail 1741 7323 32 invalid flat_memories old current result reference_control_wire_1741_position reference_control_wire_1741_split reference_control_wire_1741_straight reference_control_wire_1741_mid_safe reference_control_wire_1741_tail_safe reference_control_wire_1741_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1742_decl := match straight_drop 1822 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1742_mid := take_statements 6167 reference_control_wire_1742_decl.
Definition reference_control_wire_1742_tail := match straight_drop 7990 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1742_position : straight_drop 1821 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1742 (Gtyp (Fuint 32))) reference_control_wire_1742_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1742_split : reference_control_wire_1742_decl = statement_append reference_control_wire_1742_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1742) (@Eref VarOrder.T (@Eid VarOrder.T 7324))) reference_control_wire_1742_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1742_straight : straight_statements reference_control_wire_1742_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1742_mid_safe : formal_typed_suffix_safe flat_memories 1742 reference_control_wire_1742_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1742_tail_safe : formal_typed_suffix_safe flat_memories 1742 reference_control_wire_1742_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1742_nonregister : has_register 1742 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1742_congruent invalid left right next_left next_right :
 VM.find 7324 left = VM.find 7324 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1742 next_left = VM.find 1742 next_right.
Proof. exact (declared_connection_congruence 1821 flat_statements reference_control_wire_1742_decl reference_control_wire_1742_mid reference_control_wire_1742_tail 1742 7324 32 invalid flat_memories left right next_left next_right reference_control_wire_1742_position reference_control_wire_1742_split reference_control_wire_1742_straight reference_control_wire_1742_mid_safe reference_control_wire_1742_tail_safe reference_control_wire_1742_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1742_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1742 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1821 flat_statements reference_control_wire_1742_decl reference_control_wire_1742_mid reference_control_wire_1742_tail 1742 7324 32 invalid flat_memories old current result reference_control_wire_1742_position reference_control_wire_1742_split reference_control_wire_1742_straight reference_control_wire_1742_mid_safe reference_control_wire_1742_tail_safe reference_control_wire_1742_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1743_decl := match straight_drop 1823 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1743_mid := take_statements 6167 reference_control_wire_1743_decl.
Definition reference_control_wire_1743_tail := match straight_drop 7991 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1743_position : straight_drop 1822 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1743 (Gtyp (Fuint 32))) reference_control_wire_1743_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1743_split : reference_control_wire_1743_decl = statement_append reference_control_wire_1743_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1743) (@Eref VarOrder.T (@Eid VarOrder.T 7325))) reference_control_wire_1743_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1743_straight : straight_statements reference_control_wire_1743_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1743_mid_safe : formal_typed_suffix_safe flat_memories 1743 reference_control_wire_1743_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1743_tail_safe : formal_typed_suffix_safe flat_memories 1743 reference_control_wire_1743_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1743_nonregister : has_register 1743 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1743_congruent invalid left right next_left next_right :
 VM.find 7325 left = VM.find 7325 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1743 next_left = VM.find 1743 next_right.
Proof. exact (declared_connection_congruence 1822 flat_statements reference_control_wire_1743_decl reference_control_wire_1743_mid reference_control_wire_1743_tail 1743 7325 32 invalid flat_memories left right next_left next_right reference_control_wire_1743_position reference_control_wire_1743_split reference_control_wire_1743_straight reference_control_wire_1743_mid_safe reference_control_wire_1743_tail_safe reference_control_wire_1743_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1743_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1743 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1822 flat_statements reference_control_wire_1743_decl reference_control_wire_1743_mid reference_control_wire_1743_tail 1743 7325 32 invalid flat_memories old current result reference_control_wire_1743_position reference_control_wire_1743_split reference_control_wire_1743_straight reference_control_wire_1743_mid_safe reference_control_wire_1743_tail_safe reference_control_wire_1743_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1744_decl := match straight_drop 1824 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1744_mid := take_statements 6167 reference_control_wire_1744_decl.
Definition reference_control_wire_1744_tail := match straight_drop 7992 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1744_position : straight_drop 1823 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1744 (Gtyp (Fuint 32))) reference_control_wire_1744_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1744_split : reference_control_wire_1744_decl = statement_append reference_control_wire_1744_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1744) (@Eref VarOrder.T (@Eid VarOrder.T 7326))) reference_control_wire_1744_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1744_straight : straight_statements reference_control_wire_1744_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1744_mid_safe : formal_typed_suffix_safe flat_memories 1744 reference_control_wire_1744_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1744_tail_safe : formal_typed_suffix_safe flat_memories 1744 reference_control_wire_1744_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1744_nonregister : has_register 1744 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1744_congruent invalid left right next_left next_right :
 VM.find 7326 left = VM.find 7326 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1744 next_left = VM.find 1744 next_right.
Proof. exact (declared_connection_congruence 1823 flat_statements reference_control_wire_1744_decl reference_control_wire_1744_mid reference_control_wire_1744_tail 1744 7326 32 invalid flat_memories left right next_left next_right reference_control_wire_1744_position reference_control_wire_1744_split reference_control_wire_1744_straight reference_control_wire_1744_mid_safe reference_control_wire_1744_tail_safe reference_control_wire_1744_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1744_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1744 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1823 flat_statements reference_control_wire_1744_decl reference_control_wire_1744_mid reference_control_wire_1744_tail 1744 7326 32 invalid flat_memories old current result reference_control_wire_1744_position reference_control_wire_1744_split reference_control_wire_1744_straight reference_control_wire_1744_mid_safe reference_control_wire_1744_tail_safe reference_control_wire_1744_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1745_decl := match straight_drop 1825 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1745_mid := take_statements 6167 reference_control_wire_1745_decl.
Definition reference_control_wire_1745_tail := match straight_drop 7993 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1745_position : straight_drop 1824 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1745 (Gtyp (Fuint 32))) reference_control_wire_1745_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1745_split : reference_control_wire_1745_decl = statement_append reference_control_wire_1745_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1745) (@Eref VarOrder.T (@Eid VarOrder.T 7327))) reference_control_wire_1745_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1745_straight : straight_statements reference_control_wire_1745_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1745_mid_safe : formal_typed_suffix_safe flat_memories 1745 reference_control_wire_1745_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1745_tail_safe : formal_typed_suffix_safe flat_memories 1745 reference_control_wire_1745_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1745_nonregister : has_register 1745 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1745_congruent invalid left right next_left next_right :
 VM.find 7327 left = VM.find 7327 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1745 next_left = VM.find 1745 next_right.
Proof. exact (declared_connection_congruence 1824 flat_statements reference_control_wire_1745_decl reference_control_wire_1745_mid reference_control_wire_1745_tail 1745 7327 32 invalid flat_memories left right next_left next_right reference_control_wire_1745_position reference_control_wire_1745_split reference_control_wire_1745_straight reference_control_wire_1745_mid_safe reference_control_wire_1745_tail_safe reference_control_wire_1745_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1745_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1745 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1824 flat_statements reference_control_wire_1745_decl reference_control_wire_1745_mid reference_control_wire_1745_tail 1745 7327 32 invalid flat_memories old current result reference_control_wire_1745_position reference_control_wire_1745_split reference_control_wire_1745_straight reference_control_wire_1745_mid_safe reference_control_wire_1745_tail_safe reference_control_wire_1745_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1746_decl := match straight_drop 1826 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1746_mid := take_statements 6167 reference_control_wire_1746_decl.
Definition reference_control_wire_1746_tail := match straight_drop 7994 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1746_position : straight_drop 1825 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1746 (Gtyp (Fuint 32))) reference_control_wire_1746_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1746_split : reference_control_wire_1746_decl = statement_append reference_control_wire_1746_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1746) (@Eref VarOrder.T (@Eid VarOrder.T 7328))) reference_control_wire_1746_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1746_straight : straight_statements reference_control_wire_1746_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1746_mid_safe : formal_typed_suffix_safe flat_memories 1746 reference_control_wire_1746_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1746_tail_safe : formal_typed_suffix_safe flat_memories 1746 reference_control_wire_1746_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1746_nonregister : has_register 1746 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1746_congruent invalid left right next_left next_right :
 VM.find 7328 left = VM.find 7328 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1746 next_left = VM.find 1746 next_right.
Proof. exact (declared_connection_congruence 1825 flat_statements reference_control_wire_1746_decl reference_control_wire_1746_mid reference_control_wire_1746_tail 1746 7328 32 invalid flat_memories left right next_left next_right reference_control_wire_1746_position reference_control_wire_1746_split reference_control_wire_1746_straight reference_control_wire_1746_mid_safe reference_control_wire_1746_tail_safe reference_control_wire_1746_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1746_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1746 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1825 flat_statements reference_control_wire_1746_decl reference_control_wire_1746_mid reference_control_wire_1746_tail 1746 7328 32 invalid flat_memories old current result reference_control_wire_1746_position reference_control_wire_1746_split reference_control_wire_1746_straight reference_control_wire_1746_mid_safe reference_control_wire_1746_tail_safe reference_control_wire_1746_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1747_decl := match straight_drop 1827 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1747_mid := take_statements 6167 reference_control_wire_1747_decl.
Definition reference_control_wire_1747_tail := match straight_drop 7995 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1747_position : straight_drop 1826 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1747 (Gtyp (Fuint 32))) reference_control_wire_1747_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1747_split : reference_control_wire_1747_decl = statement_append reference_control_wire_1747_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1747) (@Eref VarOrder.T (@Eid VarOrder.T 7329))) reference_control_wire_1747_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1747_straight : straight_statements reference_control_wire_1747_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1747_mid_safe : formal_typed_suffix_safe flat_memories 1747 reference_control_wire_1747_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1747_tail_safe : formal_typed_suffix_safe flat_memories 1747 reference_control_wire_1747_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1747_nonregister : has_register 1747 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1747_congruent invalid left right next_left next_right :
 VM.find 7329 left = VM.find 7329 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1747 next_left = VM.find 1747 next_right.
Proof. exact (declared_connection_congruence 1826 flat_statements reference_control_wire_1747_decl reference_control_wire_1747_mid reference_control_wire_1747_tail 1747 7329 32 invalid flat_memories left right next_left next_right reference_control_wire_1747_position reference_control_wire_1747_split reference_control_wire_1747_straight reference_control_wire_1747_mid_safe reference_control_wire_1747_tail_safe reference_control_wire_1747_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1747_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1747 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1826 flat_statements reference_control_wire_1747_decl reference_control_wire_1747_mid reference_control_wire_1747_tail 1747 7329 32 invalid flat_memories old current result reference_control_wire_1747_position reference_control_wire_1747_split reference_control_wire_1747_straight reference_control_wire_1747_mid_safe reference_control_wire_1747_tail_safe reference_control_wire_1747_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1748_decl := match straight_drop 1828 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1748_mid := take_statements 6167 reference_control_wire_1748_decl.
Definition reference_control_wire_1748_tail := match straight_drop 7996 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1748_position : straight_drop 1827 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1748 (Gtyp (Fuint 32))) reference_control_wire_1748_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1748_split : reference_control_wire_1748_decl = statement_append reference_control_wire_1748_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1748) (@Eref VarOrder.T (@Eid VarOrder.T 7330))) reference_control_wire_1748_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1748_straight : straight_statements reference_control_wire_1748_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1748_mid_safe : formal_typed_suffix_safe flat_memories 1748 reference_control_wire_1748_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1748_tail_safe : formal_typed_suffix_safe flat_memories 1748 reference_control_wire_1748_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1748_nonregister : has_register 1748 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1748_congruent invalid left right next_left next_right :
 VM.find 7330 left = VM.find 7330 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1748 next_left = VM.find 1748 next_right.
Proof. exact (declared_connection_congruence 1827 flat_statements reference_control_wire_1748_decl reference_control_wire_1748_mid reference_control_wire_1748_tail 1748 7330 32 invalid flat_memories left right next_left next_right reference_control_wire_1748_position reference_control_wire_1748_split reference_control_wire_1748_straight reference_control_wire_1748_mid_safe reference_control_wire_1748_tail_safe reference_control_wire_1748_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1748_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1748 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1827 flat_statements reference_control_wire_1748_decl reference_control_wire_1748_mid reference_control_wire_1748_tail 1748 7330 32 invalid flat_memories old current result reference_control_wire_1748_position reference_control_wire_1748_split reference_control_wire_1748_straight reference_control_wire_1748_mid_safe reference_control_wire_1748_tail_safe reference_control_wire_1748_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1749_decl := match straight_drop 1829 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1749_mid := take_statements 6167 reference_control_wire_1749_decl.
Definition reference_control_wire_1749_tail := match straight_drop 7997 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1749_position : straight_drop 1828 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1749 (Gtyp (Fuint 32))) reference_control_wire_1749_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1749_split : reference_control_wire_1749_decl = statement_append reference_control_wire_1749_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1749) (@Eref VarOrder.T (@Eid VarOrder.T 7331))) reference_control_wire_1749_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1749_straight : straight_statements reference_control_wire_1749_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1749_mid_safe : formal_typed_suffix_safe flat_memories 1749 reference_control_wire_1749_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1749_tail_safe : formal_typed_suffix_safe flat_memories 1749 reference_control_wire_1749_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1749_nonregister : has_register 1749 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1749_congruent invalid left right next_left next_right :
 VM.find 7331 left = VM.find 7331 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1749 next_left = VM.find 1749 next_right.
Proof. exact (declared_connection_congruence 1828 flat_statements reference_control_wire_1749_decl reference_control_wire_1749_mid reference_control_wire_1749_tail 1749 7331 32 invalid flat_memories left right next_left next_right reference_control_wire_1749_position reference_control_wire_1749_split reference_control_wire_1749_straight reference_control_wire_1749_mid_safe reference_control_wire_1749_tail_safe reference_control_wire_1749_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1749_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1749 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1828 flat_statements reference_control_wire_1749_decl reference_control_wire_1749_mid reference_control_wire_1749_tail 1749 7331 32 invalid flat_memories old current result reference_control_wire_1749_position reference_control_wire_1749_split reference_control_wire_1749_straight reference_control_wire_1749_mid_safe reference_control_wire_1749_tail_safe reference_control_wire_1749_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
Definition reference_control_wire_1750_decl := match straight_drop 1830 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition reference_control_wire_1750_mid := take_statements 6167 reference_control_wire_1750_decl.
Definition reference_control_wire_1750_tail := match straight_drop 7998 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma reference_control_wire_1750_position : straight_drop 1829 flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T 1750 (Gtyp (Fuint 32))) reference_control_wire_1750_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1750_split : reference_control_wire_1750_decl = statement_append reference_control_wire_1750_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 1750) (@Eref VarOrder.T (@Eid VarOrder.T 7332))) reference_control_wire_1750_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1750_straight : straight_statements reference_control_wire_1750_mid.
Proof. vm_compute. exact I. Qed.
Lemma reference_control_wire_1750_mid_safe : formal_typed_suffix_safe flat_memories 1750 reference_control_wire_1750_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1750_tail_safe : formal_typed_suffix_safe flat_memories 1750 reference_control_wire_1750_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma reference_control_wire_1750_nonregister : has_register 1750 flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
Theorem reference_control_wire_1750_congruent invalid left right next_left next_right :
 VM.find 7332 left = VM.find 7332 right ->
 formal_value_iter invalid flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter invalid flat_memories right false right flat_statements = Some next_right ->
 VM.find 1750 next_left = VM.find 1750 next_right.
Proof. exact (declared_connection_congruence 1829 flat_statements reference_control_wire_1750_decl reference_control_wire_1750_mid reference_control_wire_1750_tail 1750 7332 32 invalid flat_memories left right next_left next_right reference_control_wire_1750_position reference_control_wire_1750_split reference_control_wire_1750_straight reference_control_wire_1750_mid_safe reference_control_wire_1750_tail_safe reference_control_wire_1750_nonregister (Logic.eq_refl _)). Qed.
Theorem reference_control_wire_1750_ground invalid old current result :
 formal_value_iter invalid flat_memories old false current flat_statements = Some result ->
 exists value ground, VM.find 1750 result = Some value /\ type_of_val value = Gtyp ground.
Proof.
 intro Step. destruct (declared_connection_observation 1829 flat_statements reference_control_wire_1750_decl reference_control_wire_1750_mid reference_control_wire_1750_tail 1750 7332 32 invalid flat_memories old current result reference_control_wire_1750_position reference_control_wire_1750_split reference_control_wire_1750_straight reference_control_wire_1750_mid_safe reference_control_wire_1750_tail_safe reference_control_wire_1750_nonregister (Logic.eq_refl _) Step)
 as [source [value [Source [Adapt Value]]]].
 exists value, (Fuint 32). split; [exact Value|]. exact (adapted_uint_result_type source 32 value Adapt).
Qed.
