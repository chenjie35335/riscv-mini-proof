Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem rfa_reset_commit_851 invalid old current result old_value word :
 VM.find 851 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1085 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 851 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 860 flat_statements joint_register_851_decl joint_register_851_mid joint_register_851_tail
 851 joint_register_851_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1085)) (@Eref VarOrder.T (@Eid VarOrder.T 1021)) invalid flat_memories old current result old_value 32
 joint_register_851_position joint_register_851_split joint_register_851_straight joint_register_851_mid_safe joint_register_851_tail_safe Old Typed joint_register_851_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1085)) (@Eref VarOrder.T (@Eid VarOrder.T 1021))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1085 1021 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7299_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7299)))).
Definition rfa_register_7299_decl := match straight_drop 7471 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7299_tail := match straight_drop 7890 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7299_mid := take_statements 418 rfa_register_7299_decl.
Lemma rfa_register_7299_position : straight_drop 7470 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7299 rfa_register_7299_reg) rfa_register_7299_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7299_split : rfa_register_7299_decl = statement_append rfa_register_7299_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7299) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7370)) (@Eref VarOrder.T (@Eid VarOrder.T 1787)))) rfa_register_7299_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7299_straight : straight_statements rfa_register_7299_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7299_mid_safe : formal_typed_suffix_safe flat_memories 7299 rfa_register_7299_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7299_tail_safe : formal_typed_suffix_safe flat_memories 7299 rfa_register_7299_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7299_identity : register_identity_b 7299 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7299 invalid old current result old_value word :
 VM.find 7299 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7370 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7299 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7470 flat_statements rfa_register_7299_decl rfa_register_7299_mid rfa_register_7299_tail
 7299 rfa_register_7299_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7370)) (@Eref VarOrder.T (@Eid VarOrder.T 1787)) invalid flat_memories old current result old_value 32
 rfa_register_7299_position rfa_register_7299_split rfa_register_7299_straight rfa_register_7299_mid_safe rfa_register_7299_tail_safe Old Typed rfa_register_7299_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7370)) (@Eref VarOrder.T (@Eid VarOrder.T 1787))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7370 1787 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_852 invalid old current result old_value word :
 VM.find 852 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1086 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 852 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 861 flat_statements joint_register_852_decl joint_register_852_mid joint_register_852_tail
 852 joint_register_852_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1086)) (@Eref VarOrder.T (@Eid VarOrder.T 1022)) invalid flat_memories old current result old_value 32
 joint_register_852_position joint_register_852_split joint_register_852_straight joint_register_852_mid_safe joint_register_852_tail_safe Old Typed joint_register_852_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1086)) (@Eref VarOrder.T (@Eid VarOrder.T 1022))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1086 1022 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7300_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7300)))).
Definition rfa_register_7300_decl := match straight_drop 7472 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7300_tail := match straight_drop 7891 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7300_mid := take_statements 418 rfa_register_7300_decl.
Lemma rfa_register_7300_position : straight_drop 7471 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7300 rfa_register_7300_reg) rfa_register_7300_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7300_split : rfa_register_7300_decl = statement_append rfa_register_7300_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7300) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7372)) (@Eref VarOrder.T (@Eid VarOrder.T 1788)))) rfa_register_7300_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7300_straight : straight_statements rfa_register_7300_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7300_mid_safe : formal_typed_suffix_safe flat_memories 7300 rfa_register_7300_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7300_tail_safe : formal_typed_suffix_safe flat_memories 7300 rfa_register_7300_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7300_identity : register_identity_b 7300 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7300 invalid old current result old_value word :
 VM.find 7300 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7372 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7300 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7471 flat_statements rfa_register_7300_decl rfa_register_7300_mid rfa_register_7300_tail
 7300 rfa_register_7300_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7372)) (@Eref VarOrder.T (@Eid VarOrder.T 1788)) invalid flat_memories old current result old_value 32
 rfa_register_7300_position rfa_register_7300_split rfa_register_7300_straight rfa_register_7300_mid_safe rfa_register_7300_tail_safe Old Typed rfa_register_7300_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7372)) (@Eref VarOrder.T (@Eid VarOrder.T 1788))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7372 1788 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_853 invalid old current result old_value word :
 VM.find 853 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1087 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 853 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 862 flat_statements joint_register_853_decl joint_register_853_mid joint_register_853_tail
 853 joint_register_853_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1087)) (@Eref VarOrder.T (@Eid VarOrder.T 1023)) invalid flat_memories old current result old_value 32
 joint_register_853_position joint_register_853_split joint_register_853_straight joint_register_853_mid_safe joint_register_853_tail_safe Old Typed joint_register_853_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1087)) (@Eref VarOrder.T (@Eid VarOrder.T 1023))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1087 1023 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7301_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7301)))).
Definition rfa_register_7301_decl := match straight_drop 7473 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7301_tail := match straight_drop 7892 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7301_mid := take_statements 418 rfa_register_7301_decl.
Lemma rfa_register_7301_position : straight_drop 7472 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7301 rfa_register_7301_reg) rfa_register_7301_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7301_split : rfa_register_7301_decl = statement_append rfa_register_7301_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7301) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7374)) (@Eref VarOrder.T (@Eid VarOrder.T 1789)))) rfa_register_7301_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7301_straight : straight_statements rfa_register_7301_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7301_mid_safe : formal_typed_suffix_safe flat_memories 7301 rfa_register_7301_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7301_tail_safe : formal_typed_suffix_safe flat_memories 7301 rfa_register_7301_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7301_identity : register_identity_b 7301 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7301 invalid old current result old_value word :
 VM.find 7301 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7374 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7301 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7472 flat_statements rfa_register_7301_decl rfa_register_7301_mid rfa_register_7301_tail
 7301 rfa_register_7301_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7374)) (@Eref VarOrder.T (@Eid VarOrder.T 1789)) invalid flat_memories old current result old_value 32
 rfa_register_7301_position rfa_register_7301_split rfa_register_7301_straight rfa_register_7301_mid_safe rfa_register_7301_tail_safe Old Typed rfa_register_7301_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7374)) (@Eref VarOrder.T (@Eid VarOrder.T 1789))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7374 1789 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Theorem rfa_reset_commit_854 invalid old current result old_value word :
 VM.find 854 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 779 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1088 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 854 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 863 flat_statements joint_register_854_decl joint_register_854_mid joint_register_854_tail
 854 joint_register_854_reg (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1088)) (@Eref VarOrder.T (@Eid VarOrder.T 1024)) invalid flat_memories old current result old_value 32
 joint_register_854_position joint_register_854_split joint_register_854_straight joint_register_854_mid_safe joint_register_854_tail_safe Old Typed joint_register_854_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 779)) (@Eref VarOrder.T (@Eid VarOrder.T 1088)) (@Eref VarOrder.T (@Eid VarOrder.T 1024))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 779 1088 1024 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
Definition rfa_register_7302_reg := (@mk_freg VarOrder.T (Gtyp (Fuint 32)) (@Eref VarOrder.T (@Eid VarOrder.T 1514)) (Rst (@Econst VarOrder.T (Fuint 1) [::false]) (@Eref VarOrder.T (@Eid VarOrder.T 7302)))).
Definition rfa_register_7302_decl := match straight_drop 7474 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7302_tail := match straight_drop 7893 flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition rfa_register_7302_mid := take_statements 418 rfa_register_7302_decl.
Lemma rfa_register_7302_position : straight_drop 7473 flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T 7302 rfa_register_7302_reg) rfa_register_7302_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7302_split : rfa_register_7302_decl = statement_append rfa_register_7302_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T 7302) (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7376)) (@Eref VarOrder.T (@Eid VarOrder.T 1790)))) rfa_register_7302_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma rfa_register_7302_straight : straight_statements rfa_register_7302_mid.
Proof. vm_compute. exact I. Qed.
Lemma rfa_register_7302_mid_safe : formal_typed_suffix_safe flat_memories 7302 rfa_register_7302_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7302_tail_safe : formal_typed_suffix_safe flat_memories 7302 rfa_register_7302_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma rfa_register_7302_identity : register_identity_b 7302 flat_statements.
Proof. vm_compute. reflexivity. Qed.
Theorem rfa_reset_commit_7302 invalid old current result old_value word :
 VM.find 7302 old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find 1515 old = Some (Gval (Fuint 1) [::true]) ->
 VM.find 7376 old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find 7302 result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation 7473 flat_statements rfa_register_7302_decl rfa_register_7302_mid rfa_register_7302_tail
 7302 rfa_register_7302_reg (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7376)) (@Eref VarOrder.T (@Eid VarOrder.T 1790)) invalid flat_memories old current result old_value 32
 rfa_register_7302_position rfa_register_7302_split rfa_register_7302_straight rfa_register_7302_mid_safe rfa_register_7302_tail_safe Old Typed rfa_register_7302_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1515)) (@Eref VarOrder.T (@Eid VarOrder.T 7376)) (@Eref VarOrder.T (@Eid VarOrder.T 1790))) old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old 1515 7376 1790 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
