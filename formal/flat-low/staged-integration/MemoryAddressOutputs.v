Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate ReferenceStoreRequestData ReferenceLoadSemantics DUTRedirectDecode FormalDeclaredWireCheck.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque generated_modules generated_top.
Definition memory_address_expr_3348 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_3349 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3348)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_3350 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3349))).
Definition memory_address_expr_3366 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_3367 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3366)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_3368 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3367))).
Definition memory_address_expr_3384 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_3385 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3384)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_3386 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3385))).
Definition memory_address_expr_3402 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_3403 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3402)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_3404 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3403))).
Definition memory_address_expr_3423 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_3424 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 3423)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_3425 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 3424))).
Definition memory_address_expr_6514 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6515 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6514)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6516 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6515))).
Definition memory_address_expr_6519 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2679)) (@Eref VarOrder.T (@Eid VarOrder.T 3425)) (@Eref VarOrder.T (@Eid VarOrder.T 6516))).
Definition memory_address_expr_6529 := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition memory_address_expr_6530 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1970)) (@Eref VarOrder.T (@Eid VarOrder.T 6519)) (@Eref VarOrder.T (@Eid VarOrder.T 6529))).
Definition memory_address_expr_6541 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6542 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6541)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6543 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6542))).
Definition memory_address_expr_6545 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2664)) (@Eref VarOrder.T (@Eid VarOrder.T 3404)) (@Eref VarOrder.T (@Eid VarOrder.T 6543))).
Definition memory_address_expr_6554 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1966)) (@Eref VarOrder.T (@Eid VarOrder.T 6545)) (@Eref VarOrder.T (@Eid VarOrder.T 6530))).
Definition memory_address_expr_6566 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6567 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6566)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6568 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6567))).
Definition memory_address_expr_6570 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2649)) (@Eref VarOrder.T (@Eid VarOrder.T 3386)) (@Eref VarOrder.T (@Eid VarOrder.T 6568))).
Definition memory_address_expr_6579 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1962)) (@Eref VarOrder.T (@Eid VarOrder.T 6570)) (@Eref VarOrder.T (@Eid VarOrder.T 6554))).
Definition memory_address_expr_6597 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1958)) (@Eref VarOrder.T (@Eid VarOrder.T 3368)) (@Eref VarOrder.T (@Eid VarOrder.T 6579))).
Definition memory_address_expr_6607 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6608 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6607)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6609 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6608))).
Definition memory_address_expr_6611 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2565)) (@Eref VarOrder.T (@Eid VarOrder.T 3350)) (@Eref VarOrder.T (@Eid VarOrder.T 6609))).
Definition memory_address_expr_6620 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1886)) (@Eref VarOrder.T (@Eid VarOrder.T 6611)) (@Eref VarOrder.T (@Eid VarOrder.T 6597))).
Definition memory_address_expr_6631 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6632 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6631)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6633 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6632))).
Definition memory_address_expr_6643 := (@Econst VarOrder.T (Fuint 32) [::false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false; false]).
Definition memory_address_expr_6644 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1951)) (@Eref VarOrder.T (@Eid VarOrder.T 6633)) (@Eref VarOrder.T (@Eid VarOrder.T 6643))).
Definition memory_address_expr_6651 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6652 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6651)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6653 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6652))).
Definition memory_address_expr_6656 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6657 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6656)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6658 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6657))).
Definition memory_address_expr_6660 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2723)) (@Eref VarOrder.T (@Eid VarOrder.T 6653)) (@Eref VarOrder.T (@Eid VarOrder.T 6658))).
Definition memory_address_expr_6669 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1946)) (@Eref VarOrder.T (@Eid VarOrder.T 6660)) (@Eref VarOrder.T (@Eid VarOrder.T 6644))).
Definition memory_address_expr_6675 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6676 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6675)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6677 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6676))).
Definition memory_address_expr_6680 := (@Eref VarOrder.T (@Eid VarOrder.T 2209)).
Definition memory_address_expr_6681 := (@Eprim_binop VarOrder.T Badd (@Eref VarOrder.T (@Eid VarOrder.T 6680)) (@Eref VarOrder.T (@Eid VarOrder.T 2552))).
Definition memory_address_expr_6682 := (@Eprim_unop VarOrder.T (Utail 1) (@Eref VarOrder.T (@Eid VarOrder.T 6681))).
Definition memory_address_expr_6684 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 2708)) (@Eref VarOrder.T (@Eid VarOrder.T 6677)) (@Eref VarOrder.T (@Eid VarOrder.T 6682))).
Definition memory_address_expr_6693 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1941)) (@Eref VarOrder.T (@Eid VarOrder.T 6684)) (@Eref VarOrder.T (@Eid VarOrder.T 6669))).
Definition memory_address_expr_6959 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6620)) (@Eref VarOrder.T (@Eid VarOrder.T 6529))).
Definition memory_address_expr_6960 := (@Eref VarOrder.T (@Eid VarOrder.T 6959)).
Definition memory_address_expr_6962 := (@Emux VarOrder.T (@Eref VarOrder.T (@Eid VarOrder.T 1707)) (@Eref VarOrder.T (@Eid VarOrder.T 6693)) (@Eref VarOrder.T (@Eid VarOrder.T 6643))).
Definition memory_address_expr_6963 := (@Eref VarOrder.T (@Eid VarOrder.T 6962)).
Definition memory_address_expr_8075 := (@Eref VarOrder.T (@Eid VarOrder.T 8004)).
Definition memory_address_expr_8076 := (@Eref VarOrder.T (@Eid VarOrder.T 8075)).
Definition memory_address_expr_8083 := (@Eref VarOrder.T (@Eid VarOrder.T 8004)).
Definition memory_address_expr_8084 := (@Eref VarOrder.T (@Eid VarOrder.T 8083)).
Definition memory_address_expr_8199 := (@Eref VarOrder.T (@Eid VarOrder.T 8076)).
Definition memory_address_expr_8203 := (@Eref VarOrder.T (@Eid VarOrder.T 8084)).
Definition memory_address_nodes := [::(3348,memory_address_expr_3348);(3349,memory_address_expr_3349);(3350,memory_address_expr_3350);(3366,memory_address_expr_3366);(3367,memory_address_expr_3367);(3368,memory_address_expr_3368);(3384,memory_address_expr_3384);(3385,memory_address_expr_3385);(3386,memory_address_expr_3386);(3402,memory_address_expr_3402);(3403,memory_address_expr_3403);(3404,memory_address_expr_3404);(3423,memory_address_expr_3423);(3424,memory_address_expr_3424);(3425,memory_address_expr_3425);(6514,memory_address_expr_6514);(6515,memory_address_expr_6515);(6516,memory_address_expr_6516);(6519,memory_address_expr_6519);(6529,memory_address_expr_6529);(6530,memory_address_expr_6530);(6541,memory_address_expr_6541);(6542,memory_address_expr_6542);(6543,memory_address_expr_6543);(6545,memory_address_expr_6545);(6554,memory_address_expr_6554);(6566,memory_address_expr_6566);(6567,memory_address_expr_6567);(6568,memory_address_expr_6568);(6570,memory_address_expr_6570);(6579,memory_address_expr_6579);(6597,memory_address_expr_6597);(6607,memory_address_expr_6607);(6608,memory_address_expr_6608);(6609,memory_address_expr_6609);(6611,memory_address_expr_6611);(6620,memory_address_expr_6620);(6631,memory_address_expr_6631);(6632,memory_address_expr_6632);(6633,memory_address_expr_6633);(6643,memory_address_expr_6643);(6644,memory_address_expr_6644);(6651,memory_address_expr_6651);(6652,memory_address_expr_6652);(6653,memory_address_expr_6653);(6656,memory_address_expr_6656);(6657,memory_address_expr_6657);(6658,memory_address_expr_6658);(6660,memory_address_expr_6660);(6669,memory_address_expr_6669);(6675,memory_address_expr_6675);(6676,memory_address_expr_6676);(6677,memory_address_expr_6677);(6680,memory_address_expr_6680);(6681,memory_address_expr_6681);(6682,memory_address_expr_6682);(6684,memory_address_expr_6684);(6693,memory_address_expr_6693);(6959,memory_address_expr_6959);(6960,memory_address_expr_6960);(6962,memory_address_expr_6962);(6963,memory_address_expr_6963);(8075,memory_address_expr_8075);(8076,memory_address_expr_8076);(8083,memory_address_expr_8083);(8084,memory_address_expr_8084);(8199,memory_address_expr_8199);(8203,memory_address_expr_8203)].
Definition memory_address_offsets := [::3427%nat;0%nat;0%nat;15%nat;0%nat;0%nat;15%nat;0%nat;0%nat;15%nat;0%nat;0%nat;18%nat;0%nat;0%nat;3088%nat;0%nat;0%nat;2%nat;9%nat;0%nat;10%nat;0%nat;0%nat;1%nat;8%nat;11%nat;0%nat;0%nat;1%nat;8%nat;17%nat;9%nat;0%nat;0%nat;1%nat;8%nat;10%nat;0%nat;0%nat;9%nat;0%nat;6%nat;0%nat;0%nat;2%nat;0%nat;0%nat;1%nat;8%nat;5%nat;0%nat;0%nat;2%nat;0%nat;0%nat;1%nat;8%nat;265%nat;0%nat;1%nat;0%nat;1538%nat;0%nat;6%nat;0%nat;114%nat;3%nat].
Lemma memory_address_positions :select_node_offsets memory_address_offsets flat_statements=Some memory_address_nodes.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_safety :selected_node_safety flat_memories flat_statements memory_address_offsets flat_statements=true.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_wire_1710 :declared_wire_check flat_memories flat_statements 1789 5561 1710 6960 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_wire_1520 :declared_wire_check flat_memories flat_statements 1599 6138 1520 1710 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_wire_1714 :declared_wire_check flat_memories flat_statements 1793 5560 1714 6963 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_wire_1524 :declared_wire_check flat_memories flat_statements 1603 6137 1524 1714 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_wire_1475 :declared_wire_check flat_memories flat_statements 1554 7408 1475 8199 32=true.
Proof. vm_compute;reflexivity. Qed.
Lemma memory_address_wire_1479 :declared_wire_check flat_memories flat_statements 1558 7408 1479 8203 32=true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories.
Definition memory_address_guards := [::1707;1886;1941;1946;1951;1958;1962;1966;1970;2565;2649;2664;2679;2708;2723].
Definition memory_address_word_3348 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_3348 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3348 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3348.
 exact RS.
Qed.
Definition memory_address_word_3349 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_3348 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_3349 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3349 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_3349.
 apply size_from_N.
Qed.
Definition memory_address_word_3350 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_3349 guards rs1 immediate)).
Lemma memory_address_size_3350 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3350 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3350.
 rewrite size_take(memory_address_size_3349 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_3366 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_3366 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3366 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3366.
 exact RS.
Qed.
Definition memory_address_word_3367 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_3366 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_3367 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3367 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_3367.
 apply size_from_N.
Qed.
Definition memory_address_word_3368 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_3367 guards rs1 immediate)).
Lemma memory_address_size_3368 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3368 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3368.
 rewrite size_take(memory_address_size_3367 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_3384 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_3384 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3384 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3384.
 exact RS.
Qed.
Definition memory_address_word_3385 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_3384 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_3385 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3385 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_3385.
 apply size_from_N.
Qed.
Definition memory_address_word_3386 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_3385 guards rs1 immediate)).
Lemma memory_address_size_3386 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3386 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3386.
 rewrite size_take(memory_address_size_3385 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_3402 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_3402 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3402 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3402.
 exact RS.
Qed.
Definition memory_address_word_3403 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_3402 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_3403 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3403 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_3403.
 apply size_from_N.
Qed.
Definition memory_address_word_3404 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_3403 guards rs1 immediate)).
Lemma memory_address_size_3404 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3404 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3404.
 rewrite size_take(memory_address_size_3403 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_3423 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_3423 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3423 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3423.
 exact RS.
Qed.
Definition memory_address_word_3424 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_3423 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_3424 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3424 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_3424.
 apply size_from_N.
Qed.
Definition memory_address_word_3425 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_3424 guards rs1 immediate)).
Lemma memory_address_size_3425 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_3425 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_3425.
 rewrite size_take(memory_address_size_3424 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6514 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6514 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6514 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6514.
 exact RS.
Qed.
Definition memory_address_word_6515 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6514 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6515 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6515 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6515.
 apply size_from_N.
Qed.
Definition memory_address_word_6516 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6515 guards rs1 immediate)).
Lemma memory_address_size_6516 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6516 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6516.
 rewrite size_take(memory_address_size_6515 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6519 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 2679 then (memory_address_word_3425 guards rs1 immediate) else (memory_address_word_6516 guards rs1 immediate)).
Lemma memory_address_size_6519 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6519 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6519.
 destruct(guards 2679);[apply memory_address_size_3425|apply memory_address_size_6516];assumption.
Qed.
Definition memory_address_word_6529 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (zeros 32).
Lemma memory_address_size_6529 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6529 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6529.
 reflexivity.
Qed.
Definition memory_address_word_6530 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1970 then (memory_address_word_6519 guards rs1 immediate) else (memory_address_word_6529 guards rs1 immediate)).
Lemma memory_address_size_6530 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6530 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6530.
 destruct(guards 1970);[apply memory_address_size_6519|apply memory_address_size_6529];assumption.
Qed.
Definition memory_address_word_6541 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6541 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6541 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6541.
 exact RS.
Qed.
Definition memory_address_word_6542 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6541 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6542 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6542 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6542.
 apply size_from_N.
Qed.
Definition memory_address_word_6543 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6542 guards rs1 immediate)).
Lemma memory_address_size_6543 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6543 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6543.
 rewrite size_take(memory_address_size_6542 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6545 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 2664 then (memory_address_word_3404 guards rs1 immediate) else (memory_address_word_6543 guards rs1 immediate)).
Lemma memory_address_size_6545 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6545 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6545.
 destruct(guards 2664);[apply memory_address_size_3404|apply memory_address_size_6543];assumption.
Qed.
Definition memory_address_word_6554 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1966 then (memory_address_word_6545 guards rs1 immediate) else (memory_address_word_6530 guards rs1 immediate)).
Lemma memory_address_size_6554 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6554 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6554.
 destruct(guards 1966);[apply memory_address_size_6545|apply memory_address_size_6530];assumption.
Qed.
Definition memory_address_word_6566 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6566 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6566 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6566.
 exact RS.
Qed.
Definition memory_address_word_6567 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6566 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6567 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6567 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6567.
 apply size_from_N.
Qed.
Definition memory_address_word_6568 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6567 guards rs1 immediate)).
Lemma memory_address_size_6568 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6568 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6568.
 rewrite size_take(memory_address_size_6567 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6570 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 2649 then (memory_address_word_3386 guards rs1 immediate) else (memory_address_word_6568 guards rs1 immediate)).
Lemma memory_address_size_6570 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6570 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6570.
 destruct(guards 2649);[apply memory_address_size_3386|apply memory_address_size_6568];assumption.
Qed.
Definition memory_address_word_6579 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1962 then (memory_address_word_6570 guards rs1 immediate) else (memory_address_word_6554 guards rs1 immediate)).
Lemma memory_address_size_6579 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6579 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6579.
 destruct(guards 1962);[apply memory_address_size_6570|apply memory_address_size_6554];assumption.
Qed.
Definition memory_address_word_6597 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1958 then (memory_address_word_3368 guards rs1 immediate) else (memory_address_word_6579 guards rs1 immediate)).
Lemma memory_address_size_6597 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6597 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6597.
 destruct(guards 1958);[apply memory_address_size_3368|apply memory_address_size_6579];assumption.
Qed.
Definition memory_address_word_6607 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6607 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6607 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6607.
 exact RS.
Qed.
Definition memory_address_word_6608 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6607 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6608 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6608 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6608.
 apply size_from_N.
Qed.
Definition memory_address_word_6609 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6608 guards rs1 immediate)).
Lemma memory_address_size_6609 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6609 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6609.
 rewrite size_take(memory_address_size_6608 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6611 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 2565 then (memory_address_word_3350 guards rs1 immediate) else (memory_address_word_6609 guards rs1 immediate)).
Lemma memory_address_size_6611 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6611 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6611.
 destruct(guards 2565);[apply memory_address_size_3350|apply memory_address_size_6609];assumption.
Qed.
Definition memory_address_word_6620 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1886 then (memory_address_word_6611 guards rs1 immediate) else (memory_address_word_6597 guards rs1 immediate)).
Lemma memory_address_size_6620 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6620 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6620.
 destruct(guards 1886);[apply memory_address_size_6611|apply memory_address_size_6597];assumption.
Qed.
Definition memory_address_word_6631 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6631 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6631 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6631.
 exact RS.
Qed.
Definition memory_address_word_6632 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6631 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6632 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6632 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6632.
 apply size_from_N.
Qed.
Definition memory_address_word_6633 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6632 guards rs1 immediate)).
Lemma memory_address_size_6633 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6633 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6633.
 rewrite size_take(memory_address_size_6632 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6643 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (zeros 32).
Lemma memory_address_size_6643 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6643 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6643.
 reflexivity.
Qed.
Definition memory_address_word_6644 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1951 then (memory_address_word_6633 guards rs1 immediate) else (memory_address_word_6643 guards rs1 immediate)).
Lemma memory_address_size_6644 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6644 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6644.
 destruct(guards 1951);[apply memory_address_size_6633|apply memory_address_size_6643];assumption.
Qed.
Definition memory_address_word_6651 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6651 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6651 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6651.
 exact RS.
Qed.
Definition memory_address_word_6652 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6651 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6652 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6652 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6652.
 apply size_from_N.
Qed.
Definition memory_address_word_6653 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6652 guards rs1 immediate)).
Lemma memory_address_size_6653 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6653 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6653.
 rewrite size_take(memory_address_size_6652 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6656 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6656 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6656 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6656.
 exact RS.
Qed.
Definition memory_address_word_6657 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6656 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6657 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6657 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6657.
 apply size_from_N.
Qed.
Definition memory_address_word_6658 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6657 guards rs1 immediate)).
Lemma memory_address_size_6658 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6658 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6658.
 rewrite size_take(memory_address_size_6657 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6660 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 2723 then (memory_address_word_6653 guards rs1 immediate) else (memory_address_word_6658 guards rs1 immediate)).
Lemma memory_address_size_6660 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6660 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6660.
 destruct(guards 2723);[apply memory_address_size_6653|apply memory_address_size_6658];assumption.
Qed.
Definition memory_address_word_6669 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1946 then (memory_address_word_6660 guards rs1 immediate) else (memory_address_word_6644 guards rs1 immediate)).
Lemma memory_address_size_6669 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6669 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6669.
 destruct(guards 1946);[apply memory_address_size_6660|apply memory_address_size_6644];assumption.
Qed.
Definition memory_address_word_6675 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6675 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6675 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6675.
 exact RS.
Qed.
Definition memory_address_word_6676 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6675 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6676 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6676 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6676.
 apply size_from_N.
Qed.
Definition memory_address_word_6677 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6676 guards rs1 immediate)).
Lemma memory_address_size_6677 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6677 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6677.
 rewrite size_take(memory_address_size_6676 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6680 (guards:VarOrder.T->bool)(rs1 immediate:bits) := rs1.
Lemma memory_address_size_6680 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6680 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6680.
 exact RS.
Qed.
Definition memory_address_word_6681 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (from_N 33(to_N (memory_address_word_6680 guards rs1 immediate)+to_N immediate)).
Lemma memory_address_size_6681 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6681 guards rs1 immediate)=33%nat.
Proof. intros RS IS. unfold memory_address_word_6681.
 apply size_from_N.
Qed.
Definition memory_address_word_6682 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (take 32 (memory_address_word_6681 guards rs1 immediate)).
Lemma memory_address_size_6682 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6682 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6682.
 rewrite size_take(memory_address_size_6681 guards rs1 immediate RS IS);reflexivity.
Qed.
Definition memory_address_word_6684 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 2708 then (memory_address_word_6677 guards rs1 immediate) else (memory_address_word_6682 guards rs1 immediate)).
Lemma memory_address_size_6684 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6684 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6684.
 destruct(guards 2708);[apply memory_address_size_6677|apply memory_address_size_6682];assumption.
Qed.
Definition memory_address_word_6693 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1941 then (memory_address_word_6684 guards rs1 immediate) else (memory_address_word_6669 guards rs1 immediate)).
Lemma memory_address_size_6693 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6693 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6693.
 destruct(guards 1941);[apply memory_address_size_6684|apply memory_address_size_6669];assumption.
Qed.
Definition memory_address_word_6959 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1707 then (memory_address_word_6620 guards rs1 immediate) else (memory_address_word_6529 guards rs1 immediate)).
Lemma memory_address_size_6959 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6959 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6959.
 destruct(guards 1707);[apply memory_address_size_6620|apply memory_address_size_6529];assumption.
Qed.
Definition memory_address_word_6960 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (memory_address_word_6959 guards rs1 immediate).
Lemma memory_address_size_6960 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6960 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6960.
 apply memory_address_size_6959;assumption.
Qed.
Definition memory_address_word_6962 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (if guards 1707 then (memory_address_word_6693 guards rs1 immediate) else (memory_address_word_6643 guards rs1 immediate)).
Lemma memory_address_size_6962 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6962 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6962.
 destruct(guards 1707);[apply memory_address_size_6693|apply memory_address_size_6643];assumption.
Qed.
Definition memory_address_word_6963 (guards:VarOrder.T->bool)(rs1 immediate:bits) := (memory_address_word_6962 guards rs1 immediate).
Lemma memory_address_size_6963 guards rs1 immediate :size rs1=32%nat ->size immediate=32%nat ->size (memory_address_word_6963 guards rs1 immediate)=32%nat.
Proof. intros RS IS. unfold memory_address_word_6963.
 apply memory_address_size_6962;assumption.
Qed.
Theorem memory_address_reference_history invalid history limit start guards rs1 immediate :
 size rs1=32%nat ->size immediate=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)rs1)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2552(history t)=Some(Gval(Fuint 32)immediate)) ->
 (forall node t,List.In node memory_address_guards ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])) ->
 forall t,(Nat.add start 30<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 6960(history t)=Some(Gval(Fuint 32)(memory_address_word_6960 guards rs1 immediate)) /\
 VM.find 6963(history t)=Some(Gval(Fuint 32)(memory_address_word_6963 guards rs1 immediate)).
Proof.
 intros RS IS Steps Src Imm Guards.
 assert(V3348:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3348(history t)=Some(Gval(Fuint 32)(memory_address_word_3348 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3348 memory_address_expr_3348);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 0%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3348.
 cbn[memory_address_expr_3348 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3349:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3349(history t)=Some(Gval(Fuint 33)(memory_address_word_3349 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3349 memory_address_expr_3349);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 1%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3349.
 cbn[memory_address_expr_3349 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3348 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3350:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3350(history t)=Some(Gval(Fuint 32)(memory_address_word_3350 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3350 memory_address_expr_3350);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 2%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3350.
 cbn[memory_address_expr_3350 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3349 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3366:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3366(history t)=Some(Gval(Fuint 32)(memory_address_word_3366 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3366 memory_address_expr_3366);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 3%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3366.
 cbn[memory_address_expr_3366 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3367:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3367(history t)=Some(Gval(Fuint 33)(memory_address_word_3367 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3367 memory_address_expr_3367);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 4%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3367.
 cbn[memory_address_expr_3367 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3366 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3368:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3368(history t)=Some(Gval(Fuint 32)(memory_address_word_3368 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3368 memory_address_expr_3368);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 5%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3368.
 cbn[memory_address_expr_3368 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3367 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3384:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3384(history t)=Some(Gval(Fuint 32)(memory_address_word_3384 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3384 memory_address_expr_3384);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 6%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3384.
 cbn[memory_address_expr_3384 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3385:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3385(history t)=Some(Gval(Fuint 33)(memory_address_word_3385 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3385 memory_address_expr_3385);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 7%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3385.
 cbn[memory_address_expr_3385 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3384 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3386:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3386(history t)=Some(Gval(Fuint 32)(memory_address_word_3386 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3386 memory_address_expr_3386);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 8%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3386.
 cbn[memory_address_expr_3386 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3385 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3402:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3402(history t)=Some(Gval(Fuint 32)(memory_address_word_3402 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3402 memory_address_expr_3402);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 9%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3402.
 cbn[memory_address_expr_3402 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3403:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3403(history t)=Some(Gval(Fuint 33)(memory_address_word_3403 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3403 memory_address_expr_3403);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 10%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3403.
 cbn[memory_address_expr_3403 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3402 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3404:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3404(history t)=Some(Gval(Fuint 32)(memory_address_word_3404 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3404 memory_address_expr_3404);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 11%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3404.
 cbn[memory_address_expr_3404 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3403 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3423:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3423(history t)=Some(Gval(Fuint 32)(memory_address_word_3423 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3423 memory_address_expr_3423);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 12%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3423.
 cbn[memory_address_expr_3423 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3424:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3424(history t)=Some(Gval(Fuint 33)(memory_address_word_3424 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3424 memory_address_expr_3424);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 13%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3424.
 cbn[memory_address_expr_3424 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3423 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V3425:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 3425(history t)=Some(Gval(Fuint 32)(memory_address_word_3425 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 3425 memory_address_expr_3425);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 14%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_3425.
 cbn[memory_address_expr_3425 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V3424 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6514:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6514(history t)=Some(Gval(Fuint 32)(memory_address_word_6514 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6514 memory_address_expr_6514);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 15%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6514.
 cbn[memory_address_expr_6514 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6515:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6515(history t)=Some(Gval(Fuint 33)(memory_address_word_6515 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6515 memory_address_expr_6515);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 16%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6515.
 cbn[memory_address_expr_6515 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6514 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6516:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6516(history t)=Some(Gval(Fuint 32)(memory_address_word_6516 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6516 memory_address_expr_6516);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 17%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6516.
 cbn[memory_address_expr_6516 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6515 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6519:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6519(history t)=Some(Gval(Fuint 32)(memory_address_word_6519 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6519 memory_address_expr_6519);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 18%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6519.
 eapply(store_data_mux_eval _ _ _ 2679 3425 6516 32);[reflexivity|apply memory_address_size_6516;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V3425;lia|apply V6516;lia|apply dut_decode_adapt;apply memory_address_size_3425;assumption]. }
 assert(V6529:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6529(history t)=Some(Gval(Fuint 32)(memory_address_word_6529 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6529 memory_address_expr_6529);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 19%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6529.
 cbn[memory_address_expr_6529 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert(V6530:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6530(history t)=Some(Gval(Fuint 32)(memory_address_word_6530 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6530 memory_address_expr_6530);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 20%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6530.
 eapply(store_data_mux_eval _ _ _ 1970 6519 6529 32);[reflexivity|apply memory_address_size_6529;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6519;lia|apply V6529;lia|apply dut_decode_adapt;apply memory_address_size_6519;assumption]. }
 assert(V6541:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6541(history t)=Some(Gval(Fuint 32)(memory_address_word_6541 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6541 memory_address_expr_6541);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 21%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6541.
 cbn[memory_address_expr_6541 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6542:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6542(history t)=Some(Gval(Fuint 33)(memory_address_word_6542 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6542 memory_address_expr_6542);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 22%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6542.
 cbn[memory_address_expr_6542 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6541 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6543:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6543(history t)=Some(Gval(Fuint 32)(memory_address_word_6543 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6543 memory_address_expr_6543);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 23%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6543.
 cbn[memory_address_expr_6543 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6542 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6545:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6545(history t)=Some(Gval(Fuint 32)(memory_address_word_6545 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6545 memory_address_expr_6545);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 24%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6545.
 eapply(store_data_mux_eval _ _ _ 2664 3404 6543 32);[reflexivity|apply memory_address_size_6543;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V3404;lia|apply V6543;lia|apply dut_decode_adapt;apply memory_address_size_3404;assumption]. }
 assert(V6554:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6554(history t)=Some(Gval(Fuint 32)(memory_address_word_6554 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6554 memory_address_expr_6554);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 25%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6554.
 eapply(store_data_mux_eval _ _ _ 1966 6545 6530 32);[reflexivity|apply memory_address_size_6530;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6545;lia|apply V6530;lia|apply dut_decode_adapt;apply memory_address_size_6545;assumption]. }
 assert(V6566:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6566(history t)=Some(Gval(Fuint 32)(memory_address_word_6566 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6566 memory_address_expr_6566);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 26%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6566.
 cbn[memory_address_expr_6566 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6567:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6567(history t)=Some(Gval(Fuint 33)(memory_address_word_6567 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6567 memory_address_expr_6567);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 27%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6567.
 cbn[memory_address_expr_6567 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6566 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6568:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6568(history t)=Some(Gval(Fuint 32)(memory_address_word_6568 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6568 memory_address_expr_6568);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 28%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6568.
 cbn[memory_address_expr_6568 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6567 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6570:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6570(history t)=Some(Gval(Fuint 32)(memory_address_word_6570 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6570 memory_address_expr_6570);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 29%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6570.
 eapply(store_data_mux_eval _ _ _ 2649 3386 6568 32);[reflexivity|apply memory_address_size_6568;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V3386;lia|apply V6568;lia|apply dut_decode_adapt;apply memory_address_size_3386;assumption]. }
 assert(V6579:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6579(history t)=Some(Gval(Fuint 32)(memory_address_word_6579 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6579 memory_address_expr_6579);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 30%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6579.
 eapply(store_data_mux_eval _ _ _ 1962 6570 6554 32);[reflexivity|apply memory_address_size_6554;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6570;lia|apply V6554;lia|apply dut_decode_adapt;apply memory_address_size_6570;assumption]. }
 assert(V6597:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6597(history t)=Some(Gval(Fuint 32)(memory_address_word_6597 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6597 memory_address_expr_6597);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 31%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6597.
 eapply(store_data_mux_eval _ _ _ 1958 3368 6579 32);[reflexivity|apply memory_address_size_6579;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V3368;lia|apply V6579;lia|apply dut_decode_adapt;apply memory_address_size_3368;assumption]. }
 assert(V6607:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6607(history t)=Some(Gval(Fuint 32)(memory_address_word_6607 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6607 memory_address_expr_6607);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 32%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6607.
 cbn[memory_address_expr_6607 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6608:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6608(history t)=Some(Gval(Fuint 33)(memory_address_word_6608 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6608 memory_address_expr_6608);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 33%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6608.
 cbn[memory_address_expr_6608 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6607 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6609:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6609(history t)=Some(Gval(Fuint 32)(memory_address_word_6609 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6609 memory_address_expr_6609);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 34%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6609.
 cbn[memory_address_expr_6609 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6608 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6611:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6611(history t)=Some(Gval(Fuint 32)(memory_address_word_6611 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6611 memory_address_expr_6611);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 35%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6611.
 eapply(store_data_mux_eval _ _ _ 2565 3350 6609 32);[reflexivity|apply memory_address_size_6609;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V3350;lia|apply V6609;lia|apply dut_decode_adapt;apply memory_address_size_3350;assumption]. }
 assert(V6620:forall t,(Nat.add start 9<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6620(history t)=Some(Gval(Fuint 32)(memory_address_word_6620 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6620 memory_address_expr_6620);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 36%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6620.
 eapply(store_data_mux_eval _ _ _ 1886 6611 6597 32);[reflexivity|apply memory_address_size_6597;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6611;lia|apply V6597;lia|apply dut_decode_adapt;apply memory_address_size_6611;assumption]. }
 assert(V6631:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6631(history t)=Some(Gval(Fuint 32)(memory_address_word_6631 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6631 memory_address_expr_6631);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 37%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6631.
 cbn[memory_address_expr_6631 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6632:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6632(history t)=Some(Gval(Fuint 33)(memory_address_word_6632 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6632 memory_address_expr_6632);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 38%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6632.
 cbn[memory_address_expr_6632 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6631 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6633:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6633(history t)=Some(Gval(Fuint 32)(memory_address_word_6633 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6633 memory_address_expr_6633);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 39%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6633.
 cbn[memory_address_expr_6633 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6632 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6643:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6643(history t)=Some(Gval(Fuint 32)(memory_address_word_6643 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6643 memory_address_expr_6643);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 40%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6643.
 cbn[memory_address_expr_6643 eval_hfexpr_validif_policy eval_href_validif_policy].
 reflexivity. }
 assert(V6644:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6644(history t)=Some(Gval(Fuint 32)(memory_address_word_6644 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6644 memory_address_expr_6644);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 41%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6644.
 eapply(store_data_mux_eval _ _ _ 1951 6633 6643 32);[reflexivity|apply memory_address_size_6643;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6633;lia|apply V6643;lia|apply dut_decode_adapt;apply memory_address_size_6633;assumption]. }
 assert(V6651:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6651(history t)=Some(Gval(Fuint 32)(memory_address_word_6651 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6651 memory_address_expr_6651);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 42%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6651.
 cbn[memory_address_expr_6651 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6652:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6652(history t)=Some(Gval(Fuint 33)(memory_address_word_6652 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6652 memory_address_expr_6652);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 43%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6652.
 cbn[memory_address_expr_6652 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6651 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6653:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6653(history t)=Some(Gval(Fuint 32)(memory_address_word_6653 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6653 memory_address_expr_6653);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 44%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6653.
 cbn[memory_address_expr_6653 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6652 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6656:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6656(history t)=Some(Gval(Fuint 32)(memory_address_word_6656 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6656 memory_address_expr_6656);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 45%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6656.
 cbn[memory_address_expr_6656 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6657:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6657(history t)=Some(Gval(Fuint 33)(memory_address_word_6657 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6657 memory_address_expr_6657);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 46%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6657.
 cbn[memory_address_expr_6657 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6656 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6658:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6658(history t)=Some(Gval(Fuint 32)(memory_address_word_6658 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6658 memory_address_expr_6658);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 47%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6658.
 cbn[memory_address_expr_6658 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6657 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6660:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6660(history t)=Some(Gval(Fuint 32)(memory_address_word_6660 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6660 memory_address_expr_6660);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 48%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6660.
 eapply(store_data_mux_eval _ _ _ 2723 6653 6658 32);[reflexivity|apply memory_address_size_6658;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6653;lia|apply V6658;lia|apply dut_decode_adapt;apply memory_address_size_6653;assumption]. }
 assert(V6669:forall t,(Nat.add start 5<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6669(history t)=Some(Gval(Fuint 32)(memory_address_word_6669 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6669 memory_address_expr_6669);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 49%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6669.
 eapply(store_data_mux_eval _ _ _ 1946 6660 6644 32);[reflexivity|apply memory_address_size_6644;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6660;lia|apply V6644;lia|apply dut_decode_adapt;apply memory_address_size_6660;assumption]. }
 assert(V6675:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6675(history t)=Some(Gval(Fuint 32)(memory_address_word_6675 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6675 memory_address_expr_6675);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 50%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6675.
 cbn[memory_address_expr_6675 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6676:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6676(history t)=Some(Gval(Fuint 33)(memory_address_word_6676 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6676 memory_address_expr_6676);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 51%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6676.
 cbn[memory_address_expr_6676 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6675 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6677:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6677(history t)=Some(Gval(Fuint 32)(memory_address_word_6677 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6677 memory_address_expr_6677);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 52%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6677.
 cbn[memory_address_expr_6677 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6676 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6680:forall t,(Nat.add start 1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6680(history t)=Some(Gval(Fuint 32)(memory_address_word_6680 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6680 memory_address_expr_6680);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 53%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6680.
 cbn[memory_address_expr_6680 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(Src t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6681:forall t,(Nat.add start 2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6681(history t)=Some(Gval(Fuint 33)(memory_address_word_6681 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6681 memory_address_expr_6681);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 54%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6681.
 cbn[memory_address_expr_6681 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6680 t ltac:(lia)ltac:(lia)).
 rewrite(Imm t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6682:forall t,(Nat.add start 3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6682(history t)=Some(Gval(Fuint 32)(memory_address_word_6682 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6682 memory_address_expr_6682);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 55%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6682.
 cbn[memory_address_expr_6682 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6681 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6684:forall t,(Nat.add start 4<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6684(history t)=Some(Gval(Fuint 32)(memory_address_word_6684 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6684 memory_address_expr_6684);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 56%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6684.
 eapply(store_data_mux_eval _ _ _ 2708 6677 6682 32);[reflexivity|apply memory_address_size_6682;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6677;lia|apply V6682;lia|apply dut_decode_adapt;apply memory_address_size_6677;assumption]. }
 assert(V6693:forall t,(Nat.add start 6<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6693(history t)=Some(Gval(Fuint 32)(memory_address_word_6693 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6693 memory_address_expr_6693);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 57%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6693.
 eapply(store_data_mux_eval _ _ _ 1941 6684 6669 32);[reflexivity|apply memory_address_size_6669;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6684;lia|apply V6669;lia|apply dut_decode_adapt;apply memory_address_size_6684;assumption]. }
 assert(V6959:forall t,(Nat.add start 10<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6959(history t)=Some(Gval(Fuint 32)(memory_address_word_6959 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6959 memory_address_expr_6959);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 58%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6959.
 eapply(store_data_mux_eval _ _ _ 1707 6620 6529 32);[reflexivity|apply memory_address_size_6529;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6620;lia|apply V6529;lia|apply dut_decode_adapt;apply memory_address_size_6620;assumption]. }
 assert(V6960:forall t,(Nat.add start 11<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6960(history t)=Some(Gval(Fuint 32)(memory_address_word_6960 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6960 memory_address_expr_6960);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 59%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6960.
 cbn[memory_address_expr_6960 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6959 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 assert(V6962:forall t,(Nat.add start 7<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6962(history t)=Some(Gval(Fuint 32)(memory_address_word_6962 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6962 memory_address_expr_6962);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 60%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6962.
 eapply(store_data_mux_eval _ _ _ 1707 6693 6643 32);[reflexivity|apply memory_address_size_6643;assumption|apply Guards;[vm_compute;tauto|lia|lia]|apply V6693;lia|apply V6643;lia|apply dut_decode_adapt;apply memory_address_size_6693;assumption]. }
 assert(V6963:forall t,(Nat.add start 8<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 6963(history t)=Some(Gval(Fuint 32)(memory_address_word_6963 guards rs1 immediate))).
 { intros[|t] Lower Upper;try lia.
 eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 6963 memory_address_expr_6963);
 [exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 61%nat);vm_compute;reflexivity| |apply Steps;lia].
 intros site. unfold memory_address_word_6963.
 cbn[memory_address_expr_6963 eval_hfexpr_validif_policy eval_href_validif_policy].
 rewrite(V6962 t ltac:(lia)ltac:(lia)).
 reflexivity. }
 intros t Lower Upper;split;[apply V6960|apply V6963];lia.
Qed.
Theorem memory_address_outputs_history invalid history limit start guards rs1 immediate address :
 size rs1=32%nat ->size immediate=32%nat ->size address=32%nat ->
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2209(history t)=Some(Gval(Fuint 32)rs1)) ->
 (forall t,(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 2552(history t)=Some(Gval(Fuint 32)immediate)) ->
 (forall node t,List.In node memory_address_guards ->(start<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find node(history t)=Some(Gval(Fuint 1)[::guards node])) ->
 (forall t,(t<=limit)%coq_nat ->VM.find 8004(history t)=Some(Gval(Fuint 32)address)) ->
 forall t,(Nat.add start 34<=t)%coq_nat ->(t<=limit)%coq_nat ->
 VM.find 1475(history t)=Some(Gval(Fuint 32)address) /\VM.find 1479(history t)=Some(Gval(Fuint 32)address) /\
 VM.find 1520(history t)=Some(Gval(Fuint 32)(memory_address_word_6960 guards rs1 immediate)) /\
 VM.find 1524(history t)=Some(Gval(Fuint 32)(memory_address_word_6963 guards rs1 immediate)).
Proof.
 intros RS IS AS Steps Src Imm Guards Address.
 pose proof(memory_address_reference_history invalid history limit start guards rs1 immediate RS IS Steps Src Imm Guards)as Ref.
 assert(V8075:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8075(history t)=Some(Gval(Fuint 32)address)).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 8075 memory_address_expr_8075 _ _ invalid(history t)(history t)(history(S t)));[exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 62%nat);vm_compute;reflexivity|intros site;apply Address;lia|apply Steps;lia]. }
 assert(V8076:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8076(history t)=Some(Gval(Fuint 32)address)).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 8076 memory_address_expr_8076 _ _ invalid(history t)(history t)(history(S t)));[exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 63%nat);vm_compute;reflexivity|intros site;apply V8075;lia|apply Steps;lia]. }
 assert(V8199:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8199(history t)=Some(Gval(Fuint 32)address)).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 8199 memory_address_expr_8199 _ _ invalid(history t)(history t)(history(S t)));[exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 66%nat);vm_compute;reflexivity|intros site;apply V8076;lia|apply Steps;lia]. }
 assert(V8083:forall t,(1<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8083(history t)=Some(Gval(Fuint 32)address)).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 8083 memory_address_expr_8083 _ _ invalid(history t)(history t)(history(S t)));[exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 64%nat);vm_compute;reflexivity|intros site;apply Address;lia|apply Steps;lia]. }
 assert(V8084:forall t,(2<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8084(history t)=Some(Gval(Fuint 32)address)).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 8084 memory_address_expr_8084 _ _ invalid(history t)(history t)(history(S t)));[exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 65%nat);vm_compute;reflexivity|intros site;apply V8083;lia|apply Steps;lia]. }
 assert(V8203:forall t,(3<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find 8203(history t)=Some(Gval(Fuint 32)address)).
 { intros[|t] Lower Upper;try lia. eapply(reference_redirect_ground_step memory_address_offsets memory_address_nodes 8203 memory_address_expr_8203 _ _ invalid(history t)(history t)(history(S t)));[exact memory_address_positions|exact memory_address_safety|apply(List.nth_error_In memory_address_nodes 67%nat);vm_compute;reflexivity|intros site;apply V8084;lia|apply Steps;lia]. }
 intros[|[|[|[|t]]]] Lower Upper;try lia. repeat split.
 - eapply declared_wire_checked_value with (old:=history(S(S(S t)))) (current:=history(S(S(S t))));[exact memory_address_wire_1475|apply V8199;lia|apply dut_decode_adapt;exact AS|apply Steps;lia].
 - eapply declared_wire_checked_value with (old:=history(S(S(S t)))) (current:=history(S(S(S t))));[exact memory_address_wire_1479|apply V8203;lia|apply dut_decode_adapt;exact AS|apply Steps;lia].
 - eapply declared_wire_checked_value with (old:=history(S(S(S t)))) (current:=history(S(S(S t))));[exact memory_address_wire_1520| |apply dut_decode_adapt;apply memory_address_size_6960;assumption|apply Steps;lia].
 eapply declared_wire_checked_value with (old:=history(S(S t))) (current:=history(S(S t)));[exact memory_address_wire_1710|exact(proj1(Ref (S(S t)) ltac:(lia)ltac:(lia)))|apply dut_decode_adapt;apply memory_address_size_6960;assumption|apply Steps;lia].
 - eapply declared_wire_checked_value with (old:=history(S(S(S t)))) (current:=history(S(S(S t))));[exact memory_address_wire_1524| |apply dut_decode_adapt;apply memory_address_size_6963;assumption|apply Steps;lia].
 eapply declared_wire_checked_value with (old:=history(S(S t))) (current:=history(S(S t)));[exact memory_address_wire_1714|exact(proj2(Ref (S(S t)) ltac:(lia)ltac:(lia)))|apply dut_decode_adapt;apply memory_address_size_6963;assumption|apply Steps;lia].
Qed.
