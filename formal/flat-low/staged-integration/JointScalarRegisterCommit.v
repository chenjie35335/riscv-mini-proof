Require Import CoreSocModel ComparisonNodes JointBoundaryRegisters JointRegisterCommitCertificates JointUpdateTargets ConcreteRegisterInitialization.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem joint_scalar_registers_commit inputs path old current result :
 (forall node width, List.In (node,width) joint_boundary_registers -> map_uint_concrete (N.of_nat node) width old) ->
 (forall source, List.In source joint_update_targets -> exists ground bits, VM.find (N.of_nat source) old = Some (Gval ground bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old true current flat_statements = Some result ->
 forall node width, List.In (node,width) joint_boundary_registers ->
 node <> 9220%nat -> node <> 9222%nat -> map_uint_concrete (N.of_nat node) width result.
Proof.
 intros Boundary Sources Step node width Member NotFetch NotLoad.
 unfold joint_boundary_registers in Member.
 repeat destruct Member as [Equal|Member]; try contradiction; inversion Equal; subst node width.
 - assert (Present : List.In (142%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 0 (142%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 142%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_142_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 761%nat). apply (@List.nth_error_In _ joint_update_targets 13 761%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (143%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 1 (143%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 143%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_143_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 762%nat). apply (@List.nth_error_In _ joint_update_targets 14 762%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (144%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 2 (144%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 144%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_144_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 767%nat). apply (@List.nth_error_In _ joint_update_targets 19 767%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (145%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 3 (145%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 145%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_145_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 769%nat). apply (@List.nth_error_In _ joint_update_targets 21 769%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (146%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 4 (146%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 146%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_146_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 768%nat). apply (@List.nth_error_In _ joint_update_targets 20 768%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (147%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 5 (147%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 147%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_147_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 770%nat). apply (@List.nth_error_In _ joint_update_targets 22 770%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (150%nat,2%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 6 (150%nat,2%nat)). vm_compute. reflexivity. }
   destruct (Boundary 150%nat 2%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_150_commit inputs path old current result (Gval (Fuint 2) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 752%nat). apply (@List.nth_error_In _ joint_update_targets 4 752%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (151%nat,2%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 7 (151%nat,2%nat)). vm_compute. reflexivity. }
   destruct (Boundary 151%nat 2%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_151_commit inputs path old current result (Gval (Fuint 2) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 754%nat). apply (@List.nth_error_In _ joint_update_targets 6 754%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (152%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 8 (152%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 152%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_152_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 753%nat). apply (@List.nth_error_In _ joint_update_targets 5 753%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (153%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 9 (153%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 153%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_153_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 755%nat). apply (@List.nth_error_In _ joint_update_targets 7 755%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (167%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 10 (167%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 167%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_167_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 757%nat). apply (@List.nth_error_In _ joint_update_targets 9 757%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (168%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 11 (168%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 168%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_168_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 759%nat). apply (@List.nth_error_In _ joint_update_targets 11 759%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (169%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 12 (169%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 169%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_169_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 758%nat). apply (@List.nth_error_In _ joint_update_targets 10 758%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (170%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 13 (170%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 170%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_170_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 760%nat). apply (@List.nth_error_In _ joint_update_targets 12 760%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (187%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 14 (187%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 187%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_187_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 763%nat). apply (@List.nth_error_In _ joint_update_targets 15 763%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (188%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 15 (188%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 188%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_188_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 764%nat). apply (@List.nth_error_In _ joint_update_targets 16 764%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (189%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 16 (189%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 189%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_189_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 750%nat). apply (@List.nth_error_In _ joint_update_targets 2 750%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (190%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 17 (190%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 190%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_190_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 751%nat). apply (@List.nth_error_In _ joint_update_targets 3 751%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (191%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 18 (191%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 191%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_191_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 756%nat). apply (@List.nth_error_In _ joint_update_targets 8 756%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (192%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 19 (192%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 192%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_192_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 116%nat). apply (@List.nth_error_In _ joint_update_targets 1 116%nat). vm_compute. reflexivity.
   + apply (Sources 765%nat). apply (@List.nth_error_In _ joint_update_targets 17 765%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (193%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 20 (193%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 193%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_193_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 766%nat). apply (@List.nth_error_In _ joint_update_targets 18 766%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (851%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 21 (851%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 851%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_851_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1021%nat). apply (@List.nth_error_In _ joint_update_targets 24 1021%nat). vm_compute. reflexivity.
   + apply (Sources 1085%nat). apply (@List.nth_error_In _ joint_update_targets 56 1085%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (852%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 22 (852%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 852%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_852_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1022%nat). apply (@List.nth_error_In _ joint_update_targets 25 1022%nat). vm_compute. reflexivity.
   + apply (Sources 1086%nat). apply (@List.nth_error_In _ joint_update_targets 57 1086%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (853%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 23 (853%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 853%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_853_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1023%nat). apply (@List.nth_error_In _ joint_update_targets 26 1023%nat). vm_compute. reflexivity.
   + apply (Sources 1087%nat). apply (@List.nth_error_In _ joint_update_targets 58 1087%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (854%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 24 (854%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 854%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_854_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1024%nat). apply (@List.nth_error_In _ joint_update_targets 27 1024%nat). vm_compute. reflexivity.
   + apply (Sources 1088%nat). apply (@List.nth_error_In _ joint_update_targets 59 1088%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (855%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 25 (855%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 855%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_855_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1025%nat). apply (@List.nth_error_In _ joint_update_targets 28 1025%nat). vm_compute. reflexivity.
   + apply (Sources 1089%nat). apply (@List.nth_error_In _ joint_update_targets 60 1089%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (856%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 26 (856%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 856%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_856_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1026%nat). apply (@List.nth_error_In _ joint_update_targets 29 1026%nat). vm_compute. reflexivity.
   + apply (Sources 1090%nat). apply (@List.nth_error_In _ joint_update_targets 61 1090%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (857%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 27 (857%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 857%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_857_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1027%nat). apply (@List.nth_error_In _ joint_update_targets 30 1027%nat). vm_compute. reflexivity.
   + apply (Sources 1091%nat). apply (@List.nth_error_In _ joint_update_targets 62 1091%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (858%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 28 (858%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 858%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_858_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1028%nat). apply (@List.nth_error_In _ joint_update_targets 31 1028%nat). vm_compute. reflexivity.
   + apply (Sources 1092%nat). apply (@List.nth_error_In _ joint_update_targets 63 1092%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (859%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 29 (859%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 859%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_859_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1029%nat). apply (@List.nth_error_In _ joint_update_targets 32 1029%nat). vm_compute. reflexivity.
   + apply (Sources 1093%nat). apply (@List.nth_error_In _ joint_update_targets 64 1093%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (860%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 30 (860%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 860%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_860_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1030%nat). apply (@List.nth_error_In _ joint_update_targets 33 1030%nat). vm_compute. reflexivity.
   + apply (Sources 1094%nat). apply (@List.nth_error_In _ joint_update_targets 65 1094%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (861%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 31 (861%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 861%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_861_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1031%nat). apply (@List.nth_error_In _ joint_update_targets 34 1031%nat). vm_compute. reflexivity.
   + apply (Sources 1095%nat). apply (@List.nth_error_In _ joint_update_targets 66 1095%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (862%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 32 (862%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 862%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_862_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1032%nat). apply (@List.nth_error_In _ joint_update_targets 35 1032%nat). vm_compute. reflexivity.
   + apply (Sources 1096%nat). apply (@List.nth_error_In _ joint_update_targets 67 1096%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (863%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 33 (863%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 863%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_863_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1033%nat). apply (@List.nth_error_In _ joint_update_targets 36 1033%nat). vm_compute. reflexivity.
   + apply (Sources 1097%nat). apply (@List.nth_error_In _ joint_update_targets 68 1097%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (864%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 34 (864%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 864%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_864_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1034%nat). apply (@List.nth_error_In _ joint_update_targets 37 1034%nat). vm_compute. reflexivity.
   + apply (Sources 1098%nat). apply (@List.nth_error_In _ joint_update_targets 69 1098%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (865%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 35 (865%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 865%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_865_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1035%nat). apply (@List.nth_error_In _ joint_update_targets 38 1035%nat). vm_compute. reflexivity.
   + apply (Sources 1099%nat). apply (@List.nth_error_In _ joint_update_targets 70 1099%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (866%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 36 (866%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 866%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_866_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1036%nat). apply (@List.nth_error_In _ joint_update_targets 39 1036%nat). vm_compute. reflexivity.
   + apply (Sources 1100%nat). apply (@List.nth_error_In _ joint_update_targets 71 1100%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (867%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 37 (867%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 867%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_867_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1037%nat). apply (@List.nth_error_In _ joint_update_targets 40 1037%nat). vm_compute. reflexivity.
   + apply (Sources 1101%nat). apply (@List.nth_error_In _ joint_update_targets 72 1101%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (868%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 38 (868%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 868%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_868_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1038%nat). apply (@List.nth_error_In _ joint_update_targets 41 1038%nat). vm_compute. reflexivity.
   + apply (Sources 1102%nat). apply (@List.nth_error_In _ joint_update_targets 73 1102%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (869%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 39 (869%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 869%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_869_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1039%nat). apply (@List.nth_error_In _ joint_update_targets 42 1039%nat). vm_compute. reflexivity.
   + apply (Sources 1103%nat). apply (@List.nth_error_In _ joint_update_targets 74 1103%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (870%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 40 (870%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 870%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_870_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1040%nat). apply (@List.nth_error_In _ joint_update_targets 43 1040%nat). vm_compute. reflexivity.
   + apply (Sources 1104%nat). apply (@List.nth_error_In _ joint_update_targets 75 1104%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (871%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 41 (871%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 871%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_871_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1041%nat). apply (@List.nth_error_In _ joint_update_targets 44 1041%nat). vm_compute. reflexivity.
   + apply (Sources 1105%nat). apply (@List.nth_error_In _ joint_update_targets 76 1105%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (872%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 42 (872%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 872%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_872_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1042%nat). apply (@List.nth_error_In _ joint_update_targets 45 1042%nat). vm_compute. reflexivity.
   + apply (Sources 1106%nat). apply (@List.nth_error_In _ joint_update_targets 77 1106%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (873%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 43 (873%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 873%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_873_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1043%nat). apply (@List.nth_error_In _ joint_update_targets 46 1043%nat). vm_compute. reflexivity.
   + apply (Sources 1107%nat). apply (@List.nth_error_In _ joint_update_targets 78 1107%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (874%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 44 (874%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 874%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_874_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1044%nat). apply (@List.nth_error_In _ joint_update_targets 47 1044%nat). vm_compute. reflexivity.
   + apply (Sources 1108%nat). apply (@List.nth_error_In _ joint_update_targets 79 1108%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (875%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 45 (875%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 875%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_875_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1045%nat). apply (@List.nth_error_In _ joint_update_targets 48 1045%nat). vm_compute. reflexivity.
   + apply (Sources 1109%nat). apply (@List.nth_error_In _ joint_update_targets 80 1109%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (876%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 46 (876%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 876%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_876_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1046%nat). apply (@List.nth_error_In _ joint_update_targets 49 1046%nat). vm_compute. reflexivity.
   + apply (Sources 1110%nat). apply (@List.nth_error_In _ joint_update_targets 81 1110%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (877%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 47 (877%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 877%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_877_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1047%nat). apply (@List.nth_error_In _ joint_update_targets 50 1047%nat). vm_compute. reflexivity.
   + apply (Sources 1111%nat). apply (@List.nth_error_In _ joint_update_targets 82 1111%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (878%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 48 (878%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 878%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_878_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1048%nat). apply (@List.nth_error_In _ joint_update_targets 51 1048%nat). vm_compute. reflexivity.
   + apply (Sources 1112%nat). apply (@List.nth_error_In _ joint_update_targets 83 1112%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (879%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 49 (879%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 879%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_879_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1049%nat). apply (@List.nth_error_In _ joint_update_targets 52 1049%nat). vm_compute. reflexivity.
   + apply (Sources 1113%nat). apply (@List.nth_error_In _ joint_update_targets 84 1113%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (880%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 50 (880%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 880%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_880_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1050%nat). apply (@List.nth_error_In _ joint_update_targets 53 1050%nat). vm_compute. reflexivity.
   + apply (Sources 1114%nat). apply (@List.nth_error_In _ joint_update_targets 85 1114%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (881%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 51 (881%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 881%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_881_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1051%nat). apply (@List.nth_error_In _ joint_update_targets 54 1051%nat). vm_compute. reflexivity.
   + apply (Sources 1115%nat). apply (@List.nth_error_In _ joint_update_targets 86 1115%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (882%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 52 (882%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 882%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_882_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 779%nat). apply (@List.nth_error_In _ joint_update_targets 23 779%nat). vm_compute. reflexivity.
   + apply (Sources 1052%nat). apply (@List.nth_error_In _ joint_update_targets 55 1052%nat). vm_compute. reflexivity.
   + apply (Sources 1116%nat). apply (@List.nth_error_In _ joint_update_targets 87 1116%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7748%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 53 (7748%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7748%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7748_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 65%nat). apply (@List.nth_error_In _ joint_update_targets 0 65%nat). vm_compute. reflexivity.
   + apply (Sources 7801%nat). apply (@List.nth_error_In _ joint_update_targets 92 7801%nat). vm_compute. reflexivity.
   + apply (Sources 8158%nat). apply (@List.nth_error_In _ joint_update_targets 104 8158%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7749%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 54 (7749%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7749%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7749_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 65%nat). apply (@List.nth_error_In _ joint_update_targets 0 65%nat). vm_compute. reflexivity.
   + apply (Sources 7800%nat). apply (@List.nth_error_In _ joint_update_targets 91 7800%nat). vm_compute. reflexivity.
   + apply (Sources 8159%nat). apply (@List.nth_error_In _ joint_update_targets 105 8159%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7750%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 55 (7750%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7750%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7750_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 65%nat). apply (@List.nth_error_In _ joint_update_targets 0 65%nat). vm_compute. reflexivity.
   + apply (Sources 7878%nat). apply (@List.nth_error_In _ joint_update_targets 100 7878%nat). vm_compute. reflexivity.
   + apply (Sources 8160%nat). apply (@List.nth_error_In _ joint_update_targets 106 8160%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7751%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 56 (7751%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7751%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7751_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 65%nat). apply (@List.nth_error_In _ joint_update_targets 0 65%nat). vm_compute. reflexivity.
   + apply (Sources 7877%nat). apply (@List.nth_error_In _ joint_update_targets 99 7877%nat). vm_compute. reflexivity.
   + apply (Sources 8161%nat). apply (@List.nth_error_In _ joint_update_targets 107 8161%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7752%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 57 (7752%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7752%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7752_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 65%nat). apply (@List.nth_error_In _ joint_update_targets 0 65%nat). vm_compute. reflexivity.
   + apply (Sources 7879%nat). apply (@List.nth_error_In _ joint_update_targets 101 7879%nat). vm_compute. reflexivity.
   + apply (Sources 8162%nat). apply (@List.nth_error_In _ joint_update_targets 108 8162%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7753%nat,32%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 58 (7753%nat,32%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7753%nat 32%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7753_commit inputs path old current result (Gval (Fuint 32) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 65%nat). apply (@List.nth_error_In _ joint_update_targets 0 65%nat). vm_compute. reflexivity.
   + apply (Sources 7880%nat). apply (@List.nth_error_In _ joint_update_targets 102 7880%nat). vm_compute. reflexivity.
   + apply (Sources 8163%nat). apply (@List.nth_error_In _ joint_update_targets 109 8163%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7754%nat,2%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 59 (7754%nat,2%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7754%nat 2%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7754_commit inputs path old current result (Gval (Fuint 2) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7871%nat). apply (@List.nth_error_In _ joint_update_targets 93 7871%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7755%nat,3%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 60 (7755%nat,3%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7755%nat 3%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7755_commit inputs path old current result (Gval (Fuint 3) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7872%nat). apply (@List.nth_error_In _ joint_update_targets 94 7872%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7756%nat,2%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 61 (7756%nat,2%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7756%nat 2%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7756_commit inputs path old current result (Gval (Fuint 2) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7881%nat). apply (@List.nth_error_In _ joint_update_targets 103 7881%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7757%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 62 (7757%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7757%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7757_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7873%nat). apply (@List.nth_error_In _ joint_update_targets 95 7873%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7758%nat,3%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 63 (7758%nat,3%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7758%nat 3%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7758_commit inputs path old current result (Gval (Fuint 3) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7874%nat). apply (@List.nth_error_In _ joint_update_targets 96 7874%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7759%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 64 (7759%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7759%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7759_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7875%nat). apply (@List.nth_error_In _ joint_update_targets 97 7875%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7760%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 65 (7760%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7760%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7760_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7876%nat). apply (@List.nth_error_In _ joint_update_targets 98 7876%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7762%nat,1%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 66 (7762%nat,1%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7762%nat 1%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7762_commit inputs path old current result (Gval (Fuint 1) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 7761%nat). apply (@List.nth_error_In _ joint_update_targets 88 7761%nat). vm_compute. reflexivity.
   + exact Step.
 - assert (Present : List.In (7768%nat,33%nat) joint_boundary_registers).
   { apply (@List.nth_error_In _ joint_boundary_registers 67 (7768%nat,33%nat)). vm_compute. reflexivity. }
   destruct (Boundary 7768%nat 33%nat Present) as [bits [Size Lookup]].
   unfold map_uint_concrete.
   eapply (joint_register_7768_commit inputs path old current result (Gval (Fuint 33) bits)).
   + exact Lookup.
   + reflexivity.
   + apply (Sources 65%nat). apply (@List.nth_error_In _ joint_update_targets 0 65%nat). vm_compute. reflexivity.
   + apply (Sources 7767%nat). apply (@List.nth_error_In _ joint_update_targets 89 7767%nat). vm_compute. reflexivity.
   + apply (Sources 7781%nat). apply (@List.nth_error_In _ joint_update_targets 90 7781%nat). vm_compute. reflexivity.
   + exact Step.
 - contradiction.
 - contradiction.
Qed.
Print Assumptions joint_scalar_registers_commit.
