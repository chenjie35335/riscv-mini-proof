Require Import DataAllReaderUpdates DataReaderTypedBlocks DataReaderUpdateBlocks DataReaderUpdatePositions DataReaderEnableConnections FormalStatementSegments FormalDeclaredConnection ScalarNodeFrames ComparisonNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem data_all_reader_updates_typed invalid scope position mm phase old current result p0
 a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1 :
 VM.find 9178 current = Some (data_ports (data_port_fields a2 e2 c2 m2 d2) (data_port_fields a3 e3 c3 m3 d3) (data_port_fields a4 e4 c4 m4 d4) (data_port_fields a5 e5 c5 m5 d5) (data_port_fields a1 e1 c1 m1 d1) p0) ->
 type_of_val a2 = Gtyp (Fuint 16) -> type_of_val e2 = Gtyp (Fuint 1) -> type_of_val c2 = Gtyp Fclock ->
 type_of_val a3 = Gtyp (Fuint 16) -> type_of_val e3 = Gtyp (Fuint 1) -> type_of_val c3 = Gtyp Fclock ->
 type_of_val a4 = Gtyp (Fuint 16) -> type_of_val e4 = Gtyp (Fuint 1) -> type_of_val c4 = Gtyp Fclock ->
 type_of_val a5 = Gtyp (Fuint 16) -> type_of_val e5 = Gtyp (Fuint 1) -> type_of_val c5 = Gtyp Fclock ->
 type_of_val a1 = Gtyp (Fuint 16) -> type_of_val e1 = Gtyp (Fuint 1) -> type_of_val c1 = Gtyp Fclock ->
 formal_statements invalid scope position mm old phase current data_all_reader_updates = Some result ->
 exists na2 nc2 na3 nc3 na4 nc4 na5 nc5 na1 nc1,
 type_of_val na2 = Gtyp (Fuint 16) /\ type_of_val na3 = Gtyp (Fuint 16) /\ type_of_val na4 = Gtyp (Fuint 16) /\ type_of_val na5 = Gtyp (Fuint 16) /\ type_of_val na1 = Gtyp (Fuint 16) /\
 type_of_val nc2 = Gtyp Fclock /\ type_of_val nc3 = Gtyp Fclock /\ type_of_val nc4 = Gtyp Fclock /\ type_of_val nc5 = Gtyp Fclock /\ type_of_val nc1 = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports (data_port_fields na2 (Gval (Fuint 1) [::true]) nc2 m2 d2) (data_port_fields na3 (Gval (Fuint 1) [::true]) nc3 m3 d3) (data_port_fields na4 (Gval (Fuint 1) [::true]) nc4 m4 d4) (data_port_fields na5 (Gval (Fuint 1) [::true]) nc5 m5 d5) (data_port_fields na1 (Gval (Fuint 1) [::true]) nc1 m1 d1) p0).
Proof.
 intros Value A2 E2 C2 A3 E3 C3 A4 E4 C4 A5 E5 C5 A1 E1 C1 Steps.
 unfold data_all_reader_updates in Steps.
 destruct (successful_straight_segment data_reader_updates_2 _ invalid scope _ mm old phase current result data_reader_block_straight_2 Steps)
 as [next2 [Block2 Rest2]].
 destruct (data_reader_updates_typed_2 invalid scope _ mm phase old current next2 (data_port_fields a3 e3 c3 m3 d3) (data_port_fields a4 e4 c4 m4 d4) (data_port_fields a5 e5 c5 m5 d5) (data_port_fields a1 e1 c1 m1 d1) p0
 a2 e2 c2 m2 d2 Value A2 E2 C2 Block2)
 as [na2 [nc2 [NA2 [NC2 V2]]]].
 clear Steps. rename Rest2 into Steps.
 destruct (successful_straight_segment data_reader_updates_3 _ invalid scope _ mm old phase next2 result data_reader_block_straight_3 Steps)
 as [next3 [Block3 Rest3]].
 destruct (data_reader_updates_typed_3 invalid scope _ mm phase old next2 next3 (data_port_fields na2 (Gval (Fuint 1) [::true]) nc2 m2 d2) (data_port_fields a4 e4 c4 m4 d4) (data_port_fields a5 e5 c5 m5 d5) (data_port_fields a1 e1 c1 m1 d1) p0
 a3 e3 c3 m3 d3 V2 A3 E3 C3 Block3)
 as [na3 [nc3 [NA3 [NC3 V3]]]].
 clear Steps. rename Rest3 into Steps.
 destruct (successful_straight_segment data_reader_updates_4 _ invalid scope _ mm old phase next3 result data_reader_block_straight_4 Steps)
 as [next4 [Block4 Rest4]].
 destruct (data_reader_updates_typed_4 invalid scope _ mm phase old next3 next4 (data_port_fields na2 (Gval (Fuint 1) [::true]) nc2 m2 d2) (data_port_fields na3 (Gval (Fuint 1) [::true]) nc3 m3 d3) (data_port_fields a5 e5 c5 m5 d5) (data_port_fields a1 e1 c1 m1 d1) p0
 a4 e4 c4 m4 d4 V3 A4 E4 C4 Block4)
 as [na4 [nc4 [NA4 [NC4 V4]]]].
 clear Steps. rename Rest4 into Steps.
 destruct (successful_straight_segment data_reader_updates_5 _ invalid scope _ mm old phase next4 result data_reader_block_straight_5 Steps)
 as [next5 [Block5 Rest5]].
 destruct (data_reader_updates_typed_5 invalid scope _ mm phase old next4 next5 (data_port_fields na2 (Gval (Fuint 1) [::true]) nc2 m2 d2) (data_port_fields na3 (Gval (Fuint 1) [::true]) nc3 m3 d3) (data_port_fields na4 (Gval (Fuint 1) [::true]) nc4 m4 d4) (data_port_fields a1 e1 c1 m1 d1) p0
 a5 e5 c5 m5 d5 V4 A5 E5 C5 Block5)
 as [na5 [nc5 [NA5 [NC5 V5]]]].
 clear Steps. rename Rest5 into Steps.
 destruct (data_reader_updates_typed_1 invalid scope _ mm phase old next5 result (data_port_fields na2 (Gval (Fuint 1) [::true]) nc2 m2 d2) (data_port_fields na3 (Gval (Fuint 1) [::true]) nc3 m3 d3) (data_port_fields na4 (Gval (Fuint 1) [::true]) nc4 m4 d4) (data_port_fields na5 (Gval (Fuint 1) [::true]) nc5 m5 d5) p0
 a1 e1 c1 m1 d1 V5 A1 E1 C1 Steps)
 as [na1 [nc1 [NA1 [NC1 V1]]]].
 exists na2, nc2, na3, nc3, na4, nc4, na5, nc5, na1, nc1. repeat split; assumption.
Qed.
Print Assumptions data_all_reader_updates_typed.
