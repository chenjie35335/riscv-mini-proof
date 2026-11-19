Require Import DataReaderUpdateBlocks DataReaderAddressConnections DataReaderEnableConnections DataReaderFieldConnections.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem data_reader_updates_typed_2 invalid scope position mm phase old current result p3 p4 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports (data_port_fields address enable clock mask data) p3 p4 p5 p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 type_of_val clock = Gtyp Fclock ->
 formal_statements invalid scope position mm old phase current data_reader_updates_2 = Some result ->
 exists new_address new_clock, type_of_val new_address = Gtyp (Fuint 16) /\ type_of_val new_clock = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports (data_port_fields new_address (Gval (Fuint 1) [::true]) new_clock mask data) p3 p4 p5 p1 p0).
Proof.
 intros Current AddressType EnableType ClockType Step.
 cbn [data_reader_updates_2 formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 assert (NoAddress : is_memory_data_port true mm 9178 2 0 = false) by reflexivity.
 assert (NoClock : is_memory_data_port true mm 9178 2 2 = false) by reflexivity.
 rewrite NoAddress NoClock in Step.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 2) 0) (@Eid VarOrder.T 9186) old current)
 as [after_address|] eqn:Address; [|discriminate Step].
 destruct (data_reader_address_typed_2 mm old current after_address p3 p4 p5 p1 p0 address enable clock mask data Current AddressType Address) as [new_address [NewAddress AfterAddress]].
 cbn [formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 destruct (formal_connect invalid (validif_raw_address scope (S position) 0 nil) mm phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 2) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old after_address) as [after_enable|] eqn:Enable; [|discriminate Step].
 pose proof (data_reader_enable_2 invalid _ mm phase old after_address after_enable p3 p4 p5 p1 p0
 new_address enable clock mask data AfterAddress EnableType Enable) as AfterEnable.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 2) 2) (@Eid VarOrder.T 0) old after_enable)
 as [after_clock|] eqn:Clock; [|discriminate Step].
 cbn [formal_statements] in Step. inversion Step; subst result.
 destruct (data_reader_clock_typed_2 mm old after_enable after_clock p3 p4 p5 p1 p0
 new_address (Gval (Fuint 1) [::true]) clock mask data AfterEnable ClockType Clock) as [new_clock [NewClock Final]].
 exists new_address, new_clock. repeat split; assumption.
Qed.
Print Assumptions data_reader_updates_typed_2.
Theorem data_reader_updates_typed_3 invalid scope position mm phase old current result p2 p4 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 (data_port_fields address enable clock mask data) p4 p5 p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 type_of_val clock = Gtyp Fclock ->
 formal_statements invalid scope position mm old phase current data_reader_updates_3 = Some result ->
 exists new_address new_clock, type_of_val new_address = Gtyp (Fuint 16) /\ type_of_val new_clock = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports p2 (data_port_fields new_address (Gval (Fuint 1) [::true]) new_clock mask data) p4 p5 p1 p0).
Proof.
 intros Current AddressType EnableType ClockType Step.
 cbn [data_reader_updates_3 formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 assert (NoAddress : is_memory_data_port true mm 9178 3 0 = false) by reflexivity.
 assert (NoClock : is_memory_data_port true mm 9178 3 2 = false) by reflexivity.
 rewrite NoAddress NoClock in Step.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 3) 0) (@Eid VarOrder.T 9194) old current)
 as [after_address|] eqn:Address; [|discriminate Step].
 destruct (data_reader_address_typed_3 mm old current after_address p2 p4 p5 p1 p0 address enable clock mask data Current AddressType Address) as [new_address [NewAddress AfterAddress]].
 cbn [formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 destruct (formal_connect invalid (validif_raw_address scope (S position) 0 nil) mm phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 3) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old after_address) as [after_enable|] eqn:Enable; [|discriminate Step].
 pose proof (data_reader_enable_3 invalid _ mm phase old after_address after_enable p2 p4 p5 p1 p0
 new_address enable clock mask data AfterAddress EnableType Enable) as AfterEnable.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 3) 2) (@Eid VarOrder.T 0) old after_enable)
 as [after_clock|] eqn:Clock; [|discriminate Step].
 cbn [formal_statements] in Step. inversion Step; subst result.
 destruct (data_reader_clock_typed_3 mm old after_enable after_clock p2 p4 p5 p1 p0
 new_address (Gval (Fuint 1) [::true]) clock mask data AfterEnable ClockType Clock) as [new_clock [NewClock Final]].
 exists new_address, new_clock. repeat split; assumption.
Qed.
Print Assumptions data_reader_updates_typed_3.
Theorem data_reader_updates_typed_4 invalid scope position mm phase old current result p2 p3 p5 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 (data_port_fields address enable clock mask data) p5 p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 type_of_val clock = Gtyp Fclock ->
 formal_statements invalid scope position mm old phase current data_reader_updates_4 = Some result ->
 exists new_address new_clock, type_of_val new_address = Gtyp (Fuint 16) /\ type_of_val new_clock = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports p2 p3 (data_port_fields new_address (Gval (Fuint 1) [::true]) new_clock mask data) p5 p1 p0).
Proof.
 intros Current AddressType EnableType ClockType Step.
 cbn [data_reader_updates_4 formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 assert (NoAddress : is_memory_data_port true mm 9178 4 0 = false) by reflexivity.
 assert (NoClock : is_memory_data_port true mm 9178 4 2 = false) by reflexivity.
 rewrite NoAddress NoClock in Step.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 4) 0) (@Eid VarOrder.T 9202) old current)
 as [after_address|] eqn:Address; [|discriminate Step].
 destruct (data_reader_address_typed_4 mm old current after_address p2 p3 p5 p1 p0 address enable clock mask data Current AddressType Address) as [new_address [NewAddress AfterAddress]].
 cbn [formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 destruct (formal_connect invalid (validif_raw_address scope (S position) 0 nil) mm phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 4) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old after_address) as [after_enable|] eqn:Enable; [|discriminate Step].
 pose proof (data_reader_enable_4 invalid _ mm phase old after_address after_enable p2 p3 p5 p1 p0
 new_address enable clock mask data AfterAddress EnableType Enable) as AfterEnable.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 4) 2) (@Eid VarOrder.T 0) old after_enable)
 as [after_clock|] eqn:Clock; [|discriminate Step].
 cbn [formal_statements] in Step. inversion Step; subst result.
 destruct (data_reader_clock_typed_4 mm old after_enable after_clock p2 p3 p5 p1 p0
 new_address (Gval (Fuint 1) [::true]) clock mask data AfterEnable ClockType Clock) as [new_clock [NewClock Final]].
 exists new_address, new_clock. repeat split; assumption.
Qed.
Print Assumptions data_reader_updates_typed_4.
Theorem data_reader_updates_typed_5 invalid scope position mm phase old current result p2 p3 p4 p1 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 (data_port_fields address enable clock mask data) p1 p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 type_of_val clock = Gtyp Fclock ->
 formal_statements invalid scope position mm old phase current data_reader_updates_5 = Some result ->
 exists new_address new_clock, type_of_val new_address = Gtyp (Fuint 16) /\ type_of_val new_clock = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 (data_port_fields new_address (Gval (Fuint 1) [::true]) new_clock mask data) p1 p0).
Proof.
 intros Current AddressType EnableType ClockType Step.
 cbn [data_reader_updates_5 formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 assert (NoAddress : is_memory_data_port true mm 9178 5 0 = false) by reflexivity.
 assert (NoClock : is_memory_data_port true mm 9178 5 2 = false) by reflexivity.
 rewrite NoAddress NoClock in Step.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 5) 0) (@Eid VarOrder.T 9210) old current)
 as [after_address|] eqn:Address; [|discriminate Step].
 destruct (data_reader_address_typed_5 mm old current after_address p2 p3 p4 p1 p0 address enable clock mask data Current AddressType Address) as [new_address [NewAddress AfterAddress]].
 cbn [formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 destruct (formal_connect invalid (validif_raw_address scope (S position) 0 nil) mm phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 5) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old after_address) as [after_enable|] eqn:Enable; [|discriminate Step].
 pose proof (data_reader_enable_5 invalid _ mm phase old after_address after_enable p2 p3 p4 p1 p0
 new_address enable clock mask data AfterAddress EnableType Enable) as AfterEnable.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 5) 2) (@Eid VarOrder.T 0) old after_enable)
 as [after_clock|] eqn:Clock; [|discriminate Step].
 cbn [formal_statements] in Step. inversion Step; subst result.
 destruct (data_reader_clock_typed_5 mm old after_enable after_clock p2 p3 p4 p1 p0
 new_address (Gval (Fuint 1) [::true]) clock mask data AfterEnable ClockType Clock) as [new_clock [NewClock Final]].
 exists new_address, new_clock. repeat split; assumption.
Qed.
Print Assumptions data_reader_updates_typed_5.
Theorem data_reader_updates_typed_1 invalid scope position mm phase old current result p2 p3 p4 p5 p0 address enable clock mask data :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) p0) ->
 type_of_val address = Gtyp (Fuint 16) ->
 type_of_val enable = Gtyp (Fuint 1) ->
 type_of_val clock = Gtyp Fclock ->
 formal_statements invalid scope position mm old phase current data_reader_updates_1 = Some result ->
 exists new_address new_clock, type_of_val new_address = Gtyp (Fuint 16) /\ type_of_val new_clock = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 (data_port_fields new_address (Gval (Fuint 1) [::true]) new_clock mask data) p0).
Proof.
 intros Current AddressType EnableType ClockType Step.
 cbn [data_reader_updates_1 formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 assert (NoAddress : is_memory_data_port true mm 9178 1 0 = false) by reflexivity.
 assert (NoClock : is_memory_data_port true mm 9178 1 2 = false) by reflexivity.
 rewrite NoAddress NoClock in Step.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 0) (@Eid VarOrder.T 9221) old current)
 as [after_address|] eqn:Address; [|discriminate Step].
 destruct (data_reader_address_typed_1 mm old current after_address p2 p3 p4 p5 p0 address enable clock mask data Current AddressType Address) as [new_address [NewAddress AfterAddress]].
 cbn [formal_statements is_memory_writer_ref is_memory_data_port memory_data_field] in Step.
 destruct (formal_connect invalid (validif_raw_address scope (S position) 0 nil) mm phase
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 1)
 (@Econst VarOrder.T (Fuint 1) [::true]) old after_address) as [after_enable|] eqn:Enable; [|discriminate Step].
 pose proof (data_reader_enable_1 invalid _ mm phase old after_address after_enable p2 p3 p4 p5 p0
 new_address enable clock mask data AfterAddress EnableType Enable) as AfterEnable.
 destruct (bidirectional_connect_with_memory mm (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 2) (@Eid VarOrder.T 0) old after_enable)
 as [after_clock|] eqn:Clock; [|discriminate Step].
 cbn [formal_statements] in Step. inversion Step; subst result.
 destruct (data_reader_clock_typed_1 mm old after_enable after_clock p2 p3 p4 p5 p0
 new_address (Gval (Fuint 1) [::true]) clock mask data AfterEnable ClockType Clock) as [new_clock [NewClock Final]].
 exists new_address, new_clock. repeat split; assumption.
Qed.
Print Assumptions data_reader_updates_typed_1.
