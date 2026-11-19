Require Import DataReaderTail DataWriterFieldConnections DataWriterControlFrames.
From nbits Require Import NBits.
Require Import DataReaderSegments DataWriterReaderFrames DataWriterBidirectionalFrames DataReaderSourceFrame DataReaderEnableConnections FormalConnectionFrames ScalarNodeFrames MemoryWriteFrames ComparisonNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem data_tail_writer_typed invalid scope position phase old current result p2 p3 p4 p5 address enable clock mask data wa we wc wm wd :
 VM.find 9178 current = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) (data_port_fields wa we wc wm wd)) ->
 type_of_val data = Gtyp (Fuint 32) ->
 type_of_val wa = Gtyp (Fuint 16) -> type_of_val we = Gtyp (Fuint 1) ->
 type_of_val wc = Gtyp Fclock -> type_of_val wm = Gtyp (Fuint 1) ->
 formal_statements invalid scope position flat_memories old phase current data_after_readers = Some result ->
 exists address0 enable1 clock2 mask4 data3,
 type_of_val address0 = Gtyp (Fuint 16) /\ type_of_val enable1 = Gtyp (Fuint 1) /\
 type_of_val mask4 = Gtyp (Fuint 1) /\ type_of_val clock2 = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) (data_port_fields address0 enable1 clock2 mask4 data3)).
Proof.
 intros Value Typed WA WE WC WM Step. rewrite data_tail_exact in Step.
 cbn [data_tail_0 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter0 : is_memory_data_port true flat_memories 9178 0 0 = false) by reflexivity.
 rewrite NoWriter0 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 0)
 (@Eid VarOrder.T 9230) old current) as [next0|] eqn:Connect0; [|discriminate Step].
 destruct (data_writer_address_typed flat_memories old current next0 p2 p3 p4 p5
 (data_port_fields address enable clock mask data) wa we wc wm wd Value WA Connect0) as [address0 [Address0 Value0]].
 cbn [data_tail_1 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter1 : is_memory_data_port true flat_memories 9178 0 1 = false) by reflexivity.
 rewrite NoWriter1 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 1)
 (@Eid VarOrder.T 9232) old next0) as [next1|] eqn:Connect1; [|discriminate Step].
 destruct (data_writer_enable_typed flat_memories old next0 next1 p2 p3 p4 p5
 (data_port_fields address enable clock mask data) we address0 wc wm wd Value0 WE Connect1) as [enable1 [Enable1 Value1]].
 cbn [data_tail_2 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter2 : is_memory_data_port true flat_memories 9178 0 2 = false) by reflexivity.
 rewrite NoWriter2 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 2)
 (@Eid VarOrder.T 9231) old next1) as [next2|] eqn:Connect2; [|discriminate Step].
 destruct (data_writer_clock_typed flat_memories old next1 next2 p2 p3 p4 p5
 (data_port_fields address enable clock mask data) address0 enable1 wc wm wd Value1 WC Connect2)
 as [clock2 [Clock2 Value2]].
 cbn [data_tail_3 formal_statements is_memory_writer_ref] in Step.
 match type of Step with
 | context [formal_connect ?inv ?site ?mm ?ph ?lhs ?rhs ?o ?c] =>
 destruct (formal_connect inv site mm ph lhs rhs o c) as [next3|] eqn:Connect3
 end; [|discriminate Step].
 destruct (data_writer_connection_preserves_controls invalid _ phase old next2 next3 _ p2 p3 p4 p5
 (data_port_fields address enable clock mask data) address0 enable1 clock2 wm wd Value2 Connect3)
 as [data3 Value3].
 cbn [data_tail_4 formal_statements is_memory_writer_ref] in Step.
 assert (NoWriter4 : is_memory_data_port true flat_memories 9178 0 3 = false) by reflexivity.
 rewrite NoWriter4 in Step.
 destruct (bidirectional_connect_with_memory flat_memories
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 0) 3)
 (@Eid VarOrder.T 9233) old next3) as [next4|] eqn:Connect4; [|discriminate Step].
 destruct (data_writer_mask_typed flat_memories old next3 next4 p2 p3 p4 p5
 (data_port_fields address enable clock mask data) wm enable1 clock2 address0 data3 Value3 WM Connect4) as [mask4 [Mask4 Value4]].
 cbn [data_tail_5 formal_statements] in Step.
 match type of Step with
 | context [formal_connect ?inv ?site ?mm ?ph ?lhs ?rhs ?o ?c] =>
 destruct (formal_connect inv site mm ph lhs rhs o c) as [next5|] eqn:Connect5
 end; [|discriminate Step].
 assert (Value5 : VM.find 9178 next5 = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) (data_port_fields address0 enable1 clock2 mask4 data3))).
 { rewrite (formal_connection_preserves_other invalid _ flat_memories phase 9178 (@Eid VarOrder.T 9180) _ old next4 next5 (Logic.eq_refl _) data_tail_register_storage_disjoint Connect5).
   exact Value4. }
 cbn [data_tail_6 formal_statements is_memory_writer_ref] in Step.
 destruct (bidirectional_connect_with_memory flat_memories (@Eid VarOrder.T 9220)
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4) old next5)
 as [next6|] eqn:Connect6; [|discriminate Step].
 assert (Value6 : VM.find 9178 next6 = Some (data_ports p2 p3 p4 p5 (data_port_fields address enable clock mask data) (data_port_fields address0 enable1 clock2 mask4 data3))).
 { rewrite (bidirectional_connect_with_memory_preserves_other flat_memories 9178 (@Eid VarOrder.T 9220) (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9176) 0) 4) old next5 next6 (Logic.eq_refl _) (Logic.eq_refl _) Connect6). exact Value5. }
 cbn [data_tail_7 formal_statements is_memory_writer_ref] in Step.
 destruct (bidirectional_connect_with_memory flat_memories (@Eid VarOrder.T 9222)
 (@Esubfield VarOrder.T (@Esubfield VarOrder.T (@Eid VarOrder.T 9178) 1) 4) old next6)
 as [next7|] eqn:Connect7; [|discriminate Step].
 cbn [data_tail_8 formal_statements] in Step. inversion Step; subst result.
 exists address0, enable1, clock2, mask4, data3. repeat split; try assumption.
 exact (data_reader_source_preserved flat_memories (@Eid VarOrder.T 9222) old next6 next7
 p2 p3 p4 p5 (data_port_fields address0 enable1 clock2 mask4 data3) address enable clock mask data (Logic.eq_refl _) Value6 Typed Connect7).
Qed.
Print Assumptions data_tail_writer_typed.
