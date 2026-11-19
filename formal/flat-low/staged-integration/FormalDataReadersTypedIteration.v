Require Import FormalDataReadersIteration DataAllReaderTypedUpdates ScalarNodeFrames DataAllReaderUpdates DataReaderEnableConnections DataReaderSegments DataReaderTail FormalDataPortPreparation FormalStatementSegments FormalNodeEquation FormalNodeSuffixFrames RegisterInvariants FormalRegisterCommitIdentity RegisterCommitCertificate StagedRegisterHold ComparisonNodes.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories data_before_readers data_all_reader_updates data_after_readers.
Theorem data_readers_iteration_typed invalid phase old current result p0
 a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1 :
 VM.find 9178 old = Some (data_ports (data_port_fields a2 e2 c2 m2 d2) (data_port_fields a3 e3 c3 m3 d3) (data_port_fields a4 e4 c4 m4 d4) (data_port_fields a5 e5 c5 m5 d5) (data_port_fields a1 e1 c1 m1 d1) p0) ->
 type_of_val a2 = Gtyp (Fuint 16) -> type_of_val e2 = Gtyp (Fuint 1) -> type_of_val c2 = Gtyp Fclock ->
 type_of_val a3 = Gtyp (Fuint 16) -> type_of_val e3 = Gtyp (Fuint 1) -> type_of_val c3 = Gtyp Fclock ->
 type_of_val a4 = Gtyp (Fuint 16) -> type_of_val e4 = Gtyp (Fuint 1) -> type_of_val c4 = Gtyp Fclock ->
 type_of_val a5 = Gtyp (Fuint 16) -> type_of_val e5 = Gtyp (Fuint 1) -> type_of_val c5 = Gtyp Fclock ->
 type_of_val a1 = Gtyp (Fuint 16) -> type_of_val e1 = Gtyp (Fuint 1) -> type_of_val c1 = Gtyp Fclock ->
 type_of_val d1 = Gtyp (Fuint 32) ->
 formal_value_iter invalid flat_memories old phase current flat_statements = Some result ->
 exists na2 nc2 na3 nc3 na4 nc4 na5 nc5 na1 nc1 updated,
 type_of_val na2 = Gtyp (Fuint 16) /\ type_of_val na3 = Gtyp (Fuint 16) /\ type_of_val na4 = Gtyp (Fuint 16) /\ type_of_val na5 = Gtyp (Fuint 16) /\ type_of_val na1 = Gtyp (Fuint 16) /\
 type_of_val nc2 = Gtyp Fclock /\ type_of_val nc3 = Gtyp Fclock /\ type_of_val nc4 = Gtyp Fclock /\ type_of_val nc5 = Gtyp Fclock /\ type_of_val nc1 = Gtyp Fclock /\
 VM.find 9178 result = Some (data_ports (data_port_fields na2 (Gval (Fuint 1) [::true]) nc2 m2 d2) (data_port_fields na3 (Gval (Fuint 1) [::true]) nc3 m3 d3) (data_port_fields na4 (Gval (Fuint 1) [::true]) nc4 m4 d4) (data_port_fields na5 (Gval (Fuint 1) [::true]) nc5 m5 d5) (data_port_fields na1 (Gval (Fuint 1) [::true]) nc1 m1 d1) updated).
Proof.
 intros Value A2 E2 C2 A3 E3 C3 A4 E4 C4 A5 E5 C5 A1 E1 C1 DataType Step.
 unfold formal_value_iter in Step.
 destruct (formal_statements invalid nil 0 flat_memories old phase current flat_statements)
 as [proposed|] eqn:Statements; [|discriminate Step].
 assert (Projection : VM.find 9178 result = VM.find 9178 proposed).
 { destruct phase.
   - exact (formal_finish_identity_preserves flat_statements invalid nil 0 flat_memories old proposed result 9178 data_port_finish_identity Step).
   - rewrite (staged_finish_false_equal flat_statements invalid nil 0 flat_memories old proposed (fun e => eval_hfexpr_with_memory flat_memories e old old)) in Step.
     exact (finish_registers_preserves_nonregister flat_statements _ old false proposed result 9178 data_port_not_register Step). }
 destruct (formal_straight_prefix 10008 flat_statements _ invalid nil 0 flat_memories old phase current proposed data_port_decl_position Statements)
 as [at_decl Decl].
 cbn [formal_statements] in Decl. rewrite Value data_before_readers_split in Decl.
 destruct (successful_straight_segment data_before_readers _ invalid nil _ flat_memories old phase _ proposed data_before_readers_straight Decl)
 as [before [Middle Rest]].
 assert (Before : VM.find 9178 before = VM.find 9178 old).
 { rewrite Value. eapply formal_suffix_preserves_value; [exact data_before_readers_safe| |exact Middle].
   apply RegisterMapFacts.find_add_eq. reflexivity. }
 destruct (successful_straight_segment data_all_reader_updates _ invalid nil _ flat_memories old phase before proposed data_all_readers_straight Rest)
 as [after [Updates Tail]].
 rewrite Value in Before.
 destruct (data_all_reader_updates_typed invalid nil _ flat_memories phase old before after p0
 a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1
 Before A2 E2 C2 A3 E3 C3 A4 E4 C4 A5 E5 C5 A1 E1 C1 Updates)
 as [na2 [nc2 [na3 [nc3 [na4 [nc4 [na5 [nc5 [na1 [nc1 [NA2 [NA3 [NA4 [NA5 [NA1 [NC2 [NC3 [NC4 [NC5 [NC1 After]]]]]]]]]]]]]]]]]]]].
 destruct (data_tail_preserves_readers invalid nil _ phase old after proposed _ _ _ _ p0
 na1 (Gval (Fuint 1) [::true]) nc1 m1 d1 After DataType Tail)
 as [updated Final].
 exists na2, nc2, na3, nc3, na4, nc4, na5, nc5, na1, nc1, updated.
 repeat split; try assumption. rewrite Projection. exact Final.
Qed.
Print Assumptions data_readers_iteration_typed.
