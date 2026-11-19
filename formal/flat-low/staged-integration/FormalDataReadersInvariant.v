Require Import FormalDataReadersTypedIteration FormalDataPortPreparation DataReaderEnableConnections FormalLocalHistory StagedFlatCircuitIteration CoreSocModel.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_readers_typed env := exists p0 a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1,
 VM.find 9178 env = Some (data_ports (data_port_fields a2 e2 c2 m2 d2) (data_port_fields a3 e3 c3 m3 d3) (data_port_fields a4 e4 c4 m4 d4) (data_port_fields a5 e5 c5 m5 d5) (data_port_fields a1 e1 c1 m1 d1) p0) /\
 type_of_val a2 = Gtyp (Fuint 16) /\ type_of_val e2 = Gtyp (Fuint 1) /\ type_of_val c2 = Gtyp Fclock /\ type_of_val a3 = Gtyp (Fuint 16) /\ type_of_val e3 = Gtyp (Fuint 1) /\ type_of_val c3 = Gtyp Fclock /\ type_of_val a4 = Gtyp (Fuint 16) /\ type_of_val e4 = Gtyp (Fuint 1) /\ type_of_val c4 = Gtyp Fclock /\ type_of_val a5 = Gtyp (Fuint 16) /\ type_of_val e5 = Gtyp (Fuint 1) /\ type_of_val c5 = Gtyp Fclock /\ type_of_val a1 = Gtyp (Fuint 16) /\ type_of_val e1 = Gtyp (Fuint 1) /\ type_of_val c1 = Gtyp Fclock /\ type_of_val d1 = Gtyp (Fuint 32).
Definition data_readers_enabled env := forall port,
 List.In port [::1;2;3;4;5] -> read_memory_port_field env 9178 port 1 = Some (Gval (Fuint 1) [::true]).
Lemma data_readers_initial_typed env :
 VM.find 9178 env = Some (memory_bundle_initial data_port_memory) -> data_readers_typed env.
Proof.
 intro Value. unfold data_readers_typed.
 exists data_port_initial_fields.
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 split; [exact Value|]. repeat split; reflexivity.
Qed.
Lemma data_readers_typed_step invalid old current result phase :
 data_readers_typed old ->
 formal_value_iter invalid ComparisonNodes.flat_memories old phase current ComparisonNodes.flat_statements = Some result ->
 data_readers_typed result /\ data_readers_enabled result.
Proof.
 intros Typed Step. unfold data_readers_typed in Typed.
 destruct Typed as [p0 [a2 [e2 [c2 [m2 [d2 [a3 [e3 [c3 [m3 [d3 [a4 [e4 [c4 [m4 [d4 [a5 [e5 [c5 [m5 [d5 [a1 [e1 [c1 [m1 [d1 [Value [A2 [E2 [C2 [A3 [E3 [C3 [A4 [E4 [C4 [A5 [E5 [C5 [A1 [E1 [C1 D1]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
 destruct (data_readers_iteration_typed invalid phase old current result p0 a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1
 Value A2 E2 C2 A3 E3 C3 A4 E4 C4 A5 E5 C5 A1 E1 C1 D1 Step)
 as [na2 [nc2 [na3 [nc3 [na4 [nc4 [na5 [nc5 [na1 [nc1 [updated [NA2 [NA3 [NA4 [NA5 [NA1 [NC2 [NC3 [NC4 [NC5 [NC1 Final]]]]]]]]]]]]]]]]]]]]].
 split.
 - unfold data_readers_typed. exists updated.
   exists na2, (Gval (Fuint 1) [::true]), nc2, m2, d2.
   exists na3, (Gval (Fuint 1) [::true]), nc3, m3, d3.
   exists na4, (Gval (Fuint 1) [::true]), nc4, m4, d4.
   exists na5, (Gval (Fuint 1) [::true]), nc5, m5, d5.
   exists na1, (Gval (Fuint 1) [::true]), nc1, m1, d1.
   split; [exact Final|]. repeat split; try assumption; reflexivity.
 - unfold data_readers_enabled. intros port Member. cbn [List.In] in Member.
   repeat destruct Member as [Same|Member]; try (subst port; unfold read_memory_port_field; rewrite Final; reflexivity).
   contradiction.
Qed.
Local Opaque generated_modules generated_top.
Lemma circuit_data_readers_typed_step invalid before after phase :
 data_readers_typed (top_environment before) ->
 formal_circuit_value_iter invalid generated_modules generated_top before phase = Some after ->
 data_readers_typed (top_environment after) /\ data_readers_enabled (top_environment after).
Proof.
 intros Typed Step. destruct (flat_iteration_projection invalid before phase after Step)
 as [old [next [Old [LocalStep Next]]]].
 unfold top_environment in Typed |- *. rewrite Old in Typed. rewrite Next.
 exact (data_readers_typed_step _ old old next phase Typed LocalStep).
Qed.
Theorem circuit_data_readers_iterations inputs n before after :
 data_readers_typed (top_environment before) ->
 circuit_formal_iterations generated_modules generated_top inputs (S n) before = Some after ->
 data_readers_typed (top_environment after) /\ data_readers_enabled (top_environment after).
Proof.
 revert before after. induction n as [|n IH]; intros before after Typed Steps;
 cbn [circuit_formal_iterations] in Steps;
 destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top before false)
 as [next|] eqn:Step; [|discriminate Steps| |discriminate Steps].
 - inversion Steps; subst after. exact (circuit_data_readers_typed_step _ before next false Typed Step).
 - apply (IH next after); [|exact Steps].
   exact (proj1 (circuit_data_readers_typed_step _ before next false Typed Step)).
Qed.
Print Assumptions circuit_data_readers_iterations.
