Require Import FormalDataWriterTypedIteration FormalDataPortPreparation DataReaderEnableConnections FormalLocalHistory StagedFlatCircuitIteration CoreSocModel.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_ports_typed env := exists wa we wc wm wd a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1,
 VM.find 9178 env = Some (data_ports (data_port_fields a2 e2 c2 m2 d2) (data_port_fields a3 e3 c3 m3 d3) (data_port_fields a4 e4 c4 m4 d4) (data_port_fields a5 e5 c5 m5 d5) (data_port_fields a1 e1 c1 m1 d1) (data_port_fields wa we wc wm wd)) /\
 type_of_val a2 = Gtyp (Fuint 16) /\
 type_of_val e2 = Gtyp (Fuint 1) /\
 type_of_val c2 = Gtyp Fclock /\
 type_of_val a3 = Gtyp (Fuint 16) /\
 type_of_val e3 = Gtyp (Fuint 1) /\
 type_of_val c3 = Gtyp Fclock /\
 type_of_val a4 = Gtyp (Fuint 16) /\
 type_of_val e4 = Gtyp (Fuint 1) /\
 type_of_val c4 = Gtyp Fclock /\
 type_of_val a5 = Gtyp (Fuint 16) /\
 type_of_val e5 = Gtyp (Fuint 1) /\
 type_of_val c5 = Gtyp Fclock /\
 type_of_val a1 = Gtyp (Fuint 16) /\
 type_of_val e1 = Gtyp (Fuint 1) /\
 type_of_val c1 = Gtyp Fclock /\
 type_of_val d1 = Gtyp (Fuint 32) /\
 type_of_val wa = Gtyp (Fuint 16) /\
 type_of_val we = Gtyp (Fuint 1) /\
 type_of_val wc = Gtyp Fclock /\
 type_of_val wm = Gtyp (Fuint 1).
Lemma data_ports_initial_typed env :
 VM.find 9178 env = Some (memory_bundle_initial data_port_memory) -> data_ports_typed env.
Proof.
 intro Value. unfold data_ports_typed.
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 exists (Needtobedefined (Gtyp (Fuint 16))), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp Fclock)), (Needtobedefined (Gtyp (Fuint 1))), (Needtobedefined (Gtyp (Fuint 32))).
 split; [exact Value|]. repeat split; reflexivity.
Qed.
Lemma data_ports_typed_step invalid old current result phase :
 data_ports_typed old ->
 formal_value_iter invalid ComparisonNodes.flat_memories old phase current ComparisonNodes.flat_statements = Some result ->
 data_ports_typed result.
Proof.
 intros Typed Step. unfold data_ports_typed in Typed.
 destruct Typed as [wa [we [wc [wm [wd [a2 [e2 [c2 [m2 [d2 [a3 [e3 [c3 [m3 [d3 [a4 [e4 [c4 [m4 [d4 [a5 [e5 [c5 [m5 [d5 [a1 [e1 [c1 [m1 [d1 [Value [T_a2 [T_e2 [T_c2 [T_a3 [T_e3 [T_c3 [T_a4 [T_e4 [T_c4 [T_a5 [T_e5 [T_c5 [T_a1 [T_e1 [T_c1 [T_d1 [T_wa [T_we [T_wc T_wm]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
 destruct (data_writer_iteration_typed invalid phase old current result wa we wc wm wd a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1 Value T_a2 T_e2 T_c2 T_a3 T_e3 T_c3 T_a4 T_e4 T_c4 T_a5 T_e5 T_c5 T_a1 T_e1 T_c1 T_d1 T_wa T_we T_wc T_wm Step)
 as [na2 [nc2 [na3 [nc3 [na4 [nc4 [na5 [nc5 [na1 [nc1 [address0 [enable0 [clock0 [mask0 [data0 [Address0 [Enable0 [Mask0 [Clock0 [NA2 [NA3 [NA4 [NA5 [NA1 [NC2 [NC3 [NC4 [NC5 [NC1 Final]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
 unfold data_ports_typed.
 exists address0, enable0, clock0, mask0, data0.
 exists na2, (Gval (Fuint 1) [::true]), nc2, m2, d2.
 exists na3, (Gval (Fuint 1) [::true]), nc3, m3, d3.
 exists na4, (Gval (Fuint 1) [::true]), nc4, m4, d4.
 exists na5, (Gval (Fuint 1) [::true]), nc5, m5, d5.
 exists na1, (Gval (Fuint 1) [::true]), nc1, m1, d1.
 split; [exact Final|]. repeat split; try assumption; reflexivity.
Qed.
Local Opaque generated_modules generated_top.
Lemma circuit_data_ports_typed_step invalid before after phase :
 data_ports_typed (top_environment before) ->
 formal_circuit_value_iter invalid generated_modules generated_top before phase = Some after ->
 data_ports_typed (top_environment after).
Proof.
 intros Typed Step.
 destruct (flat_iteration_projection invalid before phase after Step) as [old [next [Old [Local Next]]]].
 unfold top_environment in *. rewrite Old in Typed. rewrite Next.
 exact (data_ports_typed_step (invalid nil) old old next phase Typed Local).
Qed.
Lemma circuit_data_ports_typed_iterations inputs n initial result :
 data_ports_typed (top_environment initial) ->
 circuit_formal_iterations generated_modules generated_top inputs n initial = Some result ->
 data_ports_typed (top_environment result).
Proof.
 revert initial result. induction n as [|n IH]; intros initial result Typed Steps.
 - cbn [circuit_formal_iterations] in Steps. inversion Steps; subst; exact Typed.
 - cbn [circuit_formal_iterations] in Steps.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top initial false)
   as [next|] eqn:Next; [|discriminate Steps].
   exact (IH next result (circuit_data_ports_typed_step _ initial next false Typed Next) Steps).
Qed.
Print Assumptions circuit_data_ports_typed_iterations.
