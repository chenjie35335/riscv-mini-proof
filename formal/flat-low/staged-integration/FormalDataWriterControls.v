Require Import FormalDataWriterIteration FormalDataPortsInvariant DataReaderEnableConnections ComparisonNodes FormalCircuitDataCommit.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_writer_sources_concrete env :=
 (exists width bits, VM.find 9230 env = Some (Gval (Fuint width) bits)) /\
 (exists width bits, VM.find 9232 env = Some (Gval (Fuint width) bits)) /\
 (exists width bits, VM.find 9233 env = Some (Gval (Fuint width) bits)).
Definition data_writer_controls_concrete env := exists address enable mask,
 read_memory_port_field env 9178 0 0 = Some (Gval (Fuint 16) address) /\
 read_memory_port_field env 9178 0 1 = Some (Gval (Fuint 1) enable) /\
 read_memory_port_field env 9178 0 3 = Some (Gval (Fuint 1) mask).
Theorem data_writer_controls_step invalid phase old current result :
 data_ports_typed old -> data_writer_sources_concrete old ->
 formal_value_iter invalid flat_memories old phase current flat_statements = Some result ->
 data_writer_controls_concrete result.
Proof.
 intros Typed [[aw [ab SA]] [[ew [eb SE]] [mw [mb SM]]]] Step.
 unfold data_ports_typed in Typed.
 destruct Typed as [wa [we [wc [wm [wd [a2 [e2 [c2 [m2 [d2 [a3 [e3 [c3 [m3 [d3 [a4 [e4 [c4 [m4 [d4 [a5 [e5 [c5 [m5 [d5 [a1 [e1 [c1 [m1 [d1 [Value [T_a2 [T_e2 [T_c2 [T_a3 [T_e3 [T_c3 [T_a4 [T_e4 [T_c4 [T_a5 [T_e5 [T_c5 [T_a1 [T_e1 [T_c1 [T_d1 [T_wa [T_we [T_wc T_wm]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
 destruct (data_writer_iteration_concrete invalid phase old current result wa we wc wm wd aw ab ew eb mw mb a2 e2 c2 m2 d2 a3 e3 c3 m3 d3 a4 e4 c4 m4 d4 a5 e5 c5 m5 d5 a1 e1 c1 m1 d1
 Value T_a2 T_e2 T_c2 T_a3 T_e3 T_c3 T_a4 T_e4 T_c4 T_a5 T_e5 T_c5 T_a1 T_e1 T_c1 T_d1 T_wa T_we T_wc T_wm SA SE SM Step) as [na2 [nc2 [na3 [nc3 [na4 [nc4 [na5 [nc5 [na1 [nc1 [clock0 [data0 [Clock0 [NA2 [NA3 [NA4 [NA5 [NA1 [NC2 [NC3 [NC4 [NC5 [NC1 Final]]]]]]]]]]]]]]]]]]]]]]].
 unfold data_writer_controls_concrete, read_memory_port_field. rewrite Final.
 do 3 eexists. repeat split; reflexivity.
Qed.
Theorem data_commit_ready_from_controls env :
 data_writer_controls_concrete env ->
 (exists width bits, VM.find 9234 env = Some (Gval (Fuint width) bits)) ->
 data_commit_ready env.
Proof.
 intros [address [enable [mask [Address [Enable Mask]]]]] [width [bits Source]].
 exists width, bits, 1%nat, enable, 1%nat, mask, 16%nat, address.
 repeat split; assumption.
Qed.
Print Assumptions data_writer_controls_step.
