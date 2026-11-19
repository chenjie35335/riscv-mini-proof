Require Import CoreSocModel FormalLocalHistory StagedFlatCircuitIteration InstructionPortConnection FormalInstructionPortIteration.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition instruction_port_typed env := exists address enable clock mask data,
 VM.find 9176 env = Some (instruction_port_bundle address enable clock mask data) /\
 type_of_val address = Gtyp (Fuint 16) /\ type_of_val enable = Gtyp (Fuint 1) /\
 type_of_val clock = Gtyp Fclock /\ type_of_val data = Gtyp (Fuint 32).
Lemma instruction_port_iteration_typed invalid old phase current result :
 instruction_port_typed old ->
 formal_value_iter invalid ComparisonNodes.flat_memories old phase current ComparisonNodes.flat_statements = Some result ->
 instruction_port_typed result /\ read_memory_port_field result 9176 0 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros [address [enable [clock [mask [data [Old [Address [Enable [Clock Data]]]]]]]]] Step.
 destruct (instruction_port_iteration invalid old phase current result address enable clock mask data Old Address Enable Clock Data Step)
 as [next_address [next_clock [NextAddress [NextClock Result]]]].
 split.
 - exists next_address, (Gval (Fuint 1) [::true]), next_clock, mask, data.
   split; [exact Result|]. split; [exact NextAddress|]. split; [reflexivity|]. split; assumption.
 - exact (instruction_port_enable result next_address (Gval (Fuint 1) [::true]) next_clock mask data Result).
Qed.
Local Opaque generated_modules generated_top.
Lemma circuit_instruction_port_step invalid before phase after :
 instruction_port_typed (top_environment before) ->
 formal_circuit_value_iter invalid generated_modules generated_top before phase = Some after ->
 instruction_port_typed (top_environment after) /\
 read_memory_port_field (top_environment after) 9176 0 1 = Some (Gval (Fuint 1) [::true]).
Proof.
 intros Typed Step. destruct (flat_iteration_projection invalid before phase after Step)
 as [old [next [Old [LocalStep Next]]]].
 unfold top_environment in Typed |- *. rewrite Old in Typed. rewrite Next.
 exact (instruction_port_iteration_typed _ old phase old next Typed LocalStep).
Qed.
Theorem circuit_instruction_port_iterations inputs n before after :
 instruction_port_typed (top_environment before) ->
 circuit_formal_iterations generated_modules generated_top inputs n before = Some after ->
 instruction_port_typed (top_environment after).
Proof.
 revert before after. induction n as [|n IH]; intros before after Typed Steps.
 - cbn [circuit_formal_iterations] in Steps. inversion Steps; subst after. exact Typed.
 - cbn [circuit_formal_iterations] in Steps.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top before false)
   as [next|] eqn:Step; [|discriminate Steps].
   apply (IH next after); [|exact Steps].
   exact (proj1 (circuit_instruction_port_step (formal_invalid_policy inputs) before false next Typed Step)).
Qed.
Print Assumptions circuit_instruction_port_iterations.
