Require Import CoreSocModel FormalLocalHistory FormalInstructionPortInvariant.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque generated_modules generated_top.
Theorem instruction_iterations_enabled inputs n before after :
 instruction_port_typed (top_environment before) ->
 circuit_formal_iterations generated_modules generated_top inputs (S n) before = Some after ->
 read_memory_port_field (top_environment after) (N.of_nat 9176) (N.of_nat 0) (N.of_nat 1) = Some (Gval (Fuint 1) [::true]).
Proof.
 revert before after. induction n as [|n IH]; intros before after Typed Steps.
 - cbn [circuit_formal_iterations] in Steps.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top before false) as [next|] eqn:Step; [|discriminate Steps].
   inversion Steps; subst after.
   exact (proj2 (circuit_instruction_port_step _ before false next Typed Step)).
 - change (match formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top before false with
   | Some next => circuit_formal_iterations generated_modules generated_top inputs (S n) next
   | None => None end = Some after) in Steps.
   destruct (formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top before false) as [next|] eqn:Step; [|discriminate Steps].
   exact (IH next after (proj1 (circuit_instruction_port_step _ before false next Typed Step)) Steps).
Qed.
Print Assumptions instruction_iterations_enabled.
