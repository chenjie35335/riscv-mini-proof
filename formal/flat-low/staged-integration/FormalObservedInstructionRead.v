Require Import CoreSocModel FormalLocalHistory InstructionMemoryRead FormalInstructionStorageInvariant FormalInstructionStorageInitialization FormalObservedInstructionPort.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Theorem observed_instruction_read_concrete memory inputs k states address width value :
 generated_observe memory inputs k = Some states ->
 read_memory_port_field (top_environment states) 9176 0 0 = Some (Gval (Fuint width) address) ->
 eval_memory_reader_data ComparisonNodes.flat_memories 9176 0 (top_environment states) (top_environment states) = Some value ->
 exists bits, value = Gval (Fuint 32) bits.
Proof.
 intros Observe Address Read.
 destruct (observed_instruction_storage_concrete memory inputs k states Observe) as [values [Storage Concrete]].
 destruct (observed_instruction_port memory inputs k states Observe) as [Typed Enable].
 exact (instruction_memory_read_concrete (top_environment states) (top_environment states)
 values [::true] address width value Storage Enable (Logic.eq_refl _) Address Concrete Read).
Qed.
Print Assumptions observed_instruction_read_concrete.
