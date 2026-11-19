Require Import FormalDataReadersIteration FormalDataReadersInvariant FormalLocalHistory ComparisonNodes.
From Coq Require Import ZArith List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Definition data_reader_sources_concrete env := forall node,
 List.In node [::9186;9194;9202;9210;9221] -> exists width bits, VM.find node env = Some (Gval (Fuint width) bits).
Definition data_reader_addresses_concrete env := forall port,
 List.In port [::1;2;3;4;5] -> exists bits, read_memory_port_field env 9178 port 0 = Some (Gval (Fuint 16) bits).
Theorem data_reader_addresses_step invalid old current result phase :
 data_readers_typed old -> data_reader_sources_concrete old ->
 formal_value_iter invalid flat_memories old phase current flat_statements = Some result ->
 data_reader_addresses_concrete result.
Proof.
 intros Typed Sources Step. unfold data_readers_typed in Typed.
 destruct Typed as [p0 [a2 [e2 [c2 [m2 [d2 [a3 [e3 [c3 [m3 [d3 [a4 [e4 [c4 [m4 [d4 [a5 [e5 [c5 [m5 [d5 [a1 [e1 [c1 [m1 [d1 [Value [A2 [E2 [C2 [A3 [E3 [C3 [A4 [E4 [C4 [A5 [E5 [C5 [A1 [E1 [C1 D1]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
 destruct (Sources 9186 (or_introl (Logic.eq_refl _))) as [w2 [b2 S2]].
 destruct (Sources 9194 (or_intror (or_introl (Logic.eq_refl _)))) as [w3 [b3 S3]].
 destruct (Sources 9202 (or_intror (or_intror (or_introl (Logic.eq_refl _))))) as [w4 [b4 S4]].
 destruct (Sources 9210 (or_intror (or_intror (or_intror (or_introl (Logic.eq_refl _)))))) as [w5 [b5 S5]].
 destruct (Sources 9221 (or_intror (or_intror (or_intror (or_intror (or_introl (Logic.eq_refl _))))))) as [w1 [b1 S1]].
 destruct (data_readers_iteration_concrete invalid phase old current result p0
 a2 e2 c2 m2 d2 w2 b2 a3 e3 c3 m3 d3 w3 b3 a4 e4 c4 m4 d4 w4 b4 a5 e5 c5 m5 d5 w5 b5 a1 e1 c1 m1 d1 w1 b1
 Value A2 E2 C2 S2 A3 E3 C3 S3 A4 E4 C4 S4 A5 E5 C5 S5 A1 E1 C1 S1 D1 Step)
 as [nc2 [nc3 [nc4 [nc5 [nc1 [updated [NC2 [NC3 [NC4 [NC5 [NC1 Final]]]]]]]]]]].
 unfold data_reader_addresses_concrete. intros port Member. cbn [List.In] in Member.
 repeat destruct Member as [Same|Member]; try (subst port; unfold read_memory_port_field; rewrite Final; eexists; reflexivity).
 contradiction.
Qed.
Print Assumptions data_reader_addresses_step.
