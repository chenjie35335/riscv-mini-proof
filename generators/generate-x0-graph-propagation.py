"""Join actual node and connection outputs into the checked dependency graph."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[2]
rows=json.loads((root/'formal/flat-low/x0-dependency-ranks.json').read_text())['nodes']
connections={785,784,128,123,118,122,127,124,126,125,81,40,74,33}
out='''Require Import CoreSocModel ComparisonNodes X0DependencyRanks CheckedDependencyHistory X0ConcreteOutputCertificates X0ConcreteConnectionOutputs.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition x0_concrete_at (env : VM.t hvalue) (node : nat) : Prop :=
 exists width bits, VM.find (N.of_nat node) env = Some (Gval (Fuint width) bits).
Theorem x0_dependency_step inputs path old current result node rank dependencies :
 List.In (node, (rank, dependencies)) x0_dependency_ranks ->
 (0 < rank)%coq_nat ->
 (forall source, List.In source dependencies -> x0_concrete_at old source) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 x0_concrete_at result node.
Proof.
 intros Member Positive Sources Step. unfold x0_dependency_ranks in Member.
'''
for row in rows:
 n=row['id']; ds=row['dependencies']
 out+=' destruct Member as [Equal|Member].\n { inversion Equal; subst node rank dependencies.\n'
 if row['rank']==0:
  out+='   lia. }\n';continue
 prefix=f'x0_connection_output_{n} (formal_invalid_policy inputs path)' if n in connections else f'x0_node_output_{n} inputs path'
 out+=f'   apply ({prefix} old current result).\n'
 for i,d in enumerate(ds):
  out+=f'   - exact (Sources {d} ltac:(do {i} right; left; reflexivity)).\n'
 out+='   - exact Step. }\n'
out+=' contradiction.\nQed.\n'
out+='''Theorem x0_concrete_history_targets inputs path history limit :
 (forall time node dependencies, (time <= limit)%coq_nat ->
   List.In (node, (0%nat, dependencies)) x0_dependency_ranks -> x0_concrete_at (history time) node) ->
 (forall time, (time < limit)%coq_nat ->
   formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time, (time <= limit)%coq_nat -> (44 <= time)%coq_nat ->
 x0_concrete_at (history time) 784 /\\ x0_concrete_at (history time) 785.
Proof.
 intros Boundary Steps.
 apply (x0_checked_history_targets (fun time node => x0_concrete_at (history time) node) limit Boundary).
 intros time node rank dependencies Within Member Positive Sources.
 exact (x0_dependency_step inputs path (history time) (history time) (history (S time)) node rank dependencies
 Member Positive Sources (Steps time Within)).
Qed.
Print Assumptions x0_concrete_history_targets.
'''
generated_path = root/'formal/flat-low/staged-integration/X0ConcreteGraphPropagation.v'
generated_text = out
if not generated_path.exists() or generated_path.read_text() != generated_text:
    generated_path.write_text(generated_text)
print(f'Generated graph propagation with {len(rows)} entries; compilation requires completed output certificates.')
