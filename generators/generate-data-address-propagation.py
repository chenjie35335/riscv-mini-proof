"""Join checked local transfers with rank induction; retain boundary/type obligations."""
import json
import re
from pathlib import Path
root = Path(__file__).resolve().parents[2]
rows = json.loads((root / 'formal/flat-low/data-address-dependency-ranks.json').read_text())['nodes']
model = (root / 'formal/flat-low/CoreSocModel.v').read_text()
out = '''Require Import CoreSocModel ComparisonNodes DataAddressDependencyRanks DataAddressCheckedHistory CheckedDependencyHistory DataAddressOutputCertificates DataAddressConnectionCertificates DataAddressUnaryConnection.
From Coq Require Import ZArith List Arith Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition data_address_ground_at (env : VM.t hvalue) (node : nat) : Prop :=
 exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Theorem data_address_dependency_transfers inputs path old current result :
 (exists width bits, VM.find (N.of_nat 851) old = Some (Gval (Fuint width) bits)) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 List.Forall (fun entry => let '(node, (rank, dependencies)) := entry in
 (0 < rank)%coq_nat ->
 (forall source, List.In source dependencies -> data_address_ground_at old source) ->
 data_address_ground_at result node) data_address_dependency_ranks.
Proof.
 intros Typed851 Step. unfold data_address_dependency_ranks.
'''
for row in rows:
    n, ds = row['id'], row['dependencies']
    out += ' constructor.\n { cbn [fst snd]. intros Positive Sources.\n'
    if row['rank'] == 0:
        out += '   lia. }\n'
        continue
    is_node = re.search(r'\(@Snode VarOrder.T ' + str(n) + r' ', model)
    if is_node:
        out += f'   apply (data_address_node_output_{n} inputs path old current result).\n'
        for i, source in enumerate(ds):
            if n in (884, 919) and source == 851:
                out += '   - exact Typed851.\n'
            else:
                out += f'   - exact (Sources {source} ltac:(do {i} right; left; reflexivity)).\n'
        out += '   - exact Step. }\n'
    else:
        out += f'   destruct (data_address_connection_{n}_output (formal_invalid_policy inputs path) old current result\n'
        out += f'     (Sources {ds[0]} ltac:(left; reflexivity)) Step) as [bits Lookup].\n'
        out += '   unfold data_address_ground_at. do 2 eexists; exact Lookup. }\n'
out += ''' constructor.
Qed.
Theorem data_address_ground_history inputs path history limit :
 (forall time node dependencies, (time <= limit)%coq_nat ->
   List.In (node, (0%nat, dependencies)) data_address_dependency_ranks -> data_address_ground_at (history time) node) ->
 (forall time, (time < limit)%coq_nat ->
   exists width bits, VM.find (N.of_nat 851) (history time) = Some (Gval (Fuint width) bits)) ->
 (forall time, (time < limit)%coq_nat ->
   formal_value_iter (formal_invalid_policy inputs path) flat_memories (history time) false (history time) flat_statements = Some (history (S time))) ->
 forall time node, (time <= limit)%coq_nat -> (80 <= time)%coq_nat ->
 List.In node data_address_targets -> data_address_ground_at (history time) node.
Proof.
 intros Boundary Typed851 Steps.
 apply (data_address_checked_history_targets (fun time node => data_address_ground_at (history time) node) limit Boundary).
 intros time node rank dependencies Within Member Positive Sources.
 pose proof (data_address_dependency_transfers inputs path (history time) (history time) (history (S time))
   (Typed851 time Within) (Steps time Within)) as Transfers.
 rewrite List.Forall_forall in Transfers.
 exact (Transfers (node, (rank, dependencies)) Member Positive Sources).
Qed.
Print Assumptions data_address_ground_history.
'''
p = root / 'formal/flat-low/staged-integration/DataAddressGraphPropagation.v'
if not p.exists() or p.read_text() != out:
    p.write_text(out)
print(f'Generated {len(rows)} dependency transfer cases and rank-80 history theorem.')
