"""Emit one ALU stability table and batch transfer certificate; preserve public proofs."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2];d=root/'formal/flat-low/staged-integration';s=(d/'DataAddressDependencyRanks.v').read_text()
g={int(n):(int(r),list(map(int,re.findall(r'\d+',ds)))) for n,r,ds in re.findall(r'\((\d+), \((\d+), \[([^]]*)\]\)\)',s)}
base={86,87,88,89,7748,7749,7816,7819};seen=set()
def walk(n):
 if n in seen or n in base:return
 seen.add(n)
 for x in g[n][1]:walk(x)
for n in [1151,1152,1153,1155,1161]:walk(n)
order=sorted(seen,key=lambda n:(g[n][0],n));expr=(d/'DataAddressPositionCertificate.v').read_text();nodes=list(map(int,re.findall(r'\(N.of_nat (\d+), address_expr_',expr)))
conn=(d/'DataAddressConnectionCertificates.v').read_text()
out=['''Require Import CoreSocModel ComparisonNodes DataAddressPositionCertificate DataAddressSafetyCertificate
 DataAddressOutputCertificates DataAddressExpressionCertificates DataAddressConnectionCertificates
 ReferenceControlNodeGeneric ReferenceControlGroundExpressions ReferenceControlGroundOperations
 SelectedNodeSafety FormalDeclaredConnectionCongruence X0DependencyRanks DependencyRankSoundness.
From Coq Require Import NArith ZArith List Lia Arith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Definition alu_stability_ground env node := exists ground bits, VM.find (N.of_nat node) env = Some (Gval ground bits).
Definition alu_stability_roots : seq nat := [::86%nat;87%nat;88%nat;89%nat;7748%nat;7749%nat;7816%nat;7819%nat].
''']
seq=lambda ns:'[::'+';'.join(f'{n}%nat'for n in ns)+']'
entries=[f'({n}%nat,(0%nat,[::]))'for n in sorted(base)]+[f'({n}%nat,({g[n][0]}%nat,{seq(g[n][1])}))'for n in order]
out += ['Definition alu_stability_table : list (nat * (nat * list nat)) := [::\n'+';\n'.join(entries)+'].\n','Lemma alu_stability_ranks : dependency_ranks_valid alu_stability_table = true.\nProof. vm_compute;reflexivity. Qed.\n', '''Theorem alu_stability_transfer_batch inputs path left right next_left next_right :
 formal_value_iter (formal_invalid_policy inputs path) flat_memories left false left flat_statements = Some next_left ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories right false right flat_statements = Some next_right ->
 List.Forall (fun entry => let '(node,(rank,deps)) := entry in (0 < rank)%coq_nat ->
 (forall source, List.In source deps -> alu_stability_ground left source /\\ VM.find (N.of_nat source) left = VM.find (N.of_nat source) right) ->
 alu_stability_ground next_left node /\\ VM.find (N.of_nat node) next_left = VM.find (N.of_nat node) next_right) alu_stability_table.
Proof.
 intros Left Right. unfold alu_stability_table.
''']
for n in sorted(base):out+=[' constructor. { cbn;intros Positive Sources;lia. }\n']
for n in order:
 deps=g[n][1]
 out+=[' constructor. { cbn [fst snd]. intros Positive Sources.\n']
 for dep in deps:out +=[f' destruct (Sources {dep}%nat ltac:(cbn;tauto)) as [G{dep} E{dep}].\n']
 out+=[' split.\n']
 if n in nodes:
  out +=[f' - exact (data_address_node_output_{n} inputs path left left next_left '+' '.join(f'G{x}'for x in deps)+' Left).\n']
  out +=[f' - destruct (selected_node_safe_position flat_memories flat_statements data_address_node_offsets flat_statements data_address_expected_nodes {n} address_expr_{n}\n data_address_actual_node_expressions data_address_actual_nodes_safe ltac:(apply (List.nth_error_In data_address_expected_nodes {nodes.index(n)}%nat);vm_compute;reflexivity)) as [count [tail [Position [Safe Nonreg]]]].\n']
  out +=[f' eapply (reference_control_node_congruent count tail {n} address_expr_{n} inputs path left right next_left next_right Position Safe Nonreg); [| |exact Left|exact Right].\n']
  for dep in deps:out +=[f' + destruct G{dep} as [g{dep} [b{dep} G{dep}]].\n' if dep==deps[0] else f'   destruct G{dep} as [g{dep} [b{dep} G{dep}]].\n']
  if not deps:out+=[' + ']
  out +=[f'   unfold address_expr_{n}. repeat first [apply rc_const|apply rc_unary|apply rc_binary|apply rc_cast|apply rc_mux|apply rc_validif|eapply rc_ref;[eassumption|eexists;reflexivity]].\n']
  out +=[f' + intros site. cbn [address_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].\n']
  # type_of_expr also observes mux branch refs
  out +=['   unfold eval_type_of_expr; cbn [type_of_expr\' eval_type_of_ref].\n']
  if deps:out +=['   rewrite '+' '.join('E'+str(x)for x in deps)+'. reflexivity. }\n']
  else:out+=['   reflexivity. }\n']
 else:
  m=re.search(rf'data_address_connection_{n}_position : straight_drop (\d+)',conn);assert m,n
  src=deps[0];width=int(re.search(rf'@Swire VarOrder.T {n} \(Gtyp \(Fuint (\d+)\)',conn).group(1));prefix=f'data_address_connection_{n}'
  out +=[f' - destruct ({prefix}_output (formal_invalid_policy inputs path) left left next_left G{src} Left) as [bits Value]. exists (Fuint {width}),bits;exact Value.\n']
  out +=[f' - exact (declared_connection_congruence {m.group(1)} flat_statements {prefix}_decl {prefix}_mid {prefix}_tail {n} {src} {width} (formal_invalid_policy inputs path) flat_memories left right next_left next_right\n '+ ' '.join(prefix+'_'+x for x in ['position','split','straight','mid_safe','tail_safe','nonregister'])+f' (Logic.eq_refl _) E{src} Left Right). }}\n']
out+=[' constructor.\nQed.\n']
path=d/'ALUInputStability.v';marker='(* Stable public history interface. *)';old=path.read_text() if path.exists() else '';tail=old[old.index(marker):] if marker in old else marker+'\n';path.write_text(''.join(out)+tail)
print(len(order),'transfer cases;',len(nodes),'existing node positions')
