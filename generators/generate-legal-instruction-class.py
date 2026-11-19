from pathlib import Path
import re,json
root=Path(__file__).resolve().parents[2];p=root/'formal/flat-low/staged-integration';model=(root/'formal/flat-low/CoreSocModel.v').read_text()
src=(root/'formal/generators/generate-nop-kill-values.py').read_text();exec(src[src.index('def parse(s):'):src.index('values={7748:')])
expr={};positions={}
# Position is Qcons index, including declarations and wires.
for m in re.finditer(r'\(@Snode VarOrder.T (\d+) ',model):
 n=int(m[1])
 if not 9029<=n<=9138:continue
 d=1;j=m.end()
 while d:
  d+=(model[j]=='(')-(model[j]==')');j+=1
 expr[n]=model[m.end():j-1]
 positions[n]=model[:m.start()].count('(@Qcons VarOrder.T ')
# Qcons directly containing node was already counted.
positions={n:v-1 for n,v in positions.items()}
ids=sorted(expr);deps={n:list(map(int,re.findall(r'@Eid VarOrder.T (\d+)',e)))for n,e in expr.items()};rank={44:0};words={44:'instruction'};width={44:32};rows=[]
def const(a):return int(a[2][1]),sum((b=='true')<<i for i,b in enumerate(a[3]))
for n in ids:
 a=parse(expr[n]);op=a[2];rank[n]=1+max(rank[x]for x in deps[n])
 if op=='Band':
  w,v=const(a[4]);width[n]=32;words[n]=f'andB instruction (from_N {w} {v})'
 elif op==['Bcomp','Beq']:
  cw,code=const(a[3]);masknode=deps[n][0];mw,mask=const(parse(expr[masknode])[4]);width[n]=1;words[n]=f'[::N.eqb (N.land (to_N instruction) {mask}) {code}]';rows.append((n,mw,mask,cw,code))
 else:
  assert op=='Bor';width[n]=1;words[n]=f'[::(legal_class_bit_{deps[n][0]} instruction)||(legal_class_bit_{deps[n][1]} instruction)]'
out='''Require Import CoreSocModel ComparisonNodes ReferenceRedirectSpine SelectedNodeSafety X0ConcretePositionCertificate X0ConcreteSafetyCertificate.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From nbits Require Import NBits.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths Firrtl_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
for n,e in expr.items():out+=f'Definition legal_class_expr_{n} := {e}.\n'
out+='Definition legal_class_nodes := [::'+ ';'.join(f'({n},legal_class_expr_{n})'for n in ids)+'].\n'
prev=-1;offs=[]
for n in ids:offs.append(positions[n]-prev-1);prev=positions[n]
out+='Definition legal_class_offsets := [::'+';'.join(f'{n}%nat'for n in offs)+'].\n'
out+='Lemma legal_class_positions : select_node_offsets legal_class_offsets flat_statements = Some legal_class_nodes.\nProof. vm_compute;reflexivity. Qed.\nLemma legal_class_safety : selected_node_safety flat_memories flat_statements legal_class_offsets flat_statements=true.\nProof. vm_compute;reflexivity. Qed.\nLocal Opaque flat_statements flat_memories generated_modules generated_top.\n'
for n in ids:
 if width[n]==1:out+=f'Definition legal_class_bit_{n} (instruction:bits) := '+words[n][3:-1]+'.\n'
 out+=f'Definition legal_class_word_{n} (instruction:bits) := {words[n]}.\n'
out+='Definition legal_class_value (node:nat) instruction : hvalue := if Nat.eqb node 44 then Gval(Fuint 32)instruction else match Nat.sub node 9029 with\n'+''.join(f'|{n-9029}%nat=>Gval(Fuint {width[n]})(legal_class_word_{n} instruction)\n'for n in ids)+'|_=>Gval(Fuint 1)[::false] end.\n'
out+='Definition legal_class_rank (node:nat) := match Nat.sub node 9029 with\n'+''.join(f'|{n-9029}%nat=>{rank[n]}%nat\n'for n in ids)+'|_=>0%nat end.\n'
out+='Definition legal_class_dependencies (node:nat) := match Nat.sub node 9029 with\n'+''.join(f'|{n-9029}%nat=>[::'+ ';'.join(f'{d}%nat'for d in deps[n])+']\n'for n in ids)+'|_=>[::] end.\n'
out+='Lemma legal_class_step index invalid old result instruction : (index<110)%coq_nat ->\n (forall dep,List.In dep(legal_class_dependencies(9029+index)%nat)->VM.find(N.of_nat dep)old=Some(legal_class_value dep instruction))->\n formal_value_iter invalid flat_memories old false old flat_statements=Some result ->\n VM.find(N.of_nat(9029+index)%nat)result=Some(legal_class_value(9029+index)%nat instruction).\nProof. intros Bound Values Step.\n'
for n in ids:
 out+='destruct index as[|index].\n{\n'
 for d in deps[n]:out+=f'pose proof(Values {d}%nat ltac:(vm_compute;tauto))as H{d}.\n'
 out+=f'eapply(reference_redirect_ground_step legal_class_offsets legal_class_nodes {n} legal_class_expr_{n});[exact legal_class_positions|exact legal_class_safety|apply(List.nth_error_In legal_class_nodes {n-9029}%nat);reflexivity| |exact Step].\nintros site. cbn [legal_class_expr_{n} eval_hfexpr_validif_policy eval_href_validif_policy].\nrewrite '+' '.join(f'H{d}'for d in deps[n])+'.\ncbn [legal_class_value].\n'
 a=parse(expr[n]);op=a[2]
 if op==['Bcomp','Beq']:
  _,mw,mask,cw,code=next(r for r in rows if r[0]==n)
  out+=f'change(eval_binop(Bcomp Beq)(Gval(Fuint {cw})(from_N {cw} {code}))(Gval(Fuint(maxn 32 {mw}))(andB instruction(from_N {mw} {mask})))=Some(Gval(Fuint 1)(legal_class_word_{n} instruction))).\nrewrite redirect_mask_decode. reflexivity. }}\n'
 elif op=='Bor':
  ds=deps[n];out+=f'change(eval_binop Bor (Gval(Fuint 1)[::legal_class_bit_{ds[0]} instruction])(Gval(Fuint 1)[::legal_class_bit_{ds[1]} instruction])=Some(Gval(Fuint 1)[::legal_class_bit_{ds[0]} instruction || legal_class_bit_{ds[1]} instruction])).\ndestruct(legal_class_bit_{ds[0]} instruction),(legal_class_bit_{ds[1]} instruction);reflexivity. }}\n'
 else:out+='reflexivity. }\n'
out+='lia. Qed.\n'
f=p/'LegalInstructionClass.v';marker='(* Semantic history composition. *)';manual=f.read_text().split(marker,1)[1]if f.exists()and marker in f.read_text()else'\n';f.write_text(out+marker+manual)
(root/'formal/flat-low/legal-instruction-class-map.json').write_text(json.dumps({'rows':rows,'rank':rank[9138],'input':44,'names':'ADDI SLTI SLTIU ANDI ORI XORI SLLI SRLI SRAI LUI AUIPC ADD SLT SLTU AND OR XOR SLL SRL SUB SRA JAL JALR BEQ BNE BLT BLTU BGE BGEU LB LH LW LBU LHU SB SH SW'.split()},indent=2)+'\n')
print(len(ids),rank[9138],positions[9029],len(rows))
