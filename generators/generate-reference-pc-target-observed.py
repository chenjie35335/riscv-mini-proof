"""Compose the existing decoder/comparison/alignment semantics with target arithmetic."""
from pathlib import Path
p=Path(__file__).resolve().parents[2]/'formal/flat-low/staged-integration'
src=(p/'ReferenceRedirectSemantics.v').read_text()
head=src[:src.index('(* Six-input')]
head+='Require Import ReferenceRedirectSemantics ReferencePCTargetSemantics ReferencePCTargetHistory ExceptionPCPayloadNodes.\nFrom nbits Require Import NBits.\n'
s=head+'Definition reference_pc_target_guards instruction rs1 rs2 immediate pc csr (node:VarOrder.T) :bool :=\n match node with\n'
for n,code in [(1974,28771),(1980,20579),(1986,24675),(1992,16483),(1998,4195),(2004,99),(2010,103)]:s+=f' | {n} =>N.eqb(N.land instruction 28799){code}\n'
s+=' | 2357 =>N.eqb(N.land instruction 127)111\n'
for n,e in [(2806,'N.leb rs2 rs1'),(2830,'Z.leb(reference_redirect_signed rs2)(reference_redirect_signed rs1)'),(2850,'N.ltb rs1 rs2'),(2872,'Z.ltb(reference_redirect_signed rs1)(reference_redirect_signed rs2)'),(2892,'negb(N.eqb rs1 rs2)'),(2912,'N.eqb rs1 rs2')]:s+=f' | {n} =>{e}\n'
s+=' | 2949 =>reference_redirect_aligned(N.testbit csr 2)(N.clearbit(rs1+immediate)0)\n | _ =>reference_redirect_aligned(N.testbit csr 2)(pc+immediate)\n end.\n'
s+='Definition reference_pc_target_function instruction rs1 rs2 immediate pc csr :=reference_pc_target_value(reference_pc_target_guards(to_N instruction)(to_N rs1)(to_N rs2)(to_N immediate)(to_N pc)(to_N csr))pc immediate rs1.\n'
a=src.index('Theorem reference_redirect_function_history');b=src.index('\nRequire Import FormalObservedHistory',a);f=src[a:b].replace('reference_redirect_function_history','reference_pc_target_function_history').replace('(127 <= time)','(225 <= time)')
x=f.index(' VM.find 6507 (history time)');y=f.index('Proof.',x);f=f[:x]+''' VM.find 6508(history time)=Some(Gval(Fuint 32)(reference_pc_target_function instruction rs1 rs2 immediate pc csr)).
'''+f[y:]
f=f.replace('Resets Steps Lower Upper','Resets Steps ltac:(lia) Upper')
x=f.index(' rewrite <- (reference_redirect_guards_normalize');f=f[:x]+''' assert(PC2812:VM.find 2812(history time)=Some(Gval(Fuint 32)pc)).
 { rewrite(reference_control_stable_2812_history inputs path history limit reset Resets Steps time(S time)ltac:(lia)ltac:(lia)ltac:(lia)ltac:(lia)).
 exact(exception_pc_2812_value _ (history time)(history time)(history(S time))pc PcAlias(Steps time Upper)). }
 unfold reference_pc_target_function. apply(reference_pc_target_semantics inputs path history limit reset time _ pc immediate rs1 Resets Steps Lower Upper PcSize Rs1Size PC2812 Immediate Rs1).
 intros node Member. cbn[reference_pc_target_guard_nodes List.In]in Member.
 repeat destruct Member as[<-|Member];try contradiction;cbn[reference_pc_target_guards];assumption.
Qed.
'''
f=f.replace('intros Resets Steps ltac:(lia) Upper','intros Resets Steps Lower Upper')
s+='Require Import ReferenceRedirectSemantics.\n'+f
x=src.index('Require Import FormalObservedHistory',b);f=src[x:].replace('reference_redirect_function_observed','reference_pc_target_function_observed').replace('reference_redirect_function_history','reference_pc_target_function_history').replace('reference_control_stable_6507_history','reference_pc_target_6508_stable')
x=f.index(' VM.find 6507 (top_environment observed)');y=f.index('Proof.',x);f=f[:x]+''' VM.find 6508(top_environment observed)=Some(Gval(Fuint 32)(reference_pc_target_function instruction rs1 rs2 immediate pc csr)).
'''+f[y:]
s+=f
(p/'ReferencePCTargetObserved.v').write_text(s)
