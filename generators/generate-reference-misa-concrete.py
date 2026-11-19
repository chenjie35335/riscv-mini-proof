from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low/staged-integration';s=(root/'formal/flat-low/CoreSocModel.v').read_text();qs=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
def get(kind,n):
 pat=rf'\(@{kind} VarOrder.T '+(rf'\(@Eid VarOrder.T {n}\) ' if kind=='Sfcnct' else rf'{n} ')
 m=re.search(pat,s);a=m.end();d=0
 for z in range(a,len(s)):
  d+=(s[z]=='(')-(s[z]==')')
  if not d:return s[a:z+1],bisect.bisect_right(qs,m.start())-1
h='''Require Import CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip DUTRedirectDecode.
From Coq Require Import NArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
r=h
vals={7270:(31,1<<30),7271:(9,256),7272:(9,256),7273:(13,4096),7274:(13,4352),7275:(31,1073746176),7434:(32,1073746176),7435:(32,1073746176),7436:(32,1073746176)}
r+='Definition reference_misa_word := from_N 32 1073746176.\n'
ranks={}
for n,(w,v) in vals.items():
 e,pos=get('Snode',n);deps=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',e)));ranks[n]=1+max([ranks[d] for d in deps],default=0);name=f'misa_{n}'
 r+=f'''Definition {name}_expr := {e}.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {pos} flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T {n} {name}_expr){name}_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma {name}_nonreg : has_register {n} flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_step invalid old result :
'''
 for dep in deps:
  dw,dv=vals[dep];r+=f' VM.find {dep} old=Some(Gval(Fuint {dw})(from_N {dw} {dv})) ->\n'
 r+=f''' formal_value_iter invalid flat_memories old false old flat_statements=Some result ->
 VM.find {n} result=Some(Gval(Fuint {w})(from_N {w} {v})).
Proof.
 intros {' '.join('H'+str(d) for d in deps)} Step.
 eapply formal_combinational_known_node;[exact {name}_position|exact {name}_safe|exact {name}_nonreg| |reflexivity|exact Step].
 cbn [{name}_expr eval_hfexpr_validif_policy eval_href_validif_policy].
'''
 if deps:r+=' rewrite '+' '.join('H'+str(d) for d in deps)+'.\n'
 r+=' reflexivity.\nQed.\n'
 r+=f'''Lemma {name}_history invalid history limit :
 (forall t,(t<limit)%coq_nat ->formal_value_iter invalid flat_memories(history t)false(history t)flat_statements=Some(history(S t))) ->
 forall t,({ranks[n]}<=t)%coq_nat ->(t<=limit)%coq_nat ->VM.find {n}(history t)=Some(Gval(Fuint {w})(from_N {w} {v})).
Proof.
 intros Steps [|t] Lower Upper;[lia|]. eapply {name}_step.
'''
 for dep in deps:r+=f' - apply(misa_{dep}_history invalid history limit Steps t);lia.\n'
 r+=' - apply Steps;lia.\nQed.\n'
# alias normal chain
for n,dep in [(1750,7332),(2807,1750),(7150,2807),(1820,7150)]:
 name=f'misa_{n}';kind='Snode' if n in [2807,7150] else 'Sfcnct';e,pos=get(kind,n)
 if kind=='Snode':
  r+=f'''Definition {name}_expr := {e}.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {pos} flat_statements=Some(@Qcons VarOrder.T(@Snode VarOrder.T {n} {name}_expr){name}_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
'''
 else:
  m=re.search(rf'\(@Swire VarOrder.T {n} ',s);start=bisect.bisect_right(qs,m.start())-1
  r+=f'''Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition {name}_mid := take_statements {pos-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements=Some(@Qcons VarOrder.T(@Swire VarOrder.T {n}(Gtyp(Fuint 32))){name}_decl).
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_split : {name}_decl=statement_append {name}_mid(@Qcons VarOrder.T(@Sfcnct VarOrder.T(@Eid VarOrder.T {n}){e}){name}_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute;exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories {n} {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
'''
 r+=f'''Lemma {name}_nonreg : has_register {n} flat_statements=false.
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_step invalid old result word :
 size word=32%nat ->VM.find {dep} old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old false old flat_statements=Some result ->VM.find {n} result=Some(Gval(Fuint 32)word).
Proof.
 intros Size Source Step.
'''
 if kind=='Snode':r+=f''' eapply formal_combinational_known_node;[exact {name}_position|exact {name}_safe|exact {name}_nonreg|exact Source|reflexivity|exact Step].
'''
 else:r+=f''' eapply(declared_connection_value {start} flat_statements {name}_decl {name}_mid {name}_tail {n} {dep} 32);
 [exact {name}_position|exact {name}_split|exact {name}_straight|exact {name}_mid_safe|exact {name}_tail_safe|exact {name}_nonreg|reflexivity|exact Source|apply dut_decode_adapt;exact Size|exact Step].
'''
 r+='Qed.\n'
# register certificates
n=7332;reg,start=get('Sreg',n);expr,end=get('Sfcnct',n);name='misa_register'
r+=f'''Definition {name}_reg := {reg}.
Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s=>s|None=>@Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements=Some(@Qcons VarOrder.T(@Sreg VarOrder.T 7332 {name}_reg){name}_decl).
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_split : {name}_decl=statement_append {name}_mid(@Qcons VarOrder.T(@Sfcnct VarOrder.T(@Eid VarOrder.T 7332){expr}){name}_tail).
Proof. vm_compute;reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute;exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories 7332 {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories 7332 {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound;vm_compute;reflexivity. Qed.
Lemma {name}_identity : register_identity_b 7332 flat_statements.
Proof. vm_compute;reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Theorem misa_commit invalid old result word bit :
 size word=32%nat ->VM.find 7332 old=Some(Gval(Fuint 32)word) ->
 VM.find 1515 old=Some(Gval(Fuint 1)[::bit]) ->
 VM.find 7436 old=Some(Gval(Fuint 32)reference_misa_word) ->
 VM.find 1820 old=Some(Gval(Fuint 32)word) ->
 formal_value_iter invalid flat_memories old true old flat_statements=Some result ->
 VM.find 7332 result=Some(Gval(Fuint 32)(if bit then reference_misa_word else word)).
Proof.
 intros Size Old Reset Yes No Step.
 destruct(formal_committed_uint_register_mux_observation {start} flat_statements misa_register_decl misa_register_mid misa_register_tail 7332 misa_register_reg
 (@Eref VarOrder.T(@Eid VarOrder.T 1515))(@Eref VarOrder.T(@Eid VarOrder.T 7436))(@Eref VarOrder.T(@Eid VarOrder.T 1820)) invalid flat_memories old old result(Gval(Fuint 32)word)32
 misa_register_position misa_register_split misa_register_straight misa_register_mid_safe misa_register_tail_safe Old(Logic.eq_refl _)misa_register_identity Step)as[source[value[Source[Adapt Value]]]].
 change(eval_hfexpr_with_memory flat_memories {expr} old old=Some source)in Source.
 cbn [eval_hfexpr_with_memory eval_href_with_memory]in Source.
 rewrite Reset in Source. destruct bit;cbn [is_zero eval_hfexpr_with_memory eval_href_with_memory]in Source;rewrite ?Yes ?No in Source;
 unfold eval_type_of_expr in Source;cbn [type_of_expr' eval_type_of_ref]in Source;rewrite ?Yes ?No in Source.
 - inversion Source;subst source. cbn [adapt_hvalue_as_type]in Adapt. inversion Adapt;subst value. exact Value.
 - inversion Source;subst source.
   cbn [extend_hvalue_as_type adapt_hvalue_as_type]in Adapt.
   inversion Adapt;subst value. rewrite(resize_uint_roundtrip 32 32 word Size (leqnn 32))in Value. exact Value.
Qed.
'''
(base/'ReferenceMISAConcreteNodes.v').write_text(r)
