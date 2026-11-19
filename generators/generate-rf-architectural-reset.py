"""Actual shared-reset RF witnesses for flattened implementation/reference banks."""
from pathlib import Path
import re,json,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';p=base/'staged-integration';model=(base/'CoreSocModel.v').read_text()
qpositions=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',model)]
def statement_position(start):return bisect.bisect_left(qpositions,start)-1
def term(start):
 d=0
 for e in range(start,len(model)):
  d+=(model[e]=='(')-(model[e]==')')
  if not d:return model[start:e+1]
def find(pat):
 m=re.search(pat,model);assert m,pat
 return m,statement_position(m.start())
nodes={};conns={};regs={}
for kind,pat,target in [('node',r'\(@Snode VarOrder.T (\d+) ',nodes),('conn',r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T (\d+)\) ',conns),('reg',r'\(@Sreg VarOrder.T (\d+) ',regs)]:
 for m in re.finditer(pat,model):target[int(m[1])]=(term(m.end()),statement_position(m.start()))
header='''Require Import CoreSocModel ComparisonNodes ScalarNodeFrames FormalTypedNodeFrames RegisterInvariants FormalTypedNodeEquation FormalDeclaredConnection FormalStatementSegments RegisterCommitCertificate FormalUIntRegisterCommitSource SelectedUIntMuxIdentity UIntResizeRoundtrip.
From Coq Require Import ZArith List Lia.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From nbits Require Import NBits.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
def write(name,s):
 path=p/(name+'.v')
 if not path.exists() or path.read_text()!=s:path.write_text(s)
def wire_cert(n):
 expr,end=conns[n];_,start=find(r'\(@Swire VarOrder.T '+str(n)+r' ');name=f'rfa_wire_{n}'
 return f'''Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Swire VarOrder.T {n} (Gtyp (Fuint 32))) {name}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_split : {name}_decl = statement_append {name}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {n}) {expr}) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute. exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories {n} {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonreg : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
''',name,start
jointids=list(map(int,re.findall(r'\((\d+),joint_update_expr_', (p/'JointUpdateNodePositions.v').read_text())))
for batch in range(8):
 s=header
 if batch>=4:s=s.replace('Require Import CoreSocModel','Require Import SelectedNodeSafety JointUpdateNodePositions JointUpdateExpressionCertificates JointUpdateConnectionCertificates CoreSocModel')
 for i in range(4*batch,4*batch+4):
  leaf=8089+2*i;leafexpr,leafpos=nodes[leaf]
  s+=f'''Definition rfa_reset_word_{i} inputs path := proj1_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil {leafpos} 0 nil)) nil 32).
Lemma rfa_reset_word_{i}_size inputs path : size (rfa_reset_word_{i} inputs path) = 32%nat.
Proof. exact (proj2_sig (formal_symbolic_inputs inputs path (validif_source_address (validif_raw_address nil {leafpos} 0 nil)) nil 32)). Qed.
'''
  if i==0:
   s=s[:s.index('Definition rfa_reset_word_0')]+'''Definition rfa_reset_word_0 (inputs : formal_inputs) (path : SVM.key) := zeros 32.
Lemma rfa_reset_word_0_size inputs path : size (rfa_reset_word_0 inputs path) = 32%nat.
Proof. reflexivity. Qed.
'''
  order=[leaf,leaf+1,787+i,1085+i,1482+i,1672+i,7369+2*i,7370+2*i];ranks={}
  for n in order:
   name=f'rfa_node_{n}';isnode=n in nodes;expr,pos=nodes[n] if isnode else conns[n]
   deps=list(map(int,re.findall(r'\(@Eid VarOrder.T (\d+)\)',expr)));assert len(deps)<=1
   rank=1 if not deps else ranks[deps[0]]+1;ranks[n]=rank
   cached_node=batch>=4 and n in jointids and deps
   if cached_node:
    s+=f'Definition {name}_expr := joint_update_expr_{n}.\n'
   elif isnode:
    s+=f'''Definition {name}_expr := {expr}.
Definition {name}_tail := match straight_drop {pos+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Lemma {name}_position : straight_drop {pos} flat_statements = Some (@Qcons VarOrder.T (@Snode VarOrder.T {n} {name}_expr) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_nonreg : has_register {n} flat_statements = false.
Proof. vm_compute. reflexivity. Qed.
'''
   elif batch>=4 and 787<=n<=818:
    _,start=find(r'\(@Swire VarOrder.T '+str(n)+r' ');name=f'joint_update_connection_{n}'
    s+=f'Lemma {name}_nonreg : has_register {n} flat_statements = false.\nProof. exact {name}_nonregister. Qed.\n'
   else:cert,name,start=wire_cert(n);s+=cert
   s+=f'Theorem rfa_reset_step_{n} inputs path old current result :\n'
   if deps:s+=f' VM.find {deps[0]} old = Some (Gval (Fuint 32) (rfa_reset_word_{i} inputs path)) ->\n'
   s+=f''' formal_value_iter (formal_invalid_policy inputs path) flat_memories old false current flat_statements = Some result ->
 VM.find {n} result = Some (Gval (Fuint 32) (rfa_reset_word_{i} inputs path)).
Proof.
 intros {'Source ' if deps else ''}Step.
'''
   if isnode:
    if cached_node:
     s+=f''' assert (Member : List.In ({n},joint_update_expr_{n}) joint_update_expected_nodes).
 {{ apply (List.nth_error_In joint_update_expected_nodes {jointids.index(n)}%nat). vm_compute. reflexivity. }}
 destruct (selected_node_safe_position flat_memories flat_statements joint_update_node_offsets flat_statements joint_update_expected_nodes {n} joint_update_expr_{n} joint_update_node_positions joint_update_node_safety Member) as [count [tail [Position [Safe Nonreg]]]].
 eapply formal_combinational_known_node; [exact Position|exact Safe|exact Nonreg| |reflexivity|exact Step].
'''
    else:s+=f''' eapply formal_combinational_known_node;
 [exact {name}_position|exact {name}_safe|exact {name}_nonreg| |reflexivity|exact Step].
'''
    if deps:s+=f' cbn [{name}_expr eval_hfexpr_validif_policy eval_href_validif_policy]. exact Source.\n'
    else:s+=' reflexivity.\n'
   else:
    s+=f''' apply (declared_connection_value {start} flat_statements {name}_decl {name}_mid {name}_tail {n} {deps[0]} 32
 (Gval (Fuint 32) (rfa_reset_word_{i} inputs path)) (Gval (Fuint 32) (rfa_reset_word_{i} inputs path))
 (formal_invalid_policy inputs path) flat_memories old current result {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe {name}_nonreg (Logic.eq_refl _) Source).
 - assert (Take : take 32 (rfa_reset_word_{i} inputs path) = rfa_reset_word_{i} inputs path).
   {{ apply take_oversize. rewrite rfa_reset_word_{i}_size. reflexivity. }}
   cbn [adapt_hvalue_as_type]. rewrite Take. unfold zext_to,zext. rewrite rfa_reset_word_{i}_size subnn cats0. reflexivity.
 - exact Step.
'''
   s+='Qed.\n'
   s+=f'''Theorem rfa_reset_history_{n} inputs path history limit :
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, ({rank} <= t)%coq_nat -> (t <= limit)%coq_nat ->
 VM.find {n} (history t) = Some (Gval (Fuint 32) (rfa_reset_word_{i} inputs path)).
Proof.
 intros Steps t Lower Upper. destruct t as [|t]; [lia|].
 apply (rfa_reset_step_{n} inputs path (history t) (history t) (history (S t))).
'''
   if deps:s+=f' - apply (rfa_reset_history_{deps[0]} inputs path history limit Steps t);lia.\n'
   s+=' '+('- ' if deps else '')+'apply Steps;lia.\nQed.\n'
 write(f'RFArchitecturalResetSources{batch}',s)
print('Generated 8 shared RF reset source units, 32 banks, depth6')
# Existing implementation register metadata is reused; reference metadata is new.
for batch in range(8):
 s=header.replace('Require Import CoreSocModel','Require Import JointRegisterCommits2 JointRegisterCommits3 JointRegisterCommits4 JointRegisterCommits5 JointRegisterCommits6 CoreSocModel')
 for i in range(4*batch,4*batch+4):
  for n,cond,yes,no in [(851+i,779,1085+i,1021+i),(7299+i,1515,7370+2*i,1787+i)]:
   reg,start=regs[n];expr,end=conns[n];name=f'joint_register_{n}' if n<1000 else f'rfa_register_{n}'
   if n>=1000:
    s+=f'''Definition {name}_reg := {reg}.
Definition {name}_decl := match straight_drop {start+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_tail := match straight_drop {end+1} flat_statements with Some s => s | None => @Qnil VarOrder.T end.
Definition {name}_mid := take_statements {end-start-1} {name}_decl.
Lemma {name}_position : straight_drop {start} flat_statements = Some (@Qcons VarOrder.T (@Sreg VarOrder.T {n} {name}_reg) {name}_decl).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_split : {name}_decl = statement_append {name}_mid (@Qcons VarOrder.T (@Sfcnct VarOrder.T (@Eid VarOrder.T {n}) {expr}) {name}_tail).
Proof. vm_compute. reflexivity. Qed.
Lemma {name}_straight : straight_statements {name}_mid.
Proof. vm_compute. exact I. Qed.
Lemma {name}_mid_safe : formal_typed_suffix_safe flat_memories {n} {name}_mid.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_tail_safe : formal_typed_suffix_safe flat_memories {n} {name}_tail.
Proof. apply formal_typed_suffix_safe_b_sound. vm_compute. reflexivity. Qed.
Lemma {name}_identity : register_identity_b {n} flat_statements.
Proof. vm_compute. reflexivity. Qed.
'''
   s+=f'''Theorem rfa_reset_commit_{n} invalid old current result old_value word :
 VM.find {n} old = Some old_value -> type_of_val old_value = Gtyp (Fuint 32) ->
 VM.find {cond} old = Some (Gval (Fuint 1) [::true]) ->
 VM.find {yes} old = Some (Gval (Fuint 32) word) -> size word = 32%nat ->
 formal_value_iter invalid flat_memories old true current flat_statements = Some result ->
 VM.find {n} result = Some (Gval (Fuint 32) word).
Proof.
 intros Old Typed Reset Yes Size Step.
 destruct (formal_committed_uint_register_mux_observation {start} flat_statements {name}_decl {name}_mid {name}_tail
 {n} {name}_reg (@Eref VarOrder.T (@Eid VarOrder.T {cond})) (@Eref VarOrder.T (@Eid VarOrder.T {yes})) (@Eref VarOrder.T (@Eid VarOrder.T {no})) invalid flat_memories old current result old_value 32
 {name}_position {name}_split {name}_straight {name}_mid_safe {name}_tail_safe Old Typed {name}_identity Step)
 as [source [value [Source [Adapt Value]]]].
 change (eval_hfexpr_with_memory flat_memories {expr} old old = Some source) in Source.
 pose proof (selected_uint_mux_identity flat_memories old {cond} {yes} {no} 32 word source value Size Reset Yes Source Adapt) as Same.
 rewrite Same in Value. exact Value.
Qed.
'''
 write(f'RFArchitecturalResetCommits{batch}',s)
s=header.replace('Require Import CoreSocModel','Require Import ConcreteRegisterInitialization UIntRegisterCertificate FormalSingletonSymbolic StagedFlatCircuitIteration StagedObservedRegister StagedCircuitRegisterHold StagedRegisterHold FormalLocalHistory RegisterPreparationFrames CoreSocModel').replace('Semantics_with_memory.','Semantics_with_memory FormalInitialization.')
pairs='[::'+';'.join(f'({851+i}%nat,{7299+i}%nat)' for i in range(32))+']'
allids='[::'+';'.join(str(n)+'%nat' for i in range(32) for n in [851+i,7299+i])+']'
s+=f'''Definition rf_architectural_register_pairs : list (nat * nat) := {pairs}.
Definition rf_architectural_register_ids : list nat := {allids}.
Definition rf_architectural_relation env : Prop :=
 List.Forall (fun pair => exists word, size word = 32%nat /\\
 VM.find (N.of_nat (fst pair)) env = Some (Gval (Fuint 32) word) /\\
 VM.find (N.of_nat (snd pair)) env = Some (Gval (Fuint 32) word)) rf_architectural_register_pairs.
Definition rf_architectural_registers_concrete env : Prop :=
 forall node, List.In node rf_architectural_register_ids -> map_uint_concrete (N.of_nat node) 32 env.
Lemma rf_architectural_register_check :
 List.forallb (fun node => has_register (N.of_nat node) flat_statements &&
 uint_register_declarations_b (N.of_nat node) 32 flat_statements && initial_register_safe (N.of_nat node) flat_statements) rf_architectural_register_ids = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_architectural_register_properties node :
 List.In node rf_architectural_register_ids ->
 has_register (N.of_nat node) flat_statements = true /\\
 uint_register_declarations (N.of_nat node) 32 flat_statements /\\
 initial_register_safe (N.of_nat node) flat_statements.
Proof.
 intro Member. pose proof rf_architectural_register_check as Check.
 rewrite List.forallb_forall in Check. specialize (Check node Member).
 move/andP: Check => [/andP [Present Typed] Initial].
 split; [exact Present|]. split; [apply uint_register_declarations_b_sound;exact Typed|exact Initial].
Qed.
Lemma rf_architectural_symbolic_registers inputs path state :
 rf_architectural_registers_concrete (initialize_symbolic_registers inputs path flat_statements state).
Proof.
 intros node Member. destruct (rf_architectural_register_properties node Member) as [Present [Typed Initial]].
 apply initialize_establishes_uint_concrete; assumption.
Qed.
Theorem rf_architectural_symbolic_initial_concrete memory inputs states :
 circuit_symbolic_initial_state generated_modules generated_top memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\\ rf_architectural_registers_concrete env.
Proof.
 intro Init.
 exact (singleton_symbolic_property generated_modules generated_top 0 staged_top_ports flat_statements memory inputs states
 rf_architectural_registers_concrete flat_instance_map_exact flat_module_exact (rf_architectural_symbolic_registers inputs nil) Init).
Qed.
Lemma rf_architectural_nonexternal node :
 List.In node rf_architectural_register_ids ->
 (N.of_nat node != 0) /\ (N.of_nat node != 1).
Proof.
 intro Member.
 assert (Check : List.forallb (fun n => (N.of_nat n != 0) && (N.of_nat n != 1)) rf_architectural_register_ids = true).
 {{ vm_compute. reflexivity. }}
 rewrite List.forallb_forall in Check. specialize (Check node Member).
 move/andP: Check => [Clock Reset]. split; assumption.
Qed.
Theorem rf_architectural_prepared_concrete previous old external initial :
 SVM.find nil previous = Some old -> rf_architectural_registers_concrete old ->
 circuit_initial_map_with_memory generated_modules generated_top (Some previous) external = Some initial ->
 rf_architectural_registers_concrete (top_environment initial).
Proof.
 intros Previous Concrete Prepare node Member.
 destruct (rf_architectural_nonexternal node Member) as [Nonclock Nonreset].
 destruct (rf_architectural_register_properties node Member) as [Present [Typed Initial]].
 destruct (Concrete node Member) as [word [Size Value]]. exists word; split; [exact Size|].
 pose proof (staged_prepared_register_copies previous old external initial (N.of_nat node) Nonclock Nonreset Initial Present Previous Prepare) as Copy.
 rewrite Value in Copy. unfold staged_register_lookup in Copy. unfold top_environment.
 destruct (SVM.find nil initial); [exact Copy|discriminate Copy].
Qed.
Print Assumptions rf_architectural_symbolic_initial_concrete.
'''
write('RFArchitecturalRelation',s)
imports=' '.join('RFArchitecturalResetSources'+str(i)+' RFArchitecturalResetCommits'+str(i) for i in range(8))
s=header.replace('Require Import CoreSocModel',f'Require Import {imports} RFArchitecturalRelation StagedFlatCircuitIteration FormalLocalHistory StagedCircuitRegisterHold StagedRegisterHold FormalResetTrace FormalResetPreparation FormalRFResetControl ReferencePCResetHistory ObservedLegalNoTrap StagedIterationCount ObservedArchitecturalRegisters CoreSocModel').replace('Semantics_with_memory.','Semantics_with_memory FormalInitialization.')
s+='''Local Opaque flat_statements flat_memories generated_modules generated_top.
Lemma rf_architectural_history_concrete invalid history limit :
 rf_architectural_registers_concrete (history 0%nat) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter invalid flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 forall t, (t <= limit)%coq_nat -> rf_architectural_registers_concrete (history t).
Proof.
 intros Initial Steps t. induction t as [|t IH]; intro Bound; [exact Initial|].
 intros node Member. destruct (rf_architectural_register_properties node Member) as [Present Rest].
 destruct (IH ltac:(lia) node Member) as [word [Size Value]]. exists word; split; [exact Size|].
 rewrite (staged_combinational_holds_registers invalid flat_memories (history t) (history t) (history (S t)) flat_statements (N.of_nat node) Present (Steps t ltac:(lia))). exact Value.
Qed.
Theorem rf_architectural_reset_local inputs path history limit current result :
 rf_architectural_registers_concrete (history limit) ->
 (forall t, (t < limit)%coq_nat -> formal_value_iter (formal_invalid_policy inputs path) flat_memories (history t) false (history t) flat_statements = Some (history (S t))) ->
 (6 <= limit)%coq_nat ->
 VM.find 779 (history limit) = Some (Gval (Fuint 1) [::true]) ->
 VM.find 1515 (history limit) = Some (Gval (Fuint 1) [::true]) ->
 formal_value_iter (formal_invalid_policy inputs path) flat_memories (history limit) true current flat_statements = Some result ->
 rf_architectural_relation result.
Proof.
 intros Concrete Steps Bound ResetD ResetR Commit.
 unfold rf_architectural_relation, rf_architectural_register_pairs.
'''
for i in range(32):
 s+=f''' apply List.Forall_cons.
 {{ exists (rfa_reset_word_{i} inputs path). split; [apply rfa_reset_word_{i}_size|]. split.
'''
 for idx,n,source,rst in [(2*i,851+i,1085+i,'ResetD'),(2*i+1,7299+i,7370+2*i,'ResetR')]:
  s+=f'''   - assert (Member : List.In {n}%nat rf_architectural_register_ids).
     {{ apply (List.nth_error_In rf_architectural_register_ids {idx}%nat). reflexivity. }}
     destruct (Concrete {n}%nat Member) as [oldword [OldSize Old]].
     apply (rfa_reset_commit_{n} (formal_invalid_policy inputs path) (history limit) current result (Gval (Fuint 32) oldword) (rfa_reset_word_{i} inputs path));
     [exact Old|reflexivity|exact {rst}| |apply rfa_reset_word_{i}_size|exact Commit].
     apply (rfa_reset_history_{source} inputs path history limit Steps limit); lia.
'''
 s+=' }\n'
s+=''' constructor.
Qed.
Theorem rf_architectural_settle_reset_commit inputs initial stable result :
 state_reset initial true ->
 rf_architectural_registers_concrete (top_environment initial) ->
 circuit_formal_iterations generated_modules generated_top inputs 9259 initial = Some stable ->
 formal_circuit_value_iter (formal_invalid_policy inputs) generated_modules generated_top stable true = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_architectural_relation env.
Proof.
 intros Reset Concrete Iterations Commit.
 destruct (rf_control_9259 inputs initial stable true Reset Iterations) as [control [Control ResetD]].
 destruct Reset as [start [Start Reset]].
 destruct (local_iteration_history inputs 9259 initial stable Iterations) as [history [First [Last Steps]]].
 assert (Reset0 : VM.find 1 (history 0%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite First. unfold top_environment. rewrite Start. exact Reset. }
 pose proof (legal_local_reset_history _ history 9259 true Steps Reset0) as Resets.
 pose proof (reference_pc_reset_after_four (formal_invalid_policy inputs nil)
 (history 9255%nat) (history 9256%nat) (history 9257%nat) (history 9258%nat) (history 9259%nat) true
 (Resets 9255%nat ltac:(vm_compute;lia))
 (Steps 9255%nat ltac:(vm_compute;lia)) (Steps 9256%nat ltac:(vm_compute;lia))
 (Steps 9257%nat ltac:(vm_compute;lia)) (Steps 9258%nat ltac:(vm_compute;lia))) as ResetR.
 destruct (flat_iteration_projection (formal_invalid_policy inputs) stable true result Commit)
 as [before [after [Before [Local After]]]].
 assert (HistoryBefore : history 9259%nat = before).
 { rewrite Last. unfold top_environment. rewrite Before. reflexivity. }
 rewrite <- HistoryBefore in Local.
 assert (D : VM.find 779 (history 9259%nat) = Some (Gval (Fuint 1) [::true])).
 { rewrite Last. unfold top_environment. rewrite Control. exact ResetD. }
 exists after; split; [exact After|].
 apply (rf_architectural_reset_local inputs nil history 9259 (history 9259%nat) after).
 - apply (rf_architectural_history_concrete (formal_invalid_policy inputs nil) history 9259); [rewrite First;exact Concrete|exact Steps|lia].
 - exact Steps.
 - vm_compute; lia.
 - exact D.
 - exact ResetR.
 - exact Local.
Qed.
Theorem rf_architectural_real_reset_cycle inputs previous old result :
 SVM.find nil previous = Some old -> rf_architectural_registers_concrete old ->
 VM.find 1 (formal_external_inputs inputs) = Some (Gval (Fuint 1) [::true]) ->
 circuit_formal_cycle generated_modules generated_top (Some previous) inputs = Some result ->
 exists env, SVM.find nil result = Some env /\ rf_architectural_relation env.
Proof.
 intros Previous Concrete Reset Cycle. unfold circuit_formal_cycle in Cycle.
 destruct (circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs inputs)) as [initial|] eqn:Prepare; [|discriminate Cycle].
 pose proof flat_iteration_count_exact as Count. unfold flat_iteration_count in Count. rewrite Count in Cycle.
 destruct (circuit_formal_iterations generated_modules generated_top inputs 9259 initial) as [stable|] eqn:Steps; [|discriminate Cycle].
 apply (rf_architectural_settle_reset_commit inputs initial stable result); [| |exact Steps|exact Cycle].
 - exact (top_reset_prepared (Some previous) _ initial _ Reset Prepare).
 - exact (rf_architectural_prepared_concrete previous old _ initial Previous Concrete Prepare).
Qed.
Theorem rf_architectural_after_formal_reset memory inputs states :
 formal_state_after_reset generated_modules generated_top 1 (Fuint 1) memory inputs = Some states ->
 exists env, SVM.find nil states = Some env /\ rf_architectural_relation env.
Proof.
 unfold formal_state_after_reset.
 destruct (circuit_symbolic_initial_state generated_modules generated_top memory inputs) as [initial|] eqn:Init; [|discriminate]. intro Reset.
 destruct (rf_architectural_symbolic_initial_concrete memory inputs initial Init) as [old [Old Concrete]].
 apply (rf_architectural_real_reset_cycle (force_formal_reset 1 (Fuint 1) inputs) initial old states Old Concrete); [|exact Reset].
 unfold force_formal_reset. cbn [formal_external_inputs]. apply RegisterMapFacts.find_add_eq. reflexivity.
Qed.
Theorem rf_architectural_run_zero memory inputs states :
 generated_run memory inputs 0 = Some states ->
 exists env, SVM.find nil states = Some env /\ rf_architectural_relation env.
Proof.
 unfold generated_run, formal_run_after_reset.
 destruct (formal_state_after_reset generated_modules generated_top generated_reset_id generated_reset_type memory (inputs 0%nat)) as [initial|] eqn:Reset; [|discriminate].
 cbn [circuit_formal_run]. intro Run. inversion Run; subst states.
 exact (rf_architectural_after_formal_reset memory (inputs 0%nat) initial Reset).
Qed.
'''
write('RFArchitecturalResetRelation',s)
write('RFArchitecturalResetAssumptions','Require Import RFArchitecturalResetRelation.\nDefinition rf_architectural_reset_audit_bundle := (@rf_architectural_run_zero, @rf_architectural_real_reset_cycle).\nPrint Assumptions rf_architectural_reset_audit_bundle.\n')
report={'scope':'flattened LowFIRRTL actual reset wiring','register_pairs':[],'raw_symbolic_initialization':'concrete independent values; equality is established only by the subsequent shared-source reset','reset_source_depths':{'implementation':4,'reference':6},'formal_relation_module':'RFArchitecturalRelation','reset_relation_module':'RFArchitecturalResetRelation'}
for i in range(32):
 report['register_pairs'].append({'architectural_index':i,'implementation':851+i,'reference':7299+i,'implementation_reset_path':[8089+2*i,8090+2*i,787+i,1085+i,851+i],'reference_reset_path':[8089+2*i,8090+2*i,1482+i,1672+i,7369+2*i,7370+2*i,7299+i],'shared_leaf':8089+2*i,'shared_leaf_statement_position':nodes[8089+2*i][1],'shared_leaf_kind':'zero_constant' if i==0 else 'validif_false_symbolic'})
(base/'rf-architectural-reset-map.json').write_text(json.dumps(report,indent=2)+'\n')
