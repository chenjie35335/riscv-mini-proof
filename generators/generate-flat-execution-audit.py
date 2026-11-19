"""Generate an extracted diagnostic harness from immutable flat assertion expressions."""
from pathlib import Path
import re
p=Path('formal/flat-low')
s=(p/'CoreSocModel.v').read_text()
def pairs(kind):
 out=[]
 for line in s.splitlines():
  m=re.match(r'Definition generated_'+kind+r'_m0_(\d+)_local .* := generated_expr_true (.*) sem -> generated_expr_true (.*) sem\.',line)
  if m:out.append((int(m[1]),m[2],m[3]))
 return sorted(out)
asserts=pairs('assert');assumes=pairs('assume')
assert len(asserts)==45 and len(assumes)==1
out='''Require Import CoreSocModel ComparisonNodes.
From Coq Require Import ZArith Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlZBigInt.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Firrtl_with_implicit_widths Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory FormalInitialization.
Local Open Scope N_scope.
Definition audit_input (reset : bool) : formal_inputs :=
 {| formal_external_inputs := VM.add 1 (Gval (Fuint 1) [::reset]) (VM.add 0 (Gval Fclock [::false]) (VM.empty hvalue));
    formal_symbolic_inputs := fun _ _ _ width => symbolic_word_of_N width 0 |}.
Definition audit_memory : memory_initialization := fun _ _ _ => 19.
Definition audit_initial := circuit_symbolic_initial_state generated_modules generated_top audit_memory (audit_input false).
Definition audit_prepare previous reset := circuit_initial_map_with_memory generated_modules generated_top (Some previous) (formal_external_inputs (audit_input reset)).
Definition audit_step states reset := circuit_value_iter_with_memory_policy (formal_invalid_policy (audit_input reset)) generated_modules generated_top states false.
Definition audit_commit states reset := circuit_value_iter_with_memory_policy (formal_invalid_policy (audit_input reset)) generated_modules generated_top states true.
Definition audit_bound := circuit_iter_count_with_memory generated_modules generated_top Gtyp_connect_count.
Definition audit_code (v : option hvalue) : nat :=
 match v with
 | None => 0%nat
 | Some (Needtobedefined _) => 1%nat
 | Some (Uninitialized _) => 2%nat
 | Some (Undefinedonpurpose _) => 3%nat
 | Some (Gval (Fuint 1) bits) => if bits == [::false] then 4%nat else 5%nat
 | Some _ => 6%nat end.
'''
for name,ps in [('assertions',asserts),('assumptions',assumes)]:
 out+=f'Definition audit_{name}_expressions := [:: '+ '; '.join(f'({en}, {pred})' for _,en,pred in ps)+'].\n'
 out+=f'''Definition audit_{name} states :=
 match SVM.find nil states with
 | None => [:: (0%nat,0%nat)]
 | Some env => map (fun ep => (audit_code (eval_hfexpr (fst ep) env env), audit_code (eval_hfexpr (snd ep) env env))) audit_{name}_expressions end.
'''
out+='''Definition audit_fields (states : SVM.t (VM.t hvalue)) :=
 match SVM.find nil states with
 | None => [::]
 | Some env => map (fun id => (id, VM.find id env)) [:: 1; 65; 779; 852; 1086; 1395; 7603; 7605; 7748; 7750; 7768; 75; 9238; 9240] end.
Extraction "formal/flat-low/FlatExecutionAudit.ml" audit_input audit_memory audit_initial audit_prepare audit_step audit_commit audit_bound audit_assertions audit_assumptions audit_fields.
'''
(p/'FlatExecutionAudit.v').write_text(out)
print('Extracted diagnostic source: 45 original assertion pairs, 1 original assumption pair.')
