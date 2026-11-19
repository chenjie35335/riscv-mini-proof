from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';directory=base/'staged-integration'
s=(base/'CoreSocModel.v').read_text();positions=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
t=(directory/'Assertion2GuardNodes.v').read_text()
changes={7575:7588,7576:7589}
for old,new in changes.items():
 oldpos=bisect.bisect_right(positions,s.index(f'(@Snode VarOrder.T {old} '))-1
 newpos=bisect.bisect_right(positions,s.index(f'(@Snode VarOrder.T {new} '))-1
 t=t.replace(f'straight_drop {oldpos} ',f'straight_drop {newpos} ').replace(f'straight_drop {oldpos+1} ',f'straight_drop {newpos+1} ')
for old,new in changes.items():t=t.replace(str(old),str(new))
(directory/'Assertion5GuardNodes.v').write_text(t)
u=(directory/'Assertion2ResetGuard.v').read_text()
a=u.index('Theorem assertion2_history_with_reset');b=u.index('Theorem assertion2_reset_guard_observed')
u=u[:a]+u[b:]
u=u.replace('Assertion2GuardNodes','Assertion5GuardNodes Assertion2ResetGuard').replace('assertion2_guard_after_two','assertion5_guard_after_two').replace('assertion2_reset_guard_observed','assertion5_reset_guard_observed')
for old,new in changes.items():u=u.replace(str(old),str(new))
(directory/'Assertion5ResetGuard.v').write_text(u)
