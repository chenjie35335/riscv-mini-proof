"""Certify the actual reference PC register update, without modifying the model."""
from pathlib import Path
import re
import argparse
parser=argparse.ArgumentParser()
parser.add_argument("--fetch", action="store_true")
args=parser.parse_args()
root=Path(__file__).resolve().parents[2]
base=root/'formal/flat-low/staged-integration'
model=(root/'formal/flat-low/CoreSocModel.v').read_text()
def position(pattern):
 match=re.search(pattern,model)
 assert match
 return len(re.findall(r'\(@Qcons VarOrder.T ',model[:match.start()]))-1
node = 7768 if args.fetch else 7331
start=position(r'\(@Sreg VarOrder.T '+str(node)+' ')
end=position(r'\(@Sfcnct VarOrder.T \(@Eid VarOrder.T '+str(node)+r'\) ')
replacements={852:7331,778:1514,779:1515,1086:7433,1022:1819,861:start,862:start+1,331:end-start-1,1194:end+1}
if args.fetch:
 replacements.update({852:7768,778:64,779:65,1086:7767,1022:7781,32:33})
pairs = [('FormalRF852CommitSource','FetchPCCommitSource')] if args.fetch else [('FormalRF852CommitSource','ReferencePCCommitSource'),('FormalRF852ResetCommit','ReferencePCResetCommit')]
for source,target in pairs:
 text=(base/(source+'.v')).read_text()
 text=text.replace('rf_852','fetch_pc' if args.fetch else 'reference_pc').replace('FormalRF852CommitSource','ReferencePCCommitSource')
 text=re.sub(r'\b\d+\b',lambda m:str(replacements.get(int(m[0]),int(m[0]))),text)
 dest=base/(target+'.v')
 if not dest.exists() or dest.read_text()!=text:dest.write_text(text)
print('Reference PC register declaration and update positions:',start,end)
