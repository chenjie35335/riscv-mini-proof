from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text();q=[m.start()for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
a=bisect.bisect_right(q,s.index('(@Swire VarOrder.T 1481 '))-1;b=bisect.bisect_right(q,s.index('(@Sfcnct VarOrder.T (@Eid VarOrder.T 1481)'))-1
x=(base/'staged-integration/FormalRFInputConnections.v').read_text();x=x[:x.index('Definition rf_input_decl_785')]
x=x.replace('rf_input','store_checker_data').replace('784','1481').replace('7941','8205').replace('Fuint 1','Fuint 32').replace('8205 1 source','8205 32 source')
for old,new in [('8007',b-a-1),('8802',b+1),('794',a+1),('793',a)]:x=re.sub(r'\b'+old+r'\b',str(new),x)
(base/'staged-integration/StoreCheckerDataConnection.v').write_text(x)
print(a,b)
