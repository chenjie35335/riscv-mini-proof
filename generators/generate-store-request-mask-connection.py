from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
a=bisect.bisect_right(q,s.index('(@Swire VarOrder.T 80 '))-1;b=bisect.bisect_right(q,s.index('(@Sfcnct VarOrder.T (@Eid VarOrder.T 80)'))-1
x=(base/'staged-integration/FormalRFDataConnection.v').read_text().replace('Print Assumptions rf_input_connection_786.','')
x=x.replace('rf_input','store_request_mask').replace('786','80').replace('7937','7848')
for old,new in [('8007',b-a-1),('8804',b+1),('796',a+1),('795',a)]:x=x.replace(old,str(new))
x=re.sub(r'\b32\b','4',x).replace('Uextr 31 0','Uextr 3 0')
(base/'staged-integration/StoreRequestMaskConnection.v').write_text(x)
print(a,b)
