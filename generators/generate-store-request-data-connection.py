from pathlib import Path
import re,bisect
root=Path(__file__).resolve().parents[2];base=root/'formal/flat-low';s=(base/'CoreSocModel.v').read_text();q=[m.start() for m in re.finditer(r'\(@Qcons VarOrder.T ',s)]
a=bisect.bisect_right(q,s.index('(@Swire VarOrder.T 79 '))-1;b=bisect.bisect_right(q,s.index('(@Sfcnct VarOrder.T (@Eid VarOrder.T 79)'))-1
x=(base/'staged-integration/FormalRFDataConnection.v').read_text().replace('Print Assumptions rf_input_connection_786.','')
x=x.replace('rf_input','store_request_data').replace('786','79').replace('7937','7837')
for old,new in [('8007',b-a-1),('8804',b+1),('796',a+1),('795',a)]:x=x.replace(old,str(new))
(base/'staged-integration/StoreRequestDataConnection.v').write_text(x)
print(a,b)
