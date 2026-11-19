"""Generate source-independent writer type preservation from field rules."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
p=root/'formal/flat-low/staged-integration'
def write(n,s):
 f=p/n
 if not f.exists() or f.read_text()!=s:f.write_text(s)
s=(p/'DataWriterTail.v').read_text().replace('data_tail_writer_concrete','data_tail_writer_typed')
s=s.replace(' aw ab ew eb mw mb :',' :').replace(' WA WE WC WM SA SE SM Step.',' WA WE WC WM Step.')
for n,w,b in [(9230,'aw','ab'),(9232,'ew','eb'),(9233,'mw','mb')]:
 s=s.replace(f' VM.find {n} old = Some (Gval (Fuint {w}) {b}) ->\n','')
for old,new in [('(Gval (Fuint 16) (zext_to 16 (take 16 ab)))','address0'),('(Gval (Fuint 1) (zext_to 1 (take 1 eb)))','enable1'),('(Gval (Fuint 1) (zext_to 1 (take 1 mb)))','mask4')]:s=s.replace(old,new)
s=s.replace('exists clock2 data3, type_of_val clock2 = Gtyp Fclock /\\','exists address0 enable1 clock2 mask4 data3,\n type_of_val address0 = Gtyp (Fuint 16) /\\ type_of_val enable1 = Gtyp (Fuint 1) /\\\n type_of_val mask4 = Gtyp (Fuint 1) /\\ type_of_val clock2 = Gtyp Fclock /\\')
s=s.replace('pose proof (data_writer_address_concrete','destruct (data_writer_address_typed').replace('wd aw ab Value WA SA Connect0) as Value0.','wd Value WA Connect0) as [address0 [Address0 Value0]].')
s=s.replace('pose proof (data_writer_enable_concrete','destruct (data_writer_enable_typed').replace('wd ew eb Value0 WE SE Connect1) as Value1.','wd Value0 WE Connect1) as [enable1 [Enable1 Value1]].')
s=s.replace('pose proof (data_writer_mask_concrete','destruct (data_writer_mask_typed').replace('data3 mw mb Value3 WM SM Connect4) as Value4.','data3 Value3 WM Connect4) as [mask4 [Mask4 Value4]].')
s=s.replace('exists clock2, data3. split; [exact Clock2|].','exists address0, enable1, clock2, mask4, data3. repeat split; try assumption.')
write('DataWriterTypedTail.v',s)
s=(p/'FormalDataWriterIteration.v').read_text().replace('Require Import DataWriterTail.','Require Import DataWriterTypedTail.').replace('data_writer_iteration_concrete','data_writer_iteration_typed')
s=s.replace(' aw ab ew eb mw mb\n','\n').replace('DataType WA WE WC WM SA SE SM Step.','DataType WA WE WC WM Step.')
for n,w,b in [(9230,'aw','ab'),(9232,'ew','eb'),(9233,'mw','mb')]:s=s.replace(f' VM.find {n} old = Some (Gval (Fuint {w}) {b}) ->\n','')
for old,new in [('(Gval (Fuint 16) (zext_to 16 (take 16 ab)))','address0'),('(Gval (Fuint 1) (zext_to 1 (take 1 eb)))','enable0'),('(Gval (Fuint 1) (zext_to 1 (take 1 mb)))','mask0')]:s=s.replace(old,new)
s=s.replace('nc1 clock0 data0,','nc1 address0 enable0 clock0 mask0 data0,\n type_of_val address0 = Gtyp (Fuint 16) /\\ type_of_val enable0 = Gtyp (Fuint 1) /\\ type_of_val mask0 = Gtyp (Fuint 1) /\\')
s=s.replace('data_tail_writer_concrete','data_tail_writer_typed').replace('After DataType WA WE WC WM SA SE SM Tail','After DataType WA WE WC WM Tail')
s=s.replace('as [clock0 [data0 [Clock0 Final]]].','as [address0 [enable0 [clock0 [mask0 [data0 [Address0 [Enable0 [Mask0 [Clock0 Final]]]]]]]]].')
s=s.replace('nc1, clock0, data0.','nc1, address0, enable0, clock0, mask0, data0.')
write('FormalDataWriterTypedIteration.v',s)
