"""Instantiate checked bundle-field proof patterns for the actual writer port."""
from pathlib import Path
root = Path(__file__).resolve().parents[2]
p = root / 'formal/flat-low/staged-integration'
typed = (p / 'DataReaderAddressConnections.v').read_text()
typed = typed[typed.index('Lemma data_reader_address_typed_1'):typed.index('Print Assumptions data_reader_address_typed_1.')]
concrete = (p / 'DataReaderFieldConnections.v').read_text()
clock = concrete[concrete.index('Lemma data_reader_clock_typed_1'):concrete.index('Print Assumptions data_reader_address_concrete_1.')]
concrete = concrete[concrete.index('Lemma data_reader_address_concrete_1'):concrete.index('Lemma data_reader_clock_typed_1')]
header = '''Require Import RegisterInvariants ScalarNodeFrames ScalarSinkTypes DataReaderEnableConnections InstructionPortShape.
From nbits Require Import NBits.
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq.
From simplssrlib Require Import Var.
From firrtl Require Import Env_with_implicit_widths HiEnv_with_implicit_widths HiFirrtl_with_implicit_widths Semantics_with_implicit_widths Semantics_with_memory.
Local Open Scope N_scope.
'''
def writer_row(text):
    text = text.replace('p2 p3 p4 p5 p0 address', 'p2 p3 p4 p5 p1 address')
    text = text.replace('data_ports p2 p3 p4 p5 (data_port_fields', 'data_ports p2 p3 p4 p5 p1 (data_port_fields')
    text = text.replace(' data) p0)', ' data))')
    text = text.replace('(@Eid VarOrder.T 9178) 1)', '(@Eid VarOrder.T 9178) 0)')
    return text
out = header
for field, name, source, width in [(0,'address',9230,16),(1,'enable',9232,1),(3,'mask',9233,1)]:
    for kind, pattern in [('typed',typed),('concrete',concrete)]:
        text = writer_row(pattern)
        text = text.replace(f'data_reader_address_{kind}_1', f'data_writer_{name}_{kind}')
        text = text.replace('9221',str(source))
        text = text.replace('(@Eid VarOrder.T 9178) 0) 0)',f'(@Eid VarOrder.T 9178) 0) {field})')
        if name != 'address':
            # Swap local field variables; retain data_port_fields physical field order.
            text = text.replace('address','SWAPPED').replace(name,'address').replace('SWAPPED',name)
            text = text.replace('data_writer_address_',f'data_writer_{name}_')
            text = text.replace('data_port_fields enable address clock mask data','data_port_fields address enable clock mask data') if name=='enable' else text.replace('data_port_fields mask enable clock address data','data_port_fields address enable clock mask data')
            if name=='enable':
                text = text.replace('data_port_fields written address clock mask data','data_port_fields address written clock mask data')
                text = text.replace('(zext_to 16 (take 16 bits))) address clock mask data','(zext_to 16 (take 16 bits))) clock mask data')
                text = text.replace('data_port_fields (Gval (Fuint 16)', 'data_port_fields address (Gval (Fuint 16)')
            else:
                text = text.replace('data_port_fields written enable clock address data','data_port_fields address enable clock written data')
                text = text.replace('(zext_to 16 (take 16 bits))) enable clock address data','(zext_to 16 (take 16 bits))) data')
                text = text.replace('data_port_fields (Gval (Fuint 16)', 'data_port_fields address enable clock (Gval (Fuint 16)')
        text = text.replace('16', str(width))
        out += text + f'Print Assumptions data_writer_{name}_{kind}.\n'
text = writer_row(clock).replace('data_reader_clock_typed_1','data_writer_clock_typed').replace('(@Eid VarOrder.T 0) old current','(@Eid VarOrder.T 9231) old current').replace('(@Eid VarOrder.T 0) old old','(@Eid VarOrder.T 9231) old old')
out += text + 'Print Assumptions data_writer_clock_typed.\n'
f = p / 'DataWriterFieldConnections.v'
if not f.exists() or f.read_text() != out: f.write_text(out)
