import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.Uart

set_option maxRecDepth 30000 in
abbrev a8017c : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1106 128))
  (write-reg |__unconditional| nil true)
  (define-enum |SystemHintOp| 11 (|SystemHintOp_NOP| |SystemHintOp_YIELD| |SystemHintOp_WFE| |SystemHintOp_WFI| |SystemHintOp_SEV| |SystemHintOp_SEVL| |SystemHintOp_ESB| |SystemHintOp_PSB| |SystemHintOp_TSB| |SystemHintOp_BTI| |SystemHintOp_CSDB|))
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |__PC_changed| nil false)
  (declare-const v46 (_ BitVec 64)) 
  (read-reg |_PC| nil v46)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v47 (bvadd v46 #x0000000000000004))
  (write-reg |_PC| nil v47))
