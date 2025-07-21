import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearch

set_option maxRecDepth 30000 in
abbrev a58 : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1858 128))
  (write-reg |__unconditional| nil true)
  (define-enum |LogicalOp| 3 (|LogicalOp_AND| |LogicalOp_EOR| |LogicalOp_ORR|))
  (define-enum |ShiftType| 4 (|ShiftType_LSL| |ShiftType_LSR| |ShiftType_ASR| |ShiftType_ROR|))
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |__isla_vector_gpr| nil false)
  (write-reg |R23| nil #x0000000000000000)
  (read-reg |__PC_changed| nil false)
  (declare-const v34 (_ BitVec 64)) 
  (read-reg |_PC| nil v34)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v35 (bvadd v34 #x0000000000000004))
  (write-reg |_PC| nil v35))
