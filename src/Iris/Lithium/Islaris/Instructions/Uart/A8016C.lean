import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.Uart

set_option maxRecDepth 30000 in
abbrev a8016c : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1614 128))
  (write-reg |__unconditional| nil true)
  (define-enum |LogicalOp| 3 (|LogicalOp_AND| |LogicalOp_EOR| |LogicalOp_ORR|))
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |__isla_vector_gpr| nil false)
  (declare-const v41 (_ BitVec 64)) 
  (read-reg |R0| nil v41)
  (define-const v44 (concat #x00000000 (bvand ((_ extract 31 0) v41) #x000000ff)))
  (write-reg |R0| nil v44)
  (read-reg |__PC_changed| nil false)
  (declare-const v45 (_ BitVec 64)) 
  (read-reg |_PC| nil v45)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v46 (bvadd v45 #x0000000000000004))
  (write-reg |_PC| nil v46))
