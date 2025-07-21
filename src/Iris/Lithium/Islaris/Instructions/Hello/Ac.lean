import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.Hello

set_option maxRecDepth 30000 in
abbrev ac : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1486 128))
  (write-reg |__unconditional| nil true)
  (define-enum |MoveWideOp| 3 (|MoveWideOp_N| |MoveWideOp_Z| |MoveWideOp_K|))
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |__isla_vector_gpr| nil false)
  (write-reg |R0| nil #x0000000000000048)
  (read-reg |__PC_changed| nil false)
  (declare-const v32 (_ BitVec 64)) 
  (read-reg |_PC| nil v32)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v33 (bvadd v32 #x0000000000000004))
  (write-reg |_PC| nil v33))
