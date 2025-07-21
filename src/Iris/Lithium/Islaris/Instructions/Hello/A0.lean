import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.Hello

set_option maxRecDepth 30000 in
abbrev a0 : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1394 128))
  (write-reg |__unconditional| nil true)
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (declare-const v27 (_ BitVec 64)) 
  (read-reg |_PC| nil v27)
  (define-const v30 (bvadd (bvor (bvand v27 #xfffffffffffff000) #x0000000000000000) #x0000000000000000))
  (read-reg |__isla_vector_gpr| nil false)
  (write-reg |R1| nil v30)
  (read-reg |__PC_changed| nil false)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v31 (bvadd v27 #x0000000000000004))
  (write-reg |_PC| nil v31))
