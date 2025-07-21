import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.Memcpy

set_option maxRecDepth 30000 in
abbrev a10 : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1066 128))
  (write-reg |__unconditional| nil true)
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |__isla_vector_gpr| nil false)
  (declare-const v28 (_ BitVec 64)) 
  (read-reg |R3| nil v28)
  (define-const v50 (bvadd ((_ extract 63 0) ((_ zero_extend 64) v28)) #x0000000000000001))
  (write-reg |R3| nil v50)
  (read-reg |__PC_changed| nil false)
  (declare-const v51 (_ BitVec 64)) 
  (read-reg |_PC| nil v51)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v52 (bvadd v51 #x0000000000000004))
  (write-reg |_PC| nil v52))
