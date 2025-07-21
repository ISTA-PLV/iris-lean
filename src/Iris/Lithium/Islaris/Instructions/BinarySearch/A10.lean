import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearch

set_option maxRecDepth 30000 in
abbrev a10 : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (assume-reg |PSTATE| ((_ field |EL|)) #b10)
  (assume-reg |PSTATE| ((_ field |SP|)) #b1)
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1066 128))
  (write-reg |__unconditional| nil true)
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |PSTATE| ((_ field |SP|)) (_ struct (|SP| #b1)))
  (read-reg |PSTATE| ((_ field |EL|)) (_ struct (|EL| #b10)))
  (declare-const v28 (_ BitVec 64)) 
  (read-reg |SP_EL2| nil v28)
  (define-const v48 ((_ extract 63 0) ((_ zero_extend 64) v28)))
  (read-reg |__isla_vector_gpr| nil false)
  (write-reg |R29| nil v48)
  (read-reg |__PC_changed| nil false)
  (declare-const v49 (_ BitVec 64)) 
  (read-reg |_PC| nil v49)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v50 (bvadd v49 #x0000000000000004))
  (write-reg |_PC| nil v50))
