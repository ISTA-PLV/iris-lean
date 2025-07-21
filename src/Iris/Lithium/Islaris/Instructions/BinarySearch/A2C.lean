import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearch

set_option maxRecDepth 30000 in
abbrev a2c : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1027 128))
  (write-reg |__unconditional| nil true)
  (define-enum |ShiftType| 4 (|ShiftType_LSL| |ShiftType_LSR| |ShiftType_ASR| |ShiftType_ROR|))
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |__isla_vector_gpr| nil false)
  (declare-const v27 (_ BitVec 64)) 
  (read-reg |R20| nil v27)
  (declare-const v29 (_ BitVec 64)) 
  (read-reg |R23| nil v29)
  (define-const v58 (bvadd (bvadd ((_ extract 63 0) ((_ zero_extend 64) v27)) ((_ extract 63 0) ((_ zero_extend 64) (bvnot v29)))) #x0000000000000001))
  (write-reg |R8| nil v58)
  (read-reg |__PC_changed| nil false)
  (declare-const v59 (_ BitVec 64)) 
  (read-reg |_PC| nil v59)
  (read-reg |__currentInstrLength| nil (_ bv4 128))
  (define-const v60 (bvadd v59 #x0000000000000004))
  (write-reg |_PC| nil v60))
