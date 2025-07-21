import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearch

set_option maxRecDepth 30000 in
abbrev a48 : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (declare-const v24 (_ BitVec 1)) 
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1136 128))
  (write-reg |__unconditional| nil true)
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |__isla_vector_gpr| nil false)
  (declare-const v27 (_ BitVec 64)) 
  (read-reg |R23| nil v27)
  (define-const v28 v27)
  (declare-const v29 (_ BitVec 64)) 
  (read-reg |R24| nil v29)
  (define-const v30 v29)
  (read-reg |PSTATE| ((_ field |Z|)) (_ struct (|Z| v24)))
  (define-const v32 (= v24 #b1))
  (cases "model/aarch64.sail 11371:4 - 11381:5"
    (trace
      (assert v32)
      (define-const v33 v28)
      (write-reg |R23| nil v33)
      (read-reg |__PC_changed| nil false)
      (declare-const v34 (_ BitVec 64)) 
      (read-reg |_PC| nil v34)
      (read-reg |__currentInstrLength| nil (_ bv4 128))
      (define-const v35 (bvadd v34 #x0000000000000004))
      (write-reg |_PC| nil v35))
    (trace
      (assert (not v32))
      (define-const v37 (bvadd v30 #x0000000000000001))
      (write-reg |R23| nil v37)
      (read-reg |__PC_changed| nil false)
      (declare-const v38 (_ BitVec 64)) 
      (read-reg |_PC| nil v38)
      (read-reg |__currentInstrLength| nil (_ bv4 128))
      (define-const v39 (bvadd v38 #x0000000000000004))
      (write-reg |_PC| nil v39))))
