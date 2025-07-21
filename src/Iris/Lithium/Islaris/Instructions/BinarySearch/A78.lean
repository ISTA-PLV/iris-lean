import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearch

set_option maxRecDepth 30000 in
abbrev a78 : IslaTrace := isla%
(trace
  (assume-reg |__currentInstrLength| nil (_ bv4 128))
  (assume-reg |__isla_vector_gpr| nil false)
  (assume-reg |__v85_implemented| nil false)
  (define-enum |signal| 2 (|LOW| |HIGH|))
  (declare-const v2 (_ BitVec 1)) 
  (declare-const v24 (_ BitVec 1)) 
  (cycle)
  (read-reg |SEE| nil (_ bv-1 128))
  (write-reg |SEE| nil (_ bv1136 128))
  (write-reg |__unconditional| nil true)
  (define-enum |ArchVersion| 6 (|ARMv8p0| |ARMv8p1| |ARMv8p2| |ARMv8p3| |ARMv8p4| |ARMv8p5|))
  (read-reg |__v85_implemented| nil false)
  (read-reg |PSTATE| ((_ field |C|)) (_ struct (|C| v2)))
  (define-const v28 (= v2 #b1))
  (cases "model/aarch64.sail 11345:19 - 11345:52"
    (trace
      (assert v28)
      (read-reg |PSTATE| ((_ field |Z|)) (_ struct (|Z| v24)))
      (define-const v29 (= v24 #b0))
      (cases "model/aarch64.sail 11371:4 - 11381:5"
        (trace
          (assert v29)
          (read-reg |__isla_vector_gpr| nil false)
          (write-reg |R0| nil #x0000000000000000)
          (read-reg |__PC_changed| nil false)
          (declare-const v30 (_ BitVec 64)) 
          (read-reg |_PC| nil v30)
          (read-reg |__currentInstrLength| nil (_ bv4 128))
          (define-const v31 (bvadd v30 #x0000000000000004))
          (write-reg |_PC| nil v31))
        (trace
          (assert (not v29))
          (read-reg |__isla_vector_gpr| nil false)
          (write-reg |R0| nil #x0000000000000001)
          (read-reg |__PC_changed| nil false)
          (declare-const v32 (_ BitVec 64)) 
          (read-reg |_PC| nil v32)
          (read-reg |__currentInstrLength| nil (_ bv4 128))
          (define-const v33 (bvadd v32 #x0000000000000004))
          (write-reg |_PC| nil v33))))
    (trace
      (assert (not v28))
      (read-reg |__isla_vector_gpr| nil false)
      (write-reg |R0| nil #x0000000000000001)
      (read-reg |__PC_changed| nil false)
      (declare-const v34 (_ BitVec 64)) 
      (read-reg |_PC| nil v34)
      (read-reg |__currentInstrLength| nil (_ bv4 128))
      (define-const v35 (bvadd v34 #x0000000000000004))
      (write-reg |_PC| nil v35))))
