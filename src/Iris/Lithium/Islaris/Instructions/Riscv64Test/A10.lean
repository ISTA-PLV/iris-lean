import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.Riscv64Test

set_option maxRecDepth 30000 in
abbrev a10 : IslaTrace := isla%
(trace
  (declare-const v0 (_ BitVec 64)) 
  (assume (= ((_ extract 1 1) (|PC| nil)) #b0))
  (assert (= ((_ extract 1 1) v0) #b0))
  (cycle)
  (read-reg |PC| nil v0)
  (define-const v1 (bvadd v0 #x0000000000000004))
  (write-reg |nextPC| nil v1)
  (define-enum |bop| 6 (|RISCV_BEQ| |RISCV_BNE| |RISCV_BLT| |RISCV_BGE| |RISCV_BLTU| |RISCV_BGEU|))
  (declare-const v2 (_ BitVec 64)) 
  (read-reg |x10| nil v2)
  (declare-const v3 (_ BitVec 64)) 
  (read-reg |x11| nil v3)
  (define-const v4 (= v2 v3))
  (define-const v5 (bvadd v0 #x0000000000000008))
  (cases "model/riscv_insts_base.sail 186:2 - 204:23"
    (trace
      (assert v4)
      (define-const v6 ((_ extract 0 0) (bvlshr v5 #x0000000000000001)))
      (assert (not (= v6 #b1)))
      (assert (not (not (= v6 #b0))))
      (branch-address v5)
      (write-reg |nextPC| nil v5)
      (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
      (read-reg |nextPC| nil v5)
      (write-reg |PC| nil v5))
    (trace
      (assert (not v4))
      (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
      (read-reg |nextPC| nil v1)
      (write-reg |PC| nil v1))))
