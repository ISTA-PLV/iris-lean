import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.MemcpyRiscv64

set_option maxRecDepth 30000 in
abbrev a18 : IslaTrace := isla%
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
  (read-reg |x12| nil v2)
  (define-const v3 (not (= v2 #x0000000000000000)))
  (define-const v4 (bvadd v0 #xffffffffffffffec))
  (cases "model/riscv_insts_base.sail 186:2 - 204:23"
    (trace
      (assert v3)
      (define-const v5 ((_ extract 0 0) (bvlshr v4 #x0000000000000001)))
      (assert (not (= v5 #b1)))
      (assert (not (not (= v5 #b0))))
      (branch-address v4)
      (write-reg |nextPC| nil v4)
      (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
      (read-reg |nextPC| nil v4)
      (write-reg |PC| nil v4))
    (trace
      (assert (not v3))
      (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
      (read-reg |nextPC| nil v1)
      (write-reg |PC| nil v1))))
