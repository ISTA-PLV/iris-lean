import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearchRiscv64

set_option maxRecDepth 30000 in
abbrev a40 : IslaTrace := isla%
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
  (read-reg |x9| nil v2)
  (declare-const v3 (_ BitVec 64)) 
  (read-reg |x21| nil v3)
  (define-const v6 (bvsge ((_ zero_extend 64) v2) ((_ zero_extend 64) v3)))
  (define-const v7 (bvadd v0 #x0000000000000038))
  (cases "model/riscv_insts_base.sail 186:2 - 204:23"
    (trace
      (assert v6)
      (define-const v8 ((_ extract 0 0) (bvlshr v7 #x0000000000000001)))
      (assert (not (= v8 #b1)))
      (assert (not (not (= v8 #b0))))
      (branch-address v7)
      (write-reg |nextPC| nil v7)
      (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
      (read-reg |nextPC| nil v7)
      (write-reg |PC| nil v7))
    (trace
      (assert (not v6))
      (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
      (read-reg |nextPC| nil v1)
      (write-reg |PC| nil v1))))
