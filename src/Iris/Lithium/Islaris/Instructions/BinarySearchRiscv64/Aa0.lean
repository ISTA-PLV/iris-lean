import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearchRiscv64

set_option maxRecDepth 30000 in
abbrev aa0 : IslaTrace := isla%
(trace
  (cycle)
  (declare-const v0 (_ BitVec 64)) 
  (read-reg |PC| nil v0)
  (define-const v1 (bvadd v0 #x0000000000000004))
  (write-reg |nextPC| nil v1)
  (define-enum |rop| 10 (|RISCV_ADD| |RISCV_SUB| |RISCV_SLL| |RISCV_SLT| |RISCV_SLTU| |RISCV_XOR| |RISCV_SRL| |RISCV_SRA| |RISCV_OR| |RISCV_AND|))
  (declare-const v2 (_ BitVec 64)) 
  (read-reg |x11| nil v2)
  (declare-const v3 (_ BitVec 64)) 
  (read-reg |x10| nil v3)
  (define-const v8 ((_ zero_extend 63) (ite (bvslt ((_ zero_extend 64) v2) ((_ zero_extend 64) v3)) #b1 #b0)))
  (write-reg |x10| nil v8)
  (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
  (read-reg |nextPC| nil v1)
  (write-reg |PC| nil v1))
