import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearchRiscv64

set_option maxRecDepth 30000 in
abbrev a4c : IslaTrace := isla%
(trace
  (cycle)
  (declare-const v0 (_ BitVec 64)) 
  (read-reg |PC| nil v0)
  (define-const v1 (bvadd v0 #x0000000000000004))
  (write-reg |nextPC| nil v1)
  (define-enum |rop| 10 (|RISCV_ADD| |RISCV_SUB| |RISCV_SLL| |RISCV_SLT| |RISCV_SLTU| |RISCV_XOR| |RISCV_SRL| |RISCV_SRA| |RISCV_OR| |RISCV_AND|))
  (declare-const v2 (_ BitVec 64)) 
  (read-reg |x10| nil v2)
  (declare-const v3 (_ BitVec 64)) 
  (read-reg |x9| nil v3)
  (define-const v4 (bvadd v2 v3))
  (write-reg |x8| nil v4)
  (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
  (read-reg |nextPC| nil v1)
  (write-reg |PC| nil v1))
