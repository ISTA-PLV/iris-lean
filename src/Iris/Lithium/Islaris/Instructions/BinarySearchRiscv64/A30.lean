import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearchRiscv64

set_option maxRecDepth 30000 in
abbrev a30 : IslaTrace := isla%
(trace
  (cycle)
  (declare-const v0 (_ BitVec 64)) 
  (read-reg |PC| nil v0)
  (define-const v1 (bvadd v0 #x0000000000000004))
  (write-reg |nextPC| nil v1)
  (define-enum |iop| 6 (|RISCV_ADDI| |RISCV_SLTI| |RISCV_SLTIU| |RISCV_XORI| |RISCV_ORI| |RISCV_ANDI|))
  (declare-const v2 (_ BitVec 64)) 
  (read-reg |x10| nil v2)
  (define-const v3 (bvadd v2 #x0000000000000000))
  (write-reg |x20| nil v3)
  (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
  (read-reg |nextPC| nil v1)
  (write-reg |PC| nil v1))
