import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.BinarySearchRiscv64

set_option maxRecDepth 30000 in
abbrev a70 : IslaTrace := isla%
(trace
  (declare-const v0 (_ BitVec 64)) 
  (assume (= ((_ extract 1 1) (|PC| nil)) #b0))
  (assert (= ((_ extract 1 1) v0) #b0))
  (cycle)
  (read-reg |PC| nil v0)
  (define-const v1 (bvadd v0 #x0000000000000004))
  (write-reg |nextPC| nil v1)
  (define-const v2 (bvadd v0 #x0000000000000008))
  (define-const v3 ((_ extract 0 0) (bvlshr v2 #x0000000000000001)))
  (assert (not (= v3 #b1)))
  (assert (not (not (= v3 #b0))))
  (read-reg |nextPC| nil v1)
  (write-reg |nextPC| nil v2)
  (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
  (read-reg |nextPC| nil v2)
  (write-reg |PC| nil v2))
