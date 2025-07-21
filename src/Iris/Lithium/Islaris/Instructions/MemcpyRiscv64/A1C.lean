import Iris.Lithium.Islaris.Isla

namespace Islaris.Instructions.MemcpyRiscv64

set_option maxRecDepth 30000 in
abbrev a1c : IslaTrace := isla%
(trace
  (declare-const v0 (_ BitVec 64)) 
  (assume (= ((_ extract 1 1) (|x1| nil)) #b0))
  (assert (= ((_ extract 1 1) v0) #b0))
  (cycle)
  (declare-const v1 (_ BitVec 64)) 
  (read-reg |PC| nil v1)
  (define-const v2 (bvadd v1 #x0000000000000004))
  (write-reg |nextPC| nil v2)
  (read-reg |x1| nil v0)
  (define-const v4 (bvor (bvand (bvadd v0 #x0000000000000000) #xfffffffffffffffe) #x0000000000000000))
  (define-const v5 ((_ extract 0 0) (bvlshr v4 #x0000000000000001)))
  (assert (not (= v5 #b1)))
  (assert (not (not (= v5 #b0))))
  (read-reg |nextPC| nil v2)
  (write-reg |nextPC| nil v4)
  (define-enum |Retired| 2 (|RETIRE_SUCCESS| |RETIRE_FAIL|))
  (read-reg |nextPC| nil v4)
  (write-reg |PC| nil v4))
