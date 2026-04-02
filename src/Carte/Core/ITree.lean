import ITree.Definition

namespace ITree

open ITree

variable {E R} (t : ITree E R)

theorem match_itree : ∀ (t : ITree E R),
    (∃ r, t = ret r) ∨ (∃ t', t = tau t') ∨ (∃ i k, t = vis i k) := by
  intro t
  cases t with
  | ret r => left; exists r
  | tau t => right; left; exists t
  | vis i k => right; right; exists i, k

end ITree
