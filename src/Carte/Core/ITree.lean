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

@[simp]
theorem interp_ret {F} (f : (i : E.I) → ITree F (E.O i)) (r : R) :
  ITree.interp f (ret r) = ret r := by
    unfold ITree.interp ITree.iter
    simp; rfl

@[simp]
theorem interp_trigger_id (t : ITree E R) :
    ITree.interp (λ i => ITree.trigger E i) t = t := by
  ext n
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      rcases ITree.match_itree t with ⟨r, rfl⟩ | ⟨t', rfl⟩ | ⟨i, k, rfl⟩
      · simp [interp_ret]
      · simp [interp_tau, ih]
      · simp [interp_vis, ITree.trigger]
        congr
        funext o
        exact ih (k o)

end ITree
