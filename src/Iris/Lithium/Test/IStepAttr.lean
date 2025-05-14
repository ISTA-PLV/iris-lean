/-
Copyright (c) 2025 Michael Sammler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Sammler
-/
import Lean
import Qq
import Iris.BI

open Lean Meta Qq Iris.BI

/-- Environment extension for `istep` -/
initialize istepExt :
    SimpleScopedEnvExtension (Name × Array DiscrTree.Key) (DiscrTree Name) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun dt (n, ks) => dt.insertCore ks n
    initial := {}
  }

def unpackEntails : Expr → Option (Expr × Expr)
  | .app (.app (.app (.app (.const ``Entails _) _) _) G') G => some (G', G)
  | _ => none

initialize registerBuiltinAttribute {
  name := `istep
  descr := "istep lemma"
  add := fun decl _ kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let (_, _, targetTy) ← withReducible <| forallMetaTelescopeReducing declTy
    let some (_, G) := unpackEntails targetTy
      | throwError "@[istep] unexpected type"
    -- IO.println s!"{G}"
    let key ← DiscrTree.mkPath G
    istepExt.add (decl, key) kind
}
