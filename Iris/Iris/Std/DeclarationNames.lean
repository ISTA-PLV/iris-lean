/-
Adapted from Mathlib.Tactic.DeclarationNames
Copyright (c) 2024 Moritz Firsching. Released under Apache 2.0 license.
Authors: Damiano Testa, Moritz Firsching
-/

module

prelude
public import Lean.Linter.Init
public import Lean.Elab.Command

public section

open Lean Parser Elab Command Meta

namespace FromMathlib.Linter

/-- If `stx` is a syntax node for an `export` statement, then `getAliasSyntax stx` returns the
array of identifiers with the "exported" names. -/
def getAliasSyntax {m} [Monad m] [MonadResolveName m] (stx : Syntax) : m (Array Syntax) := do
  let mut aliases := #[]
  if let `(export $_ ($ids*)) := stx then
    let currNamespace ← getCurrNamespace
    for idStx in ids do
      let id := idStx.getId
      aliases := aliases.push
        (mkIdentFrom (.ofRange (idStx.raw.getRange?.getD default)) (currNamespace ++ id))
  return aliases

/-- Used for linters which use `0` instead of `false` for disabling. -/
def logLint0Disable {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Nat) (stx : Syntax) (msg : MessageData) : m Unit :=
  let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} 0`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}{disable}")

end FromMathlib.Linter

end
