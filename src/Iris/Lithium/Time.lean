import Iris.BI
import Iris.ProofMode
import Iris.Lithium.IRunAttr
import Iris.Lithium.IRun
import Iris.Lithium.Exp
import Iris.Lithium.Lithium
import Iris.Lithium.ExpLi

namespace Iris.ExampleLang
open BI

variable [BI PROP]

set_option Elab.async false in
example [BI PROP] [BIAffine PROP] P :
  ⊢ contains_spec (PROP:=PROP) P := by
  unfold contains_spec contains_spec_pre contains_spec_post contains_fn
  apply (BI.BIBase.Entails.trans _ (prove_fn_spec _ _ _))
  istart
  simp only [irun_preprocess]
  irun
  rename List Val => xs
  cases xs <;> simp at *
