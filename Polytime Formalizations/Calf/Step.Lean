import «Polytime Formalizations».Calf.CBPV
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Algebra.Order.Monoid.Basic

open CBPV


-- structure CostMonoid where
--   Cost : Type
--   zero : Cost
--   plus : Cost → Cost → Cost
--   leq :


axiom Cost : Type
axiom costMonoid : IsOrderedAddMonoid Cost



axiom Cost : Type
--mirroring ℂ in the agda files - not sure if this is the correct translation though

variable {c c' c₁ c₂ : Cost}
variable {A B C : tp_pos}
variable {X Y Z : tp_neg}



noncomputable
def C_pos : tp_pos := meta_pos Cost

axiom step : (X : tp_neg) → Cost → cmp X → cmp X
axiom step_0 {e : cmp X} : step X zero e = e
