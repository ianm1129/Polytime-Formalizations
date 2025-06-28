import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Algebra.Order.Monoid.Basic

universe u v

class Step (C : Type*) [AddCommMonoid C] (m : Type u → Type v) extends Monad m where
  step : C → m PUnit
  step_0 {α} {e : m α} : (step 0 >>= fun _ => e) = e
  step_add {c c'} : (step c >>= fun _ => step c') = step (c' + c)

-- class OracleCompLike (C : Type*) [AddMonoid C] (P : PFunctor)
--     (m : Type u → Type v) extends Monad m, Step C m where
--   oracle : (a : P.A) → m (P.B a)


variable {P : PFunctor} {m : Type → Type} [Step Nat m]

def idHard (n : Nat) : m Nat :=
  match n with
  | 0 => pure 0
  | n + 1 => do
    let _ ← Step.step (1 : Nat)
    let n' ← idHard n
    pure (n' + 1)


theorem idHardBound [LawfulMonad m] {n : Nat} : (idHard n : m Nat) = Step.step n >>= fun _ => pure n :=
  by induction n with
  | zero => simp only [idHard] ; rw [Step.step_0]
  | succ n ih => simp only [ih, idHard, bind_assoc, pure_bind, Step.step_add] ; rw [← bind_assoc, Step.step_add];



-- module Hard where
--   id : cmp (Π nat λ _ → F nat)
--   id zero = ret 0
--   id (suc n) =
--     step (F nat) 1 (
--       bind (F nat) (id n) λ n' →
--         ret (suc n')
--     )


--Goals: implement functions with this monad, instrument with cost, prove bounds
