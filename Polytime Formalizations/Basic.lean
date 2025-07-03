import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Algebra.Order.Monoid.Basic
import ToMathlib.Control.Lawful.MonadState

/-!
  # Monad Cost

  This file defines the type class `MonadCost` for monads equipped with a cost function.
  We also define the laws that a cost function must satisfy in the `LawfulMonadCost` type class.
-/

universe u v w

class Step (C : Type*) [AddCommMonoid C] (m : Type → Type v) extends Monad m where
  step : C → m PUnit
  step_0 : step 0 = pure ()
  step_add {c c'} : (step c >>= fun _ => step c') = step (c' + c)

-- We want `MonadCost` to be like `MonadState` `MonadReader` `MonadLift` etc
-- #check LawfulMonadLift

/-- A type class for monads with a cost function. -/
class MonadCost (C : outParam (Type w)) (m : Type u → Type v) where
  cost : C → m PUnit

export MonadCost (cost)

class LawfulMonadCost (C : outParam (Type w)) (m : Type u → Type v)
    [AddMonoid C] [Monad m] [MonadCost C m] where
  cost_zero : cost (0 : C) = (pure PUnit.unit : m PUnit)
  cost_add {c c' : C} : (cost c >>= fun _ => cost c') = (cost (c' + c) : m PUnit)

export LawfulMonadCost (cost_zero cost_add)

attribute [simp] cost_zero cost_add

/-- A type class for monads that may call an oracle, specified by a `PFunctor`. -/
class MonadOracle (P : PFunctor) (m : Type u → Type v) where
  oracle : (a : P.A) → m (P.B a)

-- What laws should we have for `MonadOracle`?
-- class LawfulMonadOracle (P : PFunctor) (m : Type u → Type v) [Monad m] [MonadOracle P m] where

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
  | zero => simp only [idHard] ; rw [Step.step_0, pure_bind];
  | succ n ih => simp only [ih, idHard, bind_assoc, pure_bind] ;
                 rw [← bind_assoc, Step.step_add];



def fact (n : Nat) : m Nat :=
  match n with
  | 0 => pure 1
  | n + 1 => do
    let _ ← Step.step (1 : Nat)
    let n' ← fact n
    pure ((n+1) * n')

theorem factBound [LawfulMonad m] {n : Nat} : ∃ (z : Nat), ( fact n : m Nat) = Step.step n >>= fun _ => pure z :=
  by induction n with
  | zero => simp only [fact] ; rw [Step.step_0] ; existsi 1; rw [pure_bind]
  | succ n ih =>
      simp only [fact];
      rcases ih with ⟨z, hz⟩; rw [hz];
      existsi ((n+1) * z);
      simp [← Step.step_add];



--Todo: Generalize comparison function

def cmpInsert (x : Nat)  (L : List Nat) : m (List Nat) :=
  match L with
  | [] => pure [x]
  | y::xs => do let _ ← Step.step (1 : Nat)
                let L' ← cmpInsert x xs
                pure (if x < y then x::y::xs else y :: L')

--Proof: WTS exists L', c ≤ |L|, such that insert x L = Step.step c >>= fun _ => pure L'
--Need also totality of insert?

theorem insertBound [LawfulMonad m] (x : Nat) (L : List Nat) :
                    (∃ L' : List Nat, ∃ c : Nat, c ≤ (List.length L) ∧
                    (cmpInsert x L : m (List Nat)) = Step.step c >>= fun _ => pure L') :=

  by induction L with

  | nil => simp only [cmpInsert] ;
           existsi [x] ; existsi 0;
           simp only [List.length_nil];
           simp only [Nat.zero_le, true_and];
           rw [Step.step_0, pure_bind]

  | cons y ys ih => simp only [cmpInsert] ;
                    rcases ih with ⟨L', c, hc⟩ ; rw [hc.right] ;
                    if h : x < y then
                                      simp only [if_pos h] ;
                                      existsi x::y::ys, (c + 1);
                                      simp only [List.length_cons, Nat.add_le_add_iff_right, hc.left, true_and];
                                      simp only [pure_bind, bind_assoc, ← Step.step_add];
                    else simp only [List.length_cons, if_neg h] ;
                         existsi y::L', (c + 1);
                         simp only [Nat.add_le_add_iff_right, hc.left, true_and];
                         simp only [pure_bind, bind_assoc, ← Step.step_add];



def inSort (L : List Nat) : m (List Nat) :=
  match L with
  | [] => pure []
  | x::xs => do
    let _ ← Step.step (1 : Nat)
    let L' ← inSort xs
    let L'' ← cmpInsert x L'
    pure (L'')


theorem inSortBound [LawfulMonad m] {L : List Nat} : ( ∃ L' : List Nat, ∃ c : Nat, c ≤ (List.length L)*(List.length L) ∧
                                                    (inSort L : m (List Nat)) = Step.step c >>= fun _ => pure L') :=
  by induction L with
  | nil => simp only [inSort, List.length_nil, Nat.mul_zero, Nat.le_zero_eq, exists_eq_left];
           existsi []; rw [Step.step_0, pure_bind]
  | cons y ys ih => simp only [inSort, List.length_cons];
                    rcases ih with ⟨L', c, h⟩; rw [h.right];
                    simp only [pure_bind, bind_assoc];
                    have h := insertBound (m := m) y L' ;
                    sorry
                    -- apply insertBound y L';
                    -- rw [insertBound y L'];

-- module Hard where
--   id : cmp (Π nat λ _ → F nat)
--   id zero = ret 0
--   id (suc n) =
--     step (F nat) 1 (
--       bind (F nat) (id n) λ n' →
--         ret (suc n')
--     )


--Goals: implement functions with this monad, instrument with cost, prove bounds

--todo : add some kind of other composition theorem for costs?

-- define classes wrt synthetic cost notion (think about more)

-- instrument with oracle computation framework

-- look for cslib on lean chat in zulip?
