import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Algebra.Order.Monoid.Basic
import ToMathlib.Control.Lawful.MonadState
import ToMathlib.Control.AlternativeMonad
import Mathlib.Data.Real.Basic
import VCVio

/-!
  # Monad Cost

  This file defines the type class `MonadStep` for monads equipped with a cost / step function.
  We also define the laws that a cost / step function must satisfy in the `LawfulMonadStep` type class.
-/

universe u v w

/-- A type class for monads with a step function. -/
class MonadStep (C : outParam (Type w)) (m : Type u → Type v) where
  step : C → m PUnit

-- agda-step : C → m α → m α

-- step c ma = do step c; ma = step c >>= fun _

export MonadStep (step)

class LawfulMonadStep (C : outParam (Type w)) (m : Type u → Type v)
    [AddMonoid C] [Preorder C] [Monad m] [MonadStep C m] where
  step_zero : step (0 : C) = (pure PUnit.unit : m PUnit)
  step_add {c c' : C} : (step c >>= fun _ => step c') = (step (c' + c) : m PUnit)

  -- make this c + c', possibly add commutativity for step
  -- also maybe add applicative version of step? So that don't need so many binds

export LawfulMonadStep (step_zero step_add)

attribute [simp] step_zero step_add

-- define a preorder? on the monad based on the step
-- so more step is larger


-- class IsBounded
-- or `HasCost`

-- class HasCost {C : outParam (Type w)} {m : Type u → Type v} {α : Type u} {β : Type u}
--     (f : α → m β) (cost : C) [AddMonoid C] where

--Easier to do with def than class, turns out

def HasCost {C : outParam (Type w)} {m : Type u → Type v} {α : Type u}
    (e : m α) (cost : C) [AddMonoid C] [Monad m] [MonadStep C m] : Prop :=
    (e >>= fun _ => pure PUnit.unit : m PUnit) = step cost


def IsBounded {C : outParam (Type w)} {m : Type u → Type v} {α : Type u}
    (e : m α) (cost : C) [LE C] [AddMonoid C] [Monad m] [MonadStep C m] : Prop :=
    ∃ cost', cost' ≤ cost ∧ (HasCost e cost')

-- More effects:
-- - State
-- - Prob. sampling / choice
-- - Non-determinism (special case of choice)
-- - Higher-order functions
-- - Oracle queries

-- We want `MonadStep` to be like `MonadState` `MonadReader` `MonadLift` etc
-- #check LawfulMonadLift

#check MonadState
#check LawfulMonadState

class MonadStateStep (σ : outParam (Type u)) (C : Type*) (m : Type u → Type v)
    [Monad m] [AddMonoid C] [Preorder C] [MonadStep C m] [LawfulMonadStep C m]
    extends LawfulMonadState σ m where
  /-- `get` is free, so `step` can be moved past it. -/
  get_step {cost : C} :
    (do step cost; get) = (do let s ← get; step cost; return s)
  /-- `set` is free, so it commutes with `step`. -/
  set_step {cost : C} {s : σ} :
    (do step cost; set s) = (do set s; step cost)

-- The standard `get` and `set` from `MonadState` are:
-- get : m σ
-- set : σ → m PUnit

-- The "Agda-style" `get` and `set` are continuation-based:
-- agda_get : (σ → m α) → m α
-- agda_set : σ → m α → m α

-- Here is how you can translate between them.
-- agda_get e := do let s ← get; e s
-- agda_set s e := do let x ← e s; set s; return x

-- or `MonadNonDet`
class MonadBranch (m : Type u → Type v) extends Monad m where
  branch {α : Type u} : m α → m α → m α

export MonadBranch (branch)

class AlternativeMonadBranch (m : Type u → Type v) extends AlternativeMonad m, MonadBranch m where

class LawfulMonadBranch (m : Type u → Type v) [Monad m] [MonadBranch m] where
  branch_assoc {α} {e0 e1 e2 : m α} : branch (branch e0 e1) e2 = branch e0 (branch e1 e2)
  branch_comm {α} {e0 e1 : m α} : branch e0 e1 = branch e1 e0
  branch_idem {α} {e : m α} : branch e e = e

class LawfulAlternativeMonadBranch (m : Type u → Type v) [AlternativeMonadBranch m] where
  branch_fail_left {α} : branch (failure : m α) = id
  branch_fail_right {α} : (branch · (failure : m α)) = id

class LawfulMonadBranchStep (C : outParam (Type w)) (m : Type u → Type v) [Monad m]
                      [AddMonoid C] [Preorder C] [MonadStep C m] [LawfulMonadStep C m]
                      [MonadBranch m] extends LawfulMonadBranch m where

  branch_step {α} {c : C} {e0 e1 : m α} :
    (do step c; branch e0 e1) = branch (do step c; e0) (do step c; e1)

class LawfulAlternativeMonadStep (C : outParam (Type w)) (m : Type u → Type v) [AlternativeMonad m]
                      [AddMonoid C] [Preorder C] [MonadStep C m] [LawfulMonadStep C m]
                      extends LawfulAlternative m where
  fail_step {α} {c : C} : (do step c; failure) = (failure : m α)

class MonadProb (m : Type u → Type v) extends Monad m where
  flip {α} : (Set.Icc (0 : Rat) 1) → m α → m α → m α

  flip_zero {α} {e0 e1 : m α} : flip ⟨0, by simp⟩ e0 e1 = e0
  flip_one {α} {e0 e1 : m α} : flip ⟨1, by simp⟩ e0 e1 = e1

  flip_same {α} {e : m α} {p : Set.Icc 0 1} : flip p e e = e

  flip_sym {α} {e0 e1 : m α} {p : Set.Icc 0 1} :
    flip p e0 e1 = flip ⟨1 - p, by simp; exact p.prop.symm⟩ e1 e0

  flip_assoc_right {α} {e₀ e₁ e₂ : m α} {p q r : Set.Icc 0 1} (h : p = min (max p q) r) :
    flip p (flip q e₀ e₁) e₂ = flip (max p q) e₀ (flip r e₁ e₂)

  flip_assoc_left {α} {e₀ e₁ e₂ : m α} {p q r : Set.Icc 0 1} (h : p = max (min p q) r) :
    flip p e₀ (flip q e₁ e₂) = flip (min p q) (flip r e₀ e₁) e₂

  flip_bind {α} {β} {f : α → m β} {p : Set.Icc 0 1} {e0 e1 : m α} :
          (flip p e0 e1 >>= f) = flip p (e0 >>= f) (e1 >>= f)

-- TODO: refactor hierarchy

class MonadProbStep (C : outParam (Type w)) (m : Type u → Type v) [Monad m]
                      [AddMonoid C] [Preorder C] [MonadStep C m] [LawfulMonadStep C m]
                      extends MonadProb m where
  flip_step {α} {c : C} {p : Set.Icc 0 1} {e0 e1 : m α} :
    (do step c; flip p e0 e1) = flip p (do step c; e0) (do step c; e1)

/-- A type class for monads that may call an oracle, specified by a `PFunctor`. -/
class MonadOracle (P : PFunctor) (m : Type u → Type v) extends Monad m where
  query : (a : P.A) → m (P.B a)

open MonadOracle in
class LawfulMonadOracleStep (C : outParam (Type w)) (P : PFunctor) (m : Type u → Type v)
                      [MonadOracle P m] [AddMonoid C] [Preorder C] [MonadStep C m]
                      [LawfulMonadStep C m] where
  query_step {c : C} {a : P.A} :
    (do step c; query a : m (P.B a)) = (do let x ← query a; step c; return x)

#check FreeMonad.mapM
#check OracleComp.mapM

variable {P : PFunctor} {m : Type → Type} [Monad m] [MonadStep Nat m] [LawfulMonadStep Nat m]

def idHard (n : Nat) : m Nat :=
  match n with
  | 0 => pure 0
  | n + 1 => do
    let _ ← step (1 : Nat)
    let n' ← idHard n
    pure (n' + 1)

theorem idHardBound [LawfulMonad m] {n : Nat} : (idHard n : m Nat) = step n >>= fun _ => pure n :=
  by induction n with
  | zero => simp only [idHard] ; rw [step_zero, pure_bind];
  | succ n ih => simp only [ih, idHard, bind_assoc, pure_bind] ;
                 rw [← bind_assoc, step_add, add_comm];


def fact (n : Nat) : m Nat :=
  match n with
  | 0 => pure 1
  | n + 1 => do
    let _ ← step (1 : Nat)
    let n' ← fact n
    pure ((n+1) * n')

theorem factBound [LawfulMonad m] {n : Nat} : ∃ (z : Nat), ( fact n : m Nat) = step n >>= fun _ => pure z :=
  by induction n with
  | zero => simp only [fact] ; rw [step_zero] ; existsi 1; rw [pure_bind]
  | succ n ih =>
      simp only [fact];
      rcases ih with ⟨z, hz⟩; rw [hz];
      existsi ((n+1) * z);
      simp [← step_add];

variable {α : Type}

def cmpInsert (cmp : α → α → Ordering) (x : α) (L : List α) : m (List α) :=
  match L with
  | [] => pure [x]
  | y::xs => do let _ ← step (1 : Nat)
                let L' ← cmpInsert cmp x xs
                pure (match cmp x y
                      with | Ordering.lt => x::y::xs
                           | _ => y::L')

def inSort (cmp : α → α → Ordering) (L : List α) : m (List α) :=
  match L with
    | [] => pure []
    | x::xs => do
      let L' ← inSort cmp xs
      let L'' ← (cmpInsert cmp x L')
      pure (L'')


theorem insertBound [LawfulMonad m] (cmp : α → α → Ordering) (x : α) (L : List α) :
                    (∃ L' : List α, ∃ c : Nat, c ≤ (List.length L) ∧ List.length L' = List.length L + 1 ∧
                    (cmpInsert cmp x L : m (List α)) = step c >>= fun _ => pure L') :=

  by induction L with

  | nil => simp only [cmpInsert] ;
           existsi [x] ; existsi 0;
           simp only [List.length_nil, List.length_cons];
           simp only [Nat.zero_le, true_and];
           rw [step_zero, pure_bind];

  | cons y ys ih => simp only [cmpInsert] ;
                    rcases ih with ⟨L', c, hc⟩ ; rw [hc.right.right];
                    cases cmp x y with
                    | lt =>  existsi x::y::ys, (c + 1);
                             simp only [List.length_cons, Nat.add_le_add_iff_right, hc.left, true_and];
                             simp only [pure_bind, bind_assoc, ← step_add];

                    --Surely there is a way to get rid of all this boilerplate here for the following two cases
                    | gt => simp only [List.length_cons];
                            existsi y::L', (c + 1);
                            simp only [Nat.add_le_add_iff_right, hc.left, true_and];
                            simp only [pure_bind, bind_assoc, ← step_add, List.length_cons];
                            rw [and_true]; rw [hc.right.left];

                    | eq => simp only [List.length_cons];
                            existsi y::L', (c + 1);
                            simp only [Nat.add_le_add_iff_right, hc.left, true_and];
                            simp only [pure_bind, bind_assoc, ← step_add, List.length_cons];
                            rw [and_true]; rw [hc.right.left];

theorem insertCost [LawfulMonad m] [LawfulMonadStep Nat m] (cmp : α → α → Ordering) (x : α) (L : List α) :
                     IsBounded (m := m) (cmpInsert cmp x L) (List.length L) := sorry
                    --  by have h := insertBound cmp x L



theorem inSortBound [LawfulMonad m] {cmp : α → α → Ordering} {L : List α} :
                                    ( ∃ L' : List α, ∃ c : Nat, c ≤ (List.length L)*(List.length L) ∧ List.length L = List.length L'∧
                                                    (inSort cmp L : m (List α)) = step c >>= fun _ => pure L') :=
  by induction L with

  | nil =>  existsi [];
            simp only [inSort, List.length_nil, Nat.mul_zero, Nat.le_zero_eq, exists_eq_left];
            rw [step_zero, pure_bind, true_and];

  | cons y ys ih => simp only [inSort, List.length_cons];
                    rcases ih with ⟨L', c, h⟩; rw [h.right.right];
                    simp only [pure_bind, bind_assoc];
                    have h := insertBound (m := m) cmp y L' ;
                    rcases h with ⟨L1, c1, p⟩; rw [p.right.right];
                    existsi L1, (c1 + c);
                    simp only [pure_bind, bind_assoc, ← step_add, and_true];
                    simp only [Nat.mul_add, Nat.add_mul, mul_one, one_mul];
                    omega;


def merge (cmp : α → α → m Ordering) (L : List α) (R : List α) : m (List α) :=
  match L, R with
    | [], [] => pure ([])
    | x::xs, [] => pure (x::xs)
    | [], y::ys => pure (y::ys)
    | x::xs, y::ys => do
                        let _ ← step (1 : Nat)
                        match ← cmp x y with
                          | Ordering.lt =>
                            let M ← merge cmp (x::xs) ys
                            pure (y::M)
                          | _ =>
                            let M ← merge cmp xs (y::ys)
                            pure (x::M)

--Get the first half of the list
-- def first (L : List α) : List α :=
--   let n := List.length L ;
--   let L' := List.take (n/2) L;
--   L'

--Get the second half of the list
-- def last (L : List α) : List α :=
--   let n := List.length L;
--   let L' := List.drop (n/2) L;
--   pure L'

/-- Splitting a list into two halves, together with a proof that the halves are less than the
  original list, assuming the list has at least two elements. -/
def List.splitHalfAtLeastTwo (L : List α) (h : L.length ≥ 2) :
    {left : List α // left.length < L.length} × {right : List α // right.length < L.length} := by
  let halves := L.splitAt (L.length / 2)
  refine ⟨⟨halves.1, ?_⟩, ⟨halves.2, ?_⟩⟩
  all_goals simp [halves]; omega

def mSort (cmp : α → α → m Ordering) (L : List α) : m (List α) :=
  match h : L with
    | [] => pure ([])
    | [x] => pure [x]
    | x :: y :: _ => do
      let ⟨⟨left, h1⟩, ⟨right, h2⟩⟩ := L.splitHalfAtLeastTwo (by simp [h])
      let lsort ← (mSort cmp left)
      let rsort ← (mSort cmp right)
      merge cmp lsort rsort
termination_by L.length
decreasing_by
  · simp [← h, h1]
  · simp [← h, h2]

theorem mergeBound [LawfulMonad m] {cmp : α → α → m Ordering} (L : List α) (R : List α) :
                   (∃ L' : List α, ∃ c : Nat, c ≤ List.length L + List.length R ∧
                   ((merge cmp L R) : m (List α)) = step c >>= fun _ => pure L') :=

  by induction L with

    | nil => (induction R with
                | nil => simp only [List.length_nil, add_zero]
                         existsi [], 0; simp only [merge, step_zero, pure_bind, and_true];
                         omega

                | cons y ys ih => rcases ih with ⟨L', h⟩;
                                  existsi (y::ys), 0;
                                  simp only [List.length_nil, zero_add, merge, step_zero, pure_bind];
                                  simp only [List.length_cons, Nat.le_add_left, and_self]
                                  )

    | cons x xs ih => (induction R with
                        | nil => rcases ih with ⟨L', h⟩;
                                  existsi (x::xs), 0;
                                  simp only [List.length_nil, merge, step_zero, pure_bind];
                                  simp only [List.length_cons, Nat.le_add_left, and_self]

                        | cons y ys ih2 => sorry
                        )


--Goals: implement functions with this monad, instrument with step, prove bounds

--todo : add some kind of other composition theorem for steps?

-- def compose {α β γ : Type} (f : β → m γ) (g : α → m β) (x : α) : m γ :=
--                       do let _ ← step 1
--                          let res ← g x
--                          let res' ← f res
--                          pure (res')

-- theorem composeBound {x : α} (gbound : ∃ c_g : Nat, ∃ y : β, g x = step c_g >>= fun _ => pure y)
--                              (fbound : ∃ c_f : Nat, ∃ z : γ, f (g x) = step c_f >>= fun _ => pure z)

-- define classes wrt synthetic step notion (think about more)

-- instrument with oracle computation framework

-- look for cslib on lean chat in zulip?

-- TODO: Implement mergeSort with proper termination proof
-- This would require more complex termination arguments than the simple examples above
