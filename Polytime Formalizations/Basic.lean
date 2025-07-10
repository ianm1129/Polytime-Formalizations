import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Algebra.Order.Monoid.Basic
import ToMathlib.Control.Lawful.MonadState


/-!
  # Monad Cost

  This file defines the type class `MonadCost` for monads equipped with a cost function.
  We also define the laws that a cost function must satisfy in the `LawfulMonadCost` type class.
-/

universe u v w

class Step (C : Type*) [AddCommMonoid C] (m : Type u → Type v) extends Monad m where
  step : C → m PUnit
  step_0 : step (0 : C) = (pure PUnit.unit : m PUnit)
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



variable (α : Type)

inductive Order where
        | LESS : Order
        | GREATER : Order
        | EQUAL : Order

def cmpInsert (cmp : α → α → Order) (x : α) (L : List α) : m (List α) :=
  match L with
  | [] => pure [x]
  | y::xs => do let _ ← Step.step (1 : Nat)
                let L' ← cmpInsert cmp x xs
                pure (match cmp x y
                      with | Order.LESS => x::y::xs
                           | _ => y::L')

def inSort (cmp : α → α → Order) (L : List α) : m (List α) :=
  match L with
    | [] => pure []
    | x::xs => do
      let L' ← inSort cmp xs
      let L'' ← (cmpInsert (α) cmp x L')
      pure (L'')


theorem insertBound [LawfulMonad m] {α : Type} (cmp : α → α → Order) (x : α) (L : List α) :
                    (∃ L' : List α, ∃ c : Nat, c ≤ (List.length L) ∧ List.length L' = List.length L + 1 ∧
                    (cmpInsert (α) cmp x L : m (List α)) = Step.step c >>= fun _ => pure L') :=

  by induction L with

  | nil => simp only [cmpInsert] ;
           existsi [x] ; existsi 0;
           simp only [List.length_nil, List.length_cons];
           simp only [Nat.zero_le, true_and];
           rw [Step.step_0, pure_bind];

  | cons y ys ih => simp only [cmpInsert] ;
                    rcases ih with ⟨L', c, hc⟩ ; rw [hc.right.right];
                    match cmp x y with
                    | Order.LESS =>   existsi x::y::ys, (c + 1);
                                      simp only [List.length_cons, Nat.add_le_add_iff_right, hc.left, true_and];
                                      simp only [pure_bind, bind_assoc, ← Step.step_add];

                    --Surely there is a way to get rid of all this boilerplate here for the following two cases
                    | Order.GREATER => simp only [List.length_cons];
                                       existsi y::L', (c + 1);
                                       simp only [Nat.add_le_add_iff_right, hc.left, true_and];
                                       simp only [pure_bind, bind_assoc, ← Step.step_add, List.length_cons];
                                       rw [and_true]; rw [hc.right.left];

                    | Order.EQUAL => simp only [List.length_cons];
                                       existsi y::L', (c + 1);
                                       simp only [Nat.add_le_add_iff_right, hc.left, true_and];
                                       simp only [pure_bind, bind_assoc, ← Step.step_add, List.length_cons];
                                       rw [and_true]; rw [hc.right.left];


theorem inSortBound [LawfulMonad m] {α : Type} {cmp : α → α → Order} {L : List α} :
                                    ( ∃ L' : List α, ∃ c : Nat, c ≤ (List.length L)*(List.length L) ∧ List.length L = List.length L'∧
                                                    (inSort (α) cmp L : m (List α)) = Step.step c >>= fun _ => pure L') :=
  by induction L with

  | nil =>  existsi [];
            simp only [inSort, List.length_nil, Nat.mul_zero, Nat.le_zero_eq, exists_eq_left];
            rw [Step.step_0, pure_bind, true_and];

  | cons y ys ih => simp only [inSort, List.length_cons];
                    rcases ih with ⟨L', c, h⟩; rw [h.right.right];
                    simp only [pure_bind, bind_assoc];
                    have h := insertBound (m := m) cmp y L' ;
                    rcases h with ⟨L1, c1, p⟩; rw [p.right.right];
                    existsi L1, (c1 + c);
                    simp only [pure_bind, bind_assoc, ← Step.step_add, and_true];
                    simp only [Nat.mul_add, Nat.add_mul, mul_one, one_mul];
                    omega;


def merge (cmp : α → α → Order) (L : List α) (R : List α) : m (List α) :=
  match L, R with
    | [], [] => pure ([])
    | x::xs, [] => pure (x::xs)
    | [], y::ys => pure (y::ys)
    | x::xs, y::ys => do
                        let _ ← Step.step (1 : Nat)
                        match cmp x y with
                          | Order.LESS =>
                            let M ← merge cmp (x::xs) ys
                            pure (y::M)
                          | _ =>
                            let M ← merge cmp xs (y::ys)
                            pure (x::M)

--Get the first half of the list
def first (L : List α) : m (List α) :=
  let n := List.length L ;
  let L' := List.take (n/2) L;
  do let _ ← Step.step (0 : Nat)
     pure L'

--Get the second half of the list
def last (L : List α) : m (List α) :=
  let n := List.length L;
  let L' := List.drop (n/2) L;
  pure L'

meta def mSort (cmp : α → α → Order) (L : List α) : m (List α):=
  match L with
    | [] => pure ([])
    | _ => do let left ← first (α) L
              let right ← last (α) L
              let lsort ← (mSort cmp left)
              let rsort ← (mSort cmp right)
              let merged ← (merge (α) cmp lsort rsort)
              pure (merged)

theorem mergeBound [LawfulMonad m] {a : Type} {cmp : α → α → Order} (L : List α) (R : List α) :
                   (∃ L' : List α, ∃ c : Nat, c ≤ List.length L + List.length R ∧
                   ((merge α cmp L R) : m (List α)) = Step.step c >>= fun _ => pure L') :=

  by induction L with

    | nil => (induction R with
                | nil => simp only [List.length_nil, add_zero]
                         existsi [], 0; simp only [merge, Step.step_0, pure_bind, and_true];
                         omega

                | cons y ys ih => rcases ih with ⟨L', h⟩;
                                  existsi (y::ys), 0;
                                  simp only [List.length_nil, zero_add, merge, Step.step_0, pure_bind];
                                  simp only [List.length_cons, Nat.le_add_left, and_self]
                                  )

    | cons x xs ih => (induction R with
                        | nil => rcases ih with ⟨L', h⟩;
                                  existsi (x::xs), 0;
                                  simp only [List.length_nil, merge, Step.step_0, pure_bind];
                                  simp only [List.length_cons, Nat.le_add_left, and_self]

                        | cons y ys ih2 => sorry)


--Goals: implement functions with this monad, instrument with cost, prove bounds

--todo : add some kind of other composition theorem for costs?

-- def compose {α β γ : Type} (f : β → m γ) (g : α → m β) (x : α) : m γ :=
--                       do let _ ← Step.step 1
--                          let res ← g x
--                          let res' ← f res
--                          pure (res')

-- theorem composeBound {x : α} (gbound : ∃ c_g : Nat, ∃ y : β, g x = Step.step c_g >>= fun _ => pure y)
--                              (fbound : ∃ c_f : Nat, ∃ z : γ, f (g x) = Step.step c_f >>= fun _ => pure z)

-- define classes wrt synthetic cost notion (think about more)

-- instrument with oracle computation framework

-- look for cslib on lean chat in zulip?
