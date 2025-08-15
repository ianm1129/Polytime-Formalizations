import «Polytime Formalizations».Basic
import VCVio

/-!
 Formalizing cost of procedure calls
-/

#check OracleComp
#check OracleSpec

open OracleComp OracleSpec

universe u

/- Define procedure A -/

/-- A has access to 2 oracles: B and C. Let's say they both take & return dummies. -/

def specForCallBAndC : OracleSpec (Fin 2) := fun _ => (Unit, Unit)

/-- B has access to 1 oracle: C. Let's say it takes & returns dummies. -/

def specForCallC : OracleSpec (Fin 1) := fun _ => (Unit, Unit)

def handleBQuery (procB : OracleComp specForCallC Unit) :
    QueryImpl specForCallBAndC (OracleComp specForCallC) where
  impl | query i t => match i with
    -- If it's a call to B, we run B
    | 0 => procB
    -- If it's a call to C, we also call C
    | 1 => (query (spec := specForCallC) 0 t)

/-- Orchestrator for all procedures. It will run A, and for every query A makes to B, it will run B, handling every query made to C. -/
def procOrchestrator
    (procA : OracleComp specForCallBAndC Unit) (procB : OracleComp specForCallC Unit) :
      OracleComp specForCallC Unit :=
  simulateQ (handleBQuery procB) procA

variable [MonadStep Nat (OracleComp specForCallBAndC)]
  [LawfulMonadStep Nat (OracleComp specForCallBAndC)]
  [MonadStep Nat (OracleComp specForCallC)]
  [LawfulMonadStep Nat (OracleComp specForCallC)]

-- TODO: reason about the cost of the orchestrator based on the cost of the procedures

-- the cost of the orchestrator is at most
-- (cost of `procA`) + (cost of `procB`) * (number of calls from `procA` to `procB`) + (cost of `procC`) * (number of calls from `procA` to `procC` + number of calls from `procB` to `procC`)

--   def countQueriesToAux {n : Nat} {β} (i : Fin n) : OracleComp (fun _ => (Unit, Unit)) β → Nat



--     -- | .pure _ => 0
--     -- -- | .step _ k => countQueriesToAux i (k ())
--     -- | j _ k =>
--     --   let rest := countQueriesToAux i (k ())
--     --   if j = i then rest + 1 else rest
--     -- | .bind x f => countQueriesToBind i x f

--   def countQueriesToBind {n : Nat} {β} {γ} (i : Fin n) : OracleComp (fun _ => (Unit, Unit)) β → (β → OracleComp _ γ) → Nat
--     | .pure a, f => countQueriesToAux i (f a)
--     -- | .step _ k, f => countQueriesToBind i (k ()) f
--     | .query j _ k, f =>
--       let rest := countQueriesToBind i (k ()) f
--       if j = i then rest + 1 else rest
--     | .bind x g, f => countQueriesToBind i x (fun a => countQueriesToBind i (g a) f)
-- end

def countQueriesTo {α : Type} {n : Nat} (i : Fin n) (comp : OracleComp (fun _ : Unit => (Unit, Unit)) α) : Nat :=
  by
    induction comp using OracleComp.construct


lemma orchestrator_cost (procA : OracleComp specForCallBAndC Unit) (procB : OracleComp specForCallC Unit) (a b c : Nat) :
      (IsBounded procA a) → (IsBounded procB b) →
