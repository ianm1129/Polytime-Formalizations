import «Polytime Formalizations».Basic
import VCVio

/-!
 Formalizing cost of procedure calls
-/

#check OracleComp
#check OracleSpec

open OracleComp OracleSpec

universe u v

/- Define procedure A -/

/-- A has access to 2 oracles: B and C. Let's say they both take & return dummies. -/

@[reducible]
def specForCallBAndC : OracleSpec (Fin 2) := fun _ => (Unit, Unit)

instance : FiniteRange specForCallBAndC := by
  unfold specForCallBAndC
  refine ⟨?_, ?_⟩
  · intro i; unfold OracleSpec.range; infer_instance
  · intro i; unfold OracleSpec.range; infer_instance

/-- B has access to 1 oracle: C. Let's say it takes & returns dummies. -/

@[reducible]
def specForCallC : OracleSpec (Fin 1) := fun _ => (Unit, Unit)

instance : FiniteRange specForCallC := by
  unfold specForCallC
  refine ⟨?_, ?_⟩
  · intro i; unfold OracleSpec.range; infer_instance
  · intro i; unfold OracleSpec.range; infer_instance

def handleBQuery (procB : OracleComp specForCallC Unit) :
    QueryImpl specForCallBAndC (OracleComp specForCallC) where
  impl | query i t => match i with
    -- If it's a call to B, we run B
    | 0 => procB
    -- If it's a call to C, we also call C
    | 1 => (query (spec := specForCallC) 0 t)

/-- Orchestrator for all procedures. It will run A, and for every query A makes to B, it will run B, handling every query made to C. -/
def handleProcB
    (procA : OracleComp specForCallBAndC Unit) (procB : OracleComp specForCallC Unit) :
      OracleComp specForCallC Unit :=
  simulateQ (handleBQuery procB) procA

def handleCQuery (procC : OracleComp []ₒ Unit) :
    QueryImpl specForCallC (OracleComp []ₒ) where
  impl | query i _ => match i with
    -- If it's a call to C, we run C
    | 0 => procC

def handleProcC (proc : OracleComp specForCallC Unit) (procC : OracleComp []ₒ Unit) :
      OracleComp []ₒ Unit :=
  simulateQ (handleCQuery procC) proc

#check simulateQ_query
#check simulateQ_bind

-- simulateQ_step

-- def handleQueryIWithProc : QueryImpl specForCallProc (OracleComp []ₒ) where
-- handle query by running the procedure, then continuing with the response

-- simulateQ (handleQueryIWithProc) (step a >>= (query i t)) =
-- step (a + cost of proc) >>= simulateQ (handleQueryIWithProc) (query i t)

variable
  -- There is a step function for computations that use no oracles
  [MonadStep Nat (OracleComp []ₒ)]
  -- This step function is lawful for pure and bind
  -- `step 0 = pure ()`
  -- `step a >>= step b = step (a + b)`
  [LawfulMonadStep Nat (OracleComp []ₒ)]
  -- This step function is lawful for failure: `step c >>= failure = failure >>= step c`
  [LawfulAlternativeMonadStep Nat (OracleComp []ₒ)]
  -- [MonadStep Nat (OracleComp specForCallBAndC)]
  -- [LawfulMonadStep Nat (OracleComp specForCallBAndC)]
  -- [MonadStep Nat (OracleComp specForCallC)]
  -- [LawfulMonadStep Nat (OracleComp specForCallC)]

instance {ι : Type u} {spec : OracleSpec ι} : MonadLift []ₒ.OracleQuery spec.OracleQuery where
  monadLift | query i _ => PEmpty.elim i

/-- Given a cost measure on computations that use no oracles, we can define a cost measure on computations that use any set of oracles, by lifting the cost measure. -/
instance {ι : Type u} {spec : OracleSpec ι} : MonadStep Nat (OracleComp spec) where
  step n := liftComp (step n : OracleComp []ₒ Unit) spec

-- instance {ι : Type u} {spec : OracleSpec ι} [FiniteRange spec] :
--     MonadStep (Nat × Nat) (OracleComp spec) where
--   step := fun ⟨liftComp (step (n, m) : OracleComp []ₒ Unit) spec
-- TODO: reason about the cost of the orchestrator based on the cost of the procedures

-- the cost of the orchestrator is at most
-- (cost of `procA`) + (cost of `procB`) * (number of calls from `procA` to `procB`) + (cost of `procC`) * (number of calls from `procA` to `procC` + number of calls from `procB` to `procC`)

def individualQueryBound {ι : Type u} [DecidableEq ι] {spec : OracleSpec ι} [FiniteRange spec] {α : Type v}
    (oa : OracleComp spec α) : ι → ℕ := by
  induction oa using OracleComp.construct' with
  | pure x => exact 0
  | failure => exact 0
  | query_bind i t oa rec_n =>
    exact (fun j => if j = i then 1 else 0) + ∑ x, rec_n x

-- the cost of the orchestrator is at most
-- (cost of `procA`) + (cost of `procB`) * (number of calls from `procA` to `procB`) + (cost of `procC`) * (number of calls from `procA` to `procC` + number of calls from `procB` to `procC`)

lemma orchestrator_cost
    (procA : OracleComp specForCallBAndC Unit)
    (procB : OracleComp specForCallC Unit)
    (procC : OracleComp []ₒ Unit) (a b c : Nat)
      (ha : IsBounded procA a) (hb : IsBounded procB b) (hc : IsBounded procC c) :
      IsBounded (handleProcC (handleProcB procA procB) procC)
        (a + b * individualQueryBound procA 0 +
          c * (individualQueryBound procA 1 + individualQueryBound procB 0)) := by
  sorry
