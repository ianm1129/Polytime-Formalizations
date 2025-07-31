import «Polytime Formalizations».Basic
import VCVio

/-!
 Formalizing cost of procedure calls
-/

open OracleComp OracleSpec

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
