import Tutorial.Lean.ACLSMTL
import Tutorial.Lean.LeanMTL

def initialPatient : ArrestPatient := {
  rhythm := none,
  pulse := none,
  shockCount := 0,
  cprCycle := 0,
  epinephrineCount := 0,
  amiodaroneOrLidocaineCount := 0,
  monitorAttached := false,
  defibrillatorAttached := false,
  vascularAccess := VascularAccess.None,
  airway := Airway.Basic,
  timers := [],
  latestEvent := none
}

def initialState := ArrestState.InitialAssessment

-- this is the list of TimedEvents that have occured
def events : List Event := [
    Event.CPRStarted,
    Event.AirwayPlaced
]

-- example of a trace, which is simply a list of TimedEvents, and the arbitary Trace.state type is initialized to Events
def exTrace : Trace Event :=
[
  {time := 0, state := Event.CPRStarted} ,
  {time := 100, state := Event.EpinephrineGiven}

]

def final :=
  events.foldl
    (fun (sp : ArrestState × ArrestPatient) te =>
      updateState sp.1 sp.2 te)
    (initialState, initialPatient)



#eval final
#eval ACLSOutput final.1 final.2

-- TODO: prove that the example trace above is not violating the epiRule
example (h : 0 < exTrace.length) :
    Trace.satisfies exTrace 0 h epiRule := by
  sorry
