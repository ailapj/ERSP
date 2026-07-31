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
def events : List TimedEvent := [
    {
      timestamp := 0,
      event := Event.NoPulseDetected
    },
    {
      timestamp := 0,
      event := Event.CPRStarted
    },
    {
      timestamp := 120,
      event := Event.TimerExpired TimerKind.CPR
    },
    {
      timestamp := 120,
      event := Event.CPRDone
    },
    { timestamp := 130,
      event := Event.EpinephrineGiven
    },
    {timestamp := 200,
      event := Event.ShockDelivered}
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
      updateState sp.1 sp.2 te.event)
    (initialState, initialPatient)

def epiResult :=
  events.foldl
    (fun monitor te =>
      updateEpiMonitor monitor te)
    initialMonitor


#eval final
#eval ACLSOutput final.1 final.2

-- TODO: prove that the example trace above is not violating the epiRule
example (h : 0 < exTrace.length) :
    Trace.satisfies exTrace 0 h epiRule := by
  sorry
