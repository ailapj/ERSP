import Tutorial.Lean.ACLS

def user : ArrestState × ArrestPatient :=
  let s₀ := (ArrestState.InitialAssessment,
    { rhythm := none
      pulse := none
      shockCount := 0
      cprCycle := 0
      epinephrineCount := 0
      amiodaroneOrLidocaineCount := 0
      monitorAttached := false
      defibrillatorAttached := false
      vascularAccess := VascularAccess.None
      airway := Airway.Basic
      timers := []
      latestEvent := none })
  let s₁ := updateState s₀.1 s₀.2 Event.NoPulseDetected
  let s₂ := updateState s₁.1 s₁.2 Event.CPRStarted
  let s₃ := updateState s₂.1 s₂.2 Event.AllEquipmentAttached
  let s₄ := updateState s₃.1 s₃.2 (Event.RhythmObserved Rhythm.Asystole)
  let s₅ := updateState s₄.1 s₄.2 Event.EpinephrineGiven
  s₅

#eval ACLSOutput user.1 user.2
#eval user.timers
