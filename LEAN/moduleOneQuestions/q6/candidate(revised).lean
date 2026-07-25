import Tutorial.Lean.moduleTwo

-- Safety theorem: A patient with no breathing (airway emergency) is triaged as Emergency
theorem emergency_no_breathing_safe (p : Patient)
    (h_breathing : p.breathing = some Breathing.nonexistent)
    : TriageAssessment p = Triage.Emergency := by
  unfold TriageAssessment
  unfold Emergency
  unfold AirwayABCD
  simp [optionOrList, optionEq, h_breathing]

-- Safety theorem: A patient who is unresponsive (coma) is triaged as Emergency
theorem emergency_unresponsive_safe (p : Patient)
    (h_avpu : p.avpu = some AVPU.Unresponsive)
    : TriageAssessment p = Triage.Emergency := by
  unfold TriageAssessment
  unfold Emergency
  unfold CirculationComaConulsionABCD
  unfold AirwayABCD BreathingABCD DehydrationABCD
  unfold SevereRespiratoryDistress
  unfold CirculationProblems
  unfold hasCyanosis
  simp [optionOrList, optionEq, optionGt, optionAndList, h_avpu]

-- Safety theorem: A tiny baby (age < 2 months) who is not emergency is at least Priority
theorem priority_tiny_baby_safe (p : Patient)
    (h_age : p.ageInMonth = some 1)
    (h_not_emergency : Emergency p = some false)
    : TriageAssessment p = Triage.Priority := by
  unfold TriageAssessment
  simp [h_not_emergency]
  unfold Priority
  simp [optionOrList, optionLt, h_age]