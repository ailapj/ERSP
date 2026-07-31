namespace moduleOne
/-- Emergency Triage Assessment and Treatment, Manual for participants
    by the World Health Organization
    Module 1: Triage and the "ABCD" Concept
    Assessing Triage categories for children --/

-- Triage levels for child patient care
inductive Triage where
  | Emergency
  | Priority
  | Queue
deriving DecidableEq, Repr

/-- Treatment options-/
inductive Treatment where
  | callSeniorDoctor
  | emergencyInvestigation
  | emergencyTreatment
deriving DecidableEq, Repr

/-- AVPU categories for coma assessment -/
inductive AVPU where
  | Alert
  | Verbal
  | Pain
  | Unresponsive
deriving DecidableEq, Repr

inductive SpeedMeasurement where
  | normal
  | fast
  | slow
deriving DecidableEq, Repr

inductive Temperature where
  | normal
  | slightFever
  | highFever
  | hypothermia
deriving DecidableEq, Repr

inductive BodyPart where
  | hands
  | feet
  | abdomen
  | head
deriving DecidableEq, Repr

inductive Pulse
| normal
| weakFast
| weakSlow
| absent
deriving DecidableEq, Repr

/-- Patient information -/
structure Patient where
  ageInMonth : Nat -- number in months

  breathing : Bool
  airwayObstructed : Bool   -- can be caused by blockage by the tongue, foreign body, swelling around the upper airway or severe croup
  centralCyanosis : Bool   -- A bluish discoloration of the mucous membranes, lips, and tongue

  -- if smiling or crying, no severe respitorary distress, shock, or coma
  smiling : Bool
  crying : Bool

  severeChestIndrawing : Bool
  accessoryMuscleUseBreating : Bool
  unableToTalkEatFeed : Bool
  veryFastBreathing : Bool
  breatingIsTiring : Bool

  warmHands : Bool
  capillaryRefill : Nat -- time in seconds for blood to return to the capillaries after pressure is applied
  pulse : Pulse

  avpu : AVPU

  sunkenEyes : Bool
  skinTurgor : SpeedMeasurement -- pull on skin and measure how quickly it returns to normal position. Slow return indicates dehydration.

  temperature : Temperature
  fracture: Bool
  headInjury: Bool
  acuateAbdominalPain : Bool
  whitePalm : Bool -- measure paleness (sign of anaemia)

  posion : Bool -- hisotry of wallowing druggs ot other dangerous substances (ask guardian)
  agony : Bool -- capturing the pain/agony or restlessness

  urgentReferral : Bool
  wasting : Bool -- look rapidly at arms, legs, chest o assess wasting (marasmus)
  oedema : List BodyPart -- to determine malnutrition (kwashiorkor)
  burn : Bool -- even those that look well can deteriorate rapidly
deriving DecidableEq, Repr

/-- Determining severe respiratory distress -/
def SevereRespiratoryDistress (p : Patient) : Prop :=
  p.unableToTalkEatFeed ∨
  p.severeChestIndrawing ∨
  p.accessoryMuscleUseBreating ∨
  (p.veryFastBreathing ∧
   p.breatingIsTiring)

instance(p : Patient) : Decidable (SevereRespiratoryDistress p) := by
  unfold SevereRespiratoryDistress
  infer_instance

/-- Determining circulation problems (used for C in ABCD)-/
def CirculationProblems (p : Patient) : Prop :=
  p.warmHands = false ∨
  p.capillaryRefill > 3 ∨
  p.pulse = Pulse.weakFast

instance(p : Patient) : Decidable (CirculationProblems p) := by
  unfold CirculationProblems
  infer_instance

/-- Determining coma (used for C in ABCD)-/
def Coma (p : Patient) : Prop :=
  p.avpu = AVPU.Unresponsive

instance(p : Patient) : Decidable (Coma p) := by
  unfold Coma
  infer_instance

/-- A in ABCD, an indication for emergency triage-/
def Airway (p : Patient) : Prop :=
  p.breathing = false ∨
  p.airwayObstructed ∨
  p.centralCyanosis

-- Airway is decidable
instance (p : Patient) : Decidable (Airway p) := by
  unfold Airway
  infer_instance

/-- B in ABCD, an indication for emergency triage-/
def Breathing (p : Patient) : Prop :=
  SevereRespiratoryDistress p

-- Breathing is decidable
instance (p : Patient) : Decidable (Breathing p) := by
  unfold Breathing
  infer_instance


/-- C in ABCD, an indication for emergency triage-/
def CirculationComaConulsion (p : Patient) : Prop :=
  CirculationProblems p ∨
  p.avpu = AVPU.Unresponsive ∨
  p.avpu  = AVPU.Pain ∨
  Coma p

-- CirculationComaConulsion is decidable
instance (p : Patient) : Decidable (CirculationComaConulsion p) := by
  unfold CirculationComaConulsion
  infer_instance

/-- D in ABCD, an indication for emergency triage-/
def Dehydration (p : Patient) : Prop :=
  p.sunkenEyes ∨
  p.skinTurgor = SpeedMeasurement.slow

-- Dehydration is decidable
instance (p : Patient) : Decidable (Dehydration p) := by
  unfold Dehydration
  infer_instance

def Priority (p : Patient) : Prop :=
  -- following the 3 TRP-MOB assessment for Pirority triage
  -- Tiny Baby ( < 2 months)
  p.ageInMonth < 2 ∨
  -- Temperature = child is very hot
  p.temperature = Temperature.highFever ∨
  -- Trauma or other urgent surgical condition
  p.fracture ∨ p.headInjury ∨ p.acuateAbdominalPain ∨
  -- Pallor (severe)
  p.whitePalm ∨
  -- Poisoning
  p.posion ∨
  -- Pain (severe)
  p.agony ∨
  -- Respiratory distress
  SevereRespiratoryDistress p ∨ p.breatingIsTiring ∨ p.veryFastBreathing ∨
  -- Restless, continously irritable, or lethargic
  p.avpu = AVPU.Verbal ∨
  -- Referral (urgent)
  p.urgentReferral ∨
  -- Malnutrition: Visible severe wasting
  p.wasting ∨
  -- Oedema of both feet
  BodyPart.feet ∈ p.oedema ∨
  -- Burns
  p.burn

-- Priority is decidable
instance (p : Patient) : Decidable (Priority p) := by
  unfold Priority
  infer_instance

/-- Triage assessment, returning a Triage categroy based on patient's conditions-/
def TriageAssessment (p : Patient) : Triage :=
  if (Airway p) ∨ (Breathing) p ∨ (CirculationComaConulsion) p ∨ (Dehydration) p
    then Triage.Emergency
  else if Priority p then Triage.Priority
  else Triage.Queue

end moduleOne
