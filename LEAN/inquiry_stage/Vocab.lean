/--
this funciton returns true if any of the conditions in the list are true
it returns false if and only iff all conditions are explicitly false
it will return unknown otherwise -/
def optionOrList : List (Option Bool) → Option Bool
  | [] => some false
  | xs =>
      if xs.any (· == some true) then
        some true
      else if xs.any (· == none) then
        none
      else
        some false

/--
this function returns true if and only if all the conditions are true
it returns false if any of the conditions are false
and unknown (none) otherwise -/
def optionAndList : List (Option Bool) → Option Bool
  | [] => some true
  | xs =>
      if xs.any (· == some false) then
        some false
      else if xs.any (· == none) then
        none
      else
        some true

/--
helper function that takes a decidable equation and a possible value for it
and returns if the equation takes on that value-/
def optionEq [DecidableEq α] (x : Option α) (y : α) : Option Bool :=
  match x with
  | some z => some (z = y)
  | none => none

/--
helper function for determining if a given condition takes a value greater
than a specific given natural number-/
def optionGt (x : Option Nat) (n : Nat) : Option Bool :=
  match x with
  | some m => some (m > n)
  | none => none

/--
helper function for determining if a given condition takes a value less
than a sprcific given natural number -/
def optionLt (x : Option Nat) (n : Nat) : Option Bool :=
  match x with
  | some m => some (m < n)
  | none => none

/--
helper function for determining if a given condition that takes a list contains
a specific given string-/
def optionContains [DecidableEq α] (xs : Option (List α)) (x : α) : Option Bool :=
  match xs with
  | some ys => some (x ∈ ys)
  | none => none

-- Triage levels for child patient care
inductive Triage where
  | Emergency
  | Priority
  | Queue
  | askForInfo
deriving DecidableEq, Repr

-- Treatment actions
inductive Treatment where
  | ManageAirway
  | GiveOxygen
  | KeepWarm
  | MouthFingerSwap
  | Heimlich
  | BackSlaps
  | ChestThrusts
  | AskForInfo
  | RemoveForeignBodyFromMouth
  | CheckBreathing

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
  | tongue
  | lips
  | skin
  | palms
deriving DecidableEq, Repr

inductive Emotion where
  | crying
  | smiling
  | agony  --capturing the pain/agony or restlessness
deriving DecidableEq, Repr

inductive Pulse
  | normal
  | weakFast
  | weakSlow
  | absent
deriving DecidableEq, Repr

inductive Color
  | normal
  | blue
  | purple
  | pale
deriving DecidableEq, Repr

inductive Breathing
  | nonexistent
  | slow
  | normal
  | fast
  | veryFast
deriving DecidableEq, Repr

inductive BodyState
  | normal
  | wasting -- look rapidly at arms, legs, chest to assess wasting (marasmus)
  | burn -- even those that look well can deteriorate rapidly
deriving DecidableEq, Repr

structure PhysicalExam where
  lips : Option Color
  tongue : Option Color
  palms : Option Color
  bodyState: Option (List BodyState) := none
  oedema: Option (List BodyPart) := none
  fracture:  Option Bool := none
  headInjury: Option Bool := none
  acuateAbdominalPain: Option Bool := none
deriving DecidableEq, Repr


/-- Patient information -/
structure Patient where
  ageInMonth : Option Nat := none -- number in months
  -- color of body, state of the body, swelling
  exam: PhysicalExam
  breathing : Option Breathing := none
  airwayObstructed :  Option Bool := none   -- can be caused by blockage by the tongue, foreign body, swelling around the upper airway or severe croup

  -- crying, smiling, agony?
  emotion : Option Emotion := none

  severeChestIndrawing :  Option Bool := none
  accessoryMuscleUseBreating :  Option Bool := none
  unableToTalkEatFeed :  Option Bool := none
  breatingIsTiring :  Option Bool := none

  capillaryRefill :  Option Nat := none -- time in seconds for blood to return to the capillaries after pressure is applied
  pulse : Option Pulse := none

  avpu : Option AVPU := none

  sunkenEyes :  Option Bool := none
  skinTurgor : Option Nat := none -- pull on skin and measure how quickly it returns to normal position. Slow return indicates dehydration.

  temperature :  Option Temperature := none
  poison : Option Bool := none-- hisotry of swallowing druggs ot other dangerous substances (ask guardian)

  urgentReferral :  Option Bool := none
deriving DecidableEq, Repr

def hasCyanosis (p : Patient) : Option Bool :=
  optionOrList [
    optionEq (p.exam.lips) Color.blue,
    optionEq (p.exam.lips) Color.purple,
    optionEq (p.exam.tongue) Color.blue,
    optionEq (p.exam.tongue) Color.purple,
  ]


def hasPalmarPallor (p : Patient) : Option Bool :=
  optionEq (p.exam.lips) Color.pale

/-- Determining severe respiratory distress -/
def SevereRespiratoryDistress (p : Patient) : Option Bool :=
  optionOrList [
    p.unableToTalkEatFeed,
    p.severeChestIndrawing,
    p.accessoryMuscleUseBreating,
    optionAndList [
      optionEq p.breathing Breathing.veryFast,
      p.breatingIsTiring]
  ]

/-- Determining circulation problems (used for C in ABCD)-/
def CirculationProblems (p : Patient) : Option Bool :=
  optionOrList [
    optionGt p.capillaryRefill 3,
    optionEq p.pulse Pulse.weakFast
  ]

/-- A in ABCD, an indication for emergency triage-/
def AirwayABCD (p : Patient) : Option Bool :=
  optionOrList [
    optionEq p.breathing Breathing.nonexistent,
    p.airwayObstructed,
    hasCyanosis p
  ]

/-- B in ABCD, an indication for emergency triage-/
def BreathingABCD (p : Patient) : Option Bool :=
  SevereRespiratoryDistress p


/-- C in ABCD, an indication for emergency triage-/
def CirculationComaConulsionABCD (p : Patient) : Option Bool :=
  optionOrList [
    CirculationProblems p, -- any circulation problems
    optionEq p.avpu AVPU.Unresponsive, -- in coma
    optionEq p.avpu AVPU.Pain -- only responsive to pain
  ]


/-- D in ABCD, an indication for emergency triage-/
def DehydrationABCD (p : Patient) : Option Bool :=
  optionOrList [
    p.sunkenEyes,
    optionGt p.skinTurgor 2
  ]

def Emergency (p : Patient) : Option Bool :=
  optionOrList [
    AirwayABCD p,
    BreathingABCD p,
    CirculationComaConulsionABCD p,
    DehydrationABCD p
  ]

def Priority (p : Patient) : Option Bool :=
  -- following the 3 TRP-MOB assessment for Pirority triage
  optionOrList [
    optionLt p.ageInMonth 2,   -- Tiny Baby ( < 2 months)
    optionEq p.temperature Temperature.highFever, -- Temperature = child is very hot
    -- Trauma or other urgent surgical condition
    p.exam.fracture,
    p.exam.headInjury,
    p.exam.acuateAbdominalPain,
    hasPalmarPallor p,  -- Pallor (severe)
    p.poison, -- Poisoning
    optionEq p.emotion Emotion.agony, -- Pain (severe)
    SevereRespiratoryDistress p, -- respirator distress
    p.breatingIsTiring,
    optionEq p.breathing Breathing.veryFast,
    optionEq p.avpu AVPU.Verbal,  -- Restless, continously irritable, or lethargic
    p.urgentReferral, -- Referral (urgent)
    optionContains (p.exam.bodyState) (BodyState.wasting), -- Malnutrition: Visible severe wasting
    optionContains p.exam.oedema BodyPart.feet, -- Oedema of both feet
    optionContains p.exam.bodyState BodyState.burn -- burns
  ]


/-- Triage assessment, returning a Triage categroy based on patient's conditions-/
def TriageAssessment (p : Patient) : Triage :=
  match Emergency p with
  | some true =>
      Triage.Emergency
  | some false =>
      match Priority p with
      | some true =>
          Triage.Priority
      | some false =>
          Triage.Queue
      | none =>
          Triage.askForInfo

  | none =>
      Triage.askForInfo


-- module 2 treatment plans

-- airway management for chocking child, obstructed airway
def airWayManagement (p : Patient) : List Treatment :=
  let treatment : List Treatment := [Treatment.BackSlaps]
  match p.ageInMonth with
  | some age =>
      if age < 5 then
        treatment ++ [Treatment.ChestThrusts]
      else
        treatment ++ [Treatment.Heimlich]
  | none =>
      let treatment : List Treatment := [Treatment.AskForInfo]
  treatment ++ [Treatment.RemoveForeignBodyFromMouth, Treatment.CheckBreathing]
