-- source:  https://cpr.heart.org/en/resuscitation-science/cpr-and-ecc-guidelines/algorithms
-- blue action box = ArrestState + actions
-- red decision diamond = match on patient observation
-- arrow = nextState branch
-- loop back arrow = transition to earlier states

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

def optionNot : Option Bool → Option Bool
| some true => some false
| some false => some true
| none => none

inductive Rhythm
  | VentricularFibrillation
  | PulselessVT
  | Asystole
  | PulselessElectricalActivity
deriving DecidableEq, Repr

inductive Pulse where
  | Present
  | Absent
deriving DecidableEq, Repr

def Rhythm.isShockable : Rhythm → Prop
| .VentricularFibrillation => True
| .PulselessVT             => True
| _                        => False

def Rhythm.isShockableBool : Rhythm → Bool
| .VentricularFibrillation => true
| .PulselessVT            => true
| _                       => false


-- types of vascular access, (TODO: IV is preferred, if not, then IO)
inductive VascularAccess where
  | None
  | IV_IO
deriving DecidableEq, Repr

inductive Airway where
  | Basic
  | Advanced
deriving DecidableEq, Repr


-- Timer kinds to evaluate different procedures
inductive TimerKind where
  | CPR
  | Epinephrine
  | Antiarrhythmic
deriving DecidableEq, Repr

structure Timer where
  duration: Nat
  type: TimerKind
deriving DecidableEq, Repr

-- possible states represented in the algorithm. numbers match the AHA algorithm
inductive ArrestState where
  | InitialAssessment
  | InitialACLS
  | CPR
  | RhythmAnalysis
  | ROSC
  | Terminated
deriving DecidableEq, Repr

-- possible events that deteremine the decision tree branch
inductive Event
| CPRStarted
| CPRTimerStarted
| CPRDone
| EntireACLSCompleted
| RhythmObserved (r : Rhythm)
| ShockDelivered
| EpinephrineGiven
| EpinephrineTimerStarted
| AmiodaroneOrLidocaineGiven
| AmidaroneLidocaineTimerStarted
| PulseDetected
| NoPulseDetected
| IV_IOEstablished
| DefibrillatorAttached
| MonitorAttached
| AllEquipmentAttached
| AirwayPlaced
| TimerExpired (t: TimerKind)
| PostCPRDone
deriving DecidableEq, Repr

-- possible actions the professional can take
inductive Action where
  | StartHighQualityCPR
  | AnalyzeRhythm
  | CheckPulse
  | DeliverShock
  | AttachMonitor
  | AttachDefibrillator
  | ObtainIVIO
  | AdministerEpinephrine
  | AdministerAmiodaroneOrLidocaine
  | GiveOxygen
  | PlaceAdvancedAirway
  | UseCapnography
  | TreatReversibleCauses
  | FinishTreatment
deriving DecidableEq, Repr

-- could also divide these into PatientObservatin, TreatmentHistory, Equipment, etc.
structure ArrestPatient where
  rhythm : Option Rhythm
  pulse : Option Pulse --Present or Absent

  shockCount : Nat
  cprCycle: Nat

  epinephrineCount : Nat
  amiodaroneOrLidocaineCount : Nat

  monitorAttached : Bool
  defibrillatorAttached : Bool

  vascularAccess : VascularAccess

  airway: Airway

  timers : List Timer

  latestEvent : Option Event
deriving DecidableEq, Repr


-- structure Reminder where
--   message : String
--   -- (TODO) remainingSeconds: Option Nat
-- deriving Repr

structure ProtocolOutput where
  actions : List Action
  reminders : List String
deriving DecidableEq, Repr


def ACLSOutput
  (s : ArrestState)
  (p : ArrestPatient)
  : ProtocolOutput :=
  match s with
  | .InitialAssessment =>
      match p.pulse with
      | Pulse.Present =>
          { actions := [.FinishTreatment]
            reminders := ["Ensure patient is good to leave"]}
      | Pulse.Absent =>
          { actions := [.StartHighQualityCPR]
            reminders := [ "Start CPR immedietly"]}
      | none =>
          { actions := [.CheckPulse]
            reminders := [ "Check pulse and breathing for 5-10 seconds"] }
    | .InitialACLS =>
      { actions :=
          [ .GiveOxygen
          , .AttachMonitor
          , .AttachDefibrillator
          , .ObtainIVIO ]
        reminders :=
          [ "Perform CPR for 2 minutes"
          , "Maintain compression rate 100-120/min"
          , "Allow full chest recoil by pushing down at least 5cm (2inch)"
          , "Give enough air for visible chest rise" ] }

-- change this CPR to be CPRShockable and CPRNonShockable
  | .CPR =>
      let baseActions := [ Action.StartHighQualityCPR ]
      let baseReminders :=
      [ "Perform CPR for 2 minutes"
      , "Maintain compression rate 100-120/min"
      , "Allow full chest recoil by pushing down at least 5cm (2 inch)"
      , "Give enough air for visible chest rise"
      , "Change compressor every 2 minutes"
      ]
      let rhythmActions :=
        match p.rhythm with
        | none => [Action.AnalyzeRhythm]
        | some _ => []
      let epiActions :=
        if p.shockCount >= 2 && p.shockCount % 2 == 0 then
          [ Action.AdministerEpinephrine ]
        else []
      let antiArrhythmicAction :=
        if p.shockCount >= 3 && p.shockCount % 2 == 1 then
          match p.rhythm with
          | some r =>
              if r.isShockableBool then
                [ Action.AdministerAmiodaroneOrLidocaine ]
              else []
          | none => []
        else []

        let actions :=
          baseActions
          ++ epiActions
          ++ antiArrhythmicAction
          ++ rhythmActions
          ++ [Action.PlaceAdvancedAirway, Action.UseCapnography]

        let reminders :=
          baseReminders
          ++ (if Action.AdministerEpinephrine ∈ actions then
                ["Administer 1 mg epinephrine. Next one coming up in 3-5 minutes."]
              else
                [])
          ++ (if Action.AdministerAmiodaroneOrLidocaine ∈ actions && p.amiodaroneOrLidocaineCount = 0 then
                ["Administer the first dose of amiodarone 300 mg IV push or lidocaine 1 to 1.5 mg/kg"]
              else if Action.AdministerAmiodaroneOrLidocaine ∈ actions && p.amiodaroneOrLidocaineCount > 0 then
                ["Administer a lower dose of amidoarone,150 mg IV push or lidocanine 0.5 to 0.75 mg/kg"]
              else
                [])
          ++ (if Action.AnalyzeRhythm ∈ actions then
                ["Analyze the Rhythm to detemine shockability immedietly"]
              else
                ["Next rhythm analysis when CPR timer expires"])
          ++ (if p.airway == Airway.Advanced then
                ["Since advanced airway is placed, give breaths every 6 seconds, while maintaining compressions"]
              else
              [])
        { actions := actions
          reminders := reminders }

  | .RhythmAnalysis =>
      match p.rhythm with
      | some r =>
          if r.isShockableBool then
            { actions := [ .DeliverShock ]
              reminders :=
                [ "Resume CPR immediately after shock"
                , "Depending on the defib branch, Monophasic, Zoll, Philips, Stryker/LifePak
                use 360J, 120J, 150J, 200J respectively. " ] }
          else
            { actions :=
                [ .StartHighQualityCPR
                , .TreatReversibleCauses ]
              reminders :=
                [ "Administer epinephrine as early as possible" ] }

      | none =>
          { actions := [ .AnalyzeRhythm ]
            reminders := [] }

  | .ROSC =>
      { actions := []
        reminders := [ "Begin post-cardiac arrest care" ] }

  | .Terminated =>
      { actions := []
        reminders := [] }


def updateState
  (state : ArrestState)
  (patient : ArrestPatient)
  (e : Event)
  : ArrestState × ArrestPatient :=
  match e with
  | .CPRStarted =>

      let updated := {patient with
      latestEvent := Event.CPRStarted
      timers :=
        patient.timers ++
        [
          {
            duration := 120,
            type := TimerKind.CPR
          }
        ]
      }
      if state == .InitialAssessment then
      (.InitialACLS, updated)
      else
      (.CPR, updated)
  | .EntireACLSCompleted =>
      (.Terminated, {patient with latestEvent := Event.EntireACLSCompleted})
  | .RhythmObserved r =>
      let updated := { patient with
                        rhythm := some r
                        latestEvent := Event.RhythmObserved r}
      (.RhythmAnalysis, updated)
  | .ShockDelivered =>
      let updated :=
        { patient with
            shockCount := patient.shockCount + 1
            latestEvent := Event.ShockDelivered}
      (.CPR, updated)
  | .EpinephrineGiven =>
      let updated :=
        { patient with
            epinephrineCount := patient.epinephrineCount + 1
            timers :=
              patient.timers ++
              [
                {
                  duration := 240,
                  type := TimerKind.Epinephrine
                }
              ]
        }
    (.RhythmAnalysis, updated)
  | .AmiodaroneOrLidocaineGiven =>
      let updated :=
        { patient with
            amiodaroneOrLidocaineCount :=
              patient.amiodaroneOrLidocaineCount + 1
            timers :=
              patient.timers ++
              [
                {
                  duration := 240,
                  type := TimerKind.Antiarrhythmic
                }
              ]
            latestEvent := Event.AmiodaroneOrLidocaineGiven}
      (.RhythmAnalysis, updated)
  | .PulseDetected =>
      let updated := { patient with pulse := some Pulse.Present
                                    latestEvent := Event.PulseDetected }
      (.ROSC, updated)
  | .NoPulseDetected =>
      let updated := { patient with pulse := some Pulse.Absent
                                    latestEvent := Event.NoPulseDetected}
      (.InitialAssessment, updated)
  | .IV_IOEstablished =>
    let updated := { patient with vascularAccess := VascularAccess.IV_IO
                                  latestEvent := Event.IV_IOEstablished}
    (state, updated)
  | .DefibrillatorAttached =>
      let updated := { patient with defibrillatorAttached := true
                                    latestEvent := Event.DefibrillatorAttached}
      (state, updated)
  | .MonitorAttached =>
      let updated := { patient with monitorAttached := true
                                    latestEvent := Event.MonitorAttached}
      (state, updated)
  | .AllEquipmentAttached =>
      let updated := { patient with
        defibrillatorAttached := true
        monitorAttached := true
        vascularAccess := VascularAccess.IV_IO
        latestEvent := Event.AllEquipmentAttached
      }
      (state, updated)
  | .CPRDone =>
      let updated := { patient with cprCycle := patient.cprCycle + 1
                                    latestEvent := Event.CPRDone}
      (.RhythmAnalysis, updated)
  | .AirwayPlaced =>
      let updated := { patient with airway := Airway.Advanced
                                    latestEvent := Event.AirwayPlaced}
      (state, updated)
  | .TimerExpired timerKind =>
      (state,
        { patient with
            timers :=
              patient.timers.filter
                (fun t => t.type != timerKind)
            latestEvent := Event.TimerExpired timerKind
        })
  | .PostCPRDone =>
    (.Terminated, { patient with latestEvent := Event.PostCPRDone})

  | .CPRTimerStarted =>
    (state, { patient with latestEvent := some Event.CPRTimerStarted})
  | .EpinephrineTimerStarted =>
    (state, { patient with latestEvent := some Event.EpinephrineTimerStarted})
  | .AmidaroneLidocaineTimerStarted =>
    (state, { patient with latestEvent := some Event.AmidaroneLidocaineTimerStarted})
