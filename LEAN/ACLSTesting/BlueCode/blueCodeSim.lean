import Tutorial.Lean.ACLS

-- Ms. Jones is unresponsive/unconscious.
-- User has confirmed: no pulse detected.
-- User has started CPR and attached defibrillator pads (and called code blue).
-- User reports a shockable rhythm on the monitor.
-- User has delivered a shock. About 1 minute has passed.
-- User now reports asystole — they say "we have asystole we have gotten a rhythm"
-- This means the rhythm check after CPR shows asystole (a non-shockable rhythm).
-- User has given 1 mg of epinephrine.
-- User reports: she's not breathing, blood pressure is good.
-- Not breathing is consistent with cardiac arrest (already known).
-- Blood pressure being "good" is noted but does not change the arrest state —
-- the patient still has asystole and no pulse was re-confirmed.
-- No new events change the state; we are still in RhythmAnalysis with Asystole.

def msJones : ArrestPatient :=
{
  rhythm := none
  pulse := none

  shockCount := 0
  cprCycle := 0

  epinephrineCount := 0
  amiodaroneOrLidocaineCount := 0

  monitorAttached := false
  defibrillatorAttached := false

  vascularAccess := VascularAccess.None

  airway := Airway.Basic

  timers :=
  {
    duration := 0
    type := TimerKind.Epinephrine
  }
  latestEvent := none
}

def currentState : ArrestState := ArrestState.InitialAssessment

-- Step 1: User reports no pulse detected.
def step1 := updateState currentState msJones Event.NoPulseDetected
def stateAfterNoPulse : ArrestState := step1.1
def msJonesAfterNoPulse : ArrestPatient := step1.2

#eval stateAfterNoPulse
-- ArrestState.InitialAssessment

#eval msJonesAfterNoPulse.pulse
-- some (Pulse.Absent)

#eval ACLSOutput stateAfterNoPulse msJonesAfterNoPulse
-- actions = [StartHighQualityCPR], reminders = ["Start CPR immedietly"]

-- Step 2: User starts CPR. This transitions from InitialAssessment to InitialACLS.
def step2 := updateState stateAfterNoPulse msJonesAfterNoPulse Event.CPRStarted
def stateAfterCPRStarted : ArrestState := step2.1
def msJonesAfterCPRStarted : ArrestPatient := step2.2

#eval stateAfterCPRStarted
-- ArrestState.InitialACLS

-- Step 3: User attached defibrillator pads.
def step3 := updateState stateAfterCPRStarted msJonesAfterCPRStarted Event.DefibrillatorAttached
def stateAfterDefib : ArrestState := step3.1
def msJonesAfterDefib : ArrestPatient := step3.2

#eval stateAfterDefib
-- ArrestState.InitialACLS

#eval msJonesAfterDefib.defibrillatorAttached
-- true

-- Step 4: Code blue called implies monitor is also being attached (pads serve as monitor).
def step4 := updateState stateAfterDefib msJonesAfterDefib Event.MonitorAttached
def stateAfterMonitor : ArrestState := step4.1
def msJonesAfterMonitor : ArrestPatient := step4.2

#eval stateAfterMonitor
-- ArrestState.InitialACLS

#eval msJonesAfterMonitor.monitorAttached
-- true

-- Get the next actions and reminders from InitialACLS
#eval ACLSOutput stateAfterMonitor msJonesAfterMonitor
-- actions = [GiveOxygen, AttachMonitor, AttachDefibrillator, ObtainIVIO]
-- reminders include CPR quality reminders

-- Step 5: User reports a shockable rhythm. Using VentricularFibrillation as the
-- specific shockable rhythm (user said "shockable rhythm" without specifying VF vs pVT;
-- VentricularFibrillation is used as the representative shockable rhythm).
def step5 := updateState stateAfterMonitor msJonesAfterMonitor (Event.RhythmObserved Rhythm.VentricularFibrillation)
def stateAfterRhythm : ArrestState := step5.1
def msJonesAfterRhythm : ArrestPatient := step5.2

#eval stateAfterRhythm
-- ArrestState.RhythmAnalysis

#eval msJonesAfterRhythm.rhythm
-- some (Rhythm.VentricularFibrillation)

-- Get the next actions and reminders from RhythmAnalysis with a shockable rhythm
#eval ACLSOutput stateAfterRhythm msJonesAfterRhythm
-- actions = [DeliverShock], reminders = ["Resume CPR immediately after shock"]

-- Step 6: User has delivered the shock. shockCount goes from 0 to 1. State transitions to CPR.
def step6 := updateState stateAfterRhythm msJonesAfterRhythm Event.ShockDelivered
def stateAfterShock : ArrestState := step6.1
def msJonesAfterShock : ArrestPatient := step6.2

#eval stateAfterShock
-- ArrestState.CPR

#eval msJonesAfterShock.shockCount
-- 1

-- Get the next actions and reminders from CPR state after first shock.
#eval ACLSOutput stateAfterShock msJonesAfterShock
-- actions = [StartHighQualityCPR, PlaceAdvancedAirway, UseCapnography]
-- reminders include CPR quality reminders and "Next rhythm analysis when CPR timer expires"

-- Step 7: CPR cycle completed (user has been doing CPR, now checking rhythm).
-- cprCycle goes from 0 to 1. State transitions to RhythmAnalysis.
def step7 := updateState stateAfterShock msJonesAfterShock Event.CPRDone
def stateAfterCPRDone : ArrestState := step7.1
def msJonesAfterCPRDone : ArrestPatient := step7.2

#eval stateAfterCPRDone
-- ArrestState.RhythmAnalysis

#eval msJonesAfterCPRDone.cprCycle
-- 1

-- Step 8: User reports asystole on rhythm check. This is a non-shockable rhythm.
-- The rhythm has changed from VF to Asystole.
def step8 := updateState stateAfterCPRDone msJonesAfterCPRDone (Event.RhythmObserved Rhythm.Asystole)
def stateAfterAsystole : ArrestState := step8.1
def msJonesAfterAsystole : ArrestPatient := step8.2

#eval stateAfterAsystole
-- ArrestState.RhythmAnalysis

#eval msJonesAfterAsystole.rhythm
-- some (Rhythm.Asystole)

-- Get the next actions and reminders from RhythmAnalysis with a non-shockable rhythm (Asystole).
-- Since Asystole is NOT shockable, the protocol says: StartHighQualityCPR + TreatReversibleCauses
-- Reminder: "Administer epinephrine as early as possible"
#eval ACLSOutput stateAfterAsystole msJonesAfterAsystole
-- actions = [StartHighQualityCPR, TreatReversibleCauses]
-- reminders = ["Administer epinephrine as early as possible"]

-- Step 9: User has given 1 mg of epinephrine. This implies IV/IO access has been established.
-- First, record that IV/IO access is established (user must have access to give epi).
def step9a := updateState stateAfterAsystole msJonesAfterAsystole Event.IV_IOEstablished
def stateAfterIVIO : ArrestState := step9a.1
def msJonesAfterIVIO : ArrestPatient := step9a.2

#eval stateAfterIVIO
-- ArrestState.RhythmAnalysis

#eval msJonesAfterIVIO.vascularAccess
-- VascularAccess.IV_IO

-- Now record epinephrine given. epinephrineCount goes from 0 to 1.
-- Epinephrine timer starts at 240 seconds (4 minutes).
-- State remains RhythmAnalysis per updateState.
def step9b := updateState stateAfterIVIO msJonesAfterIVIO Event.EpinephrineGiven
def stateAfterEpi : ArrestState := step9b.1
def msJonesAfterEpi : ArrestPatient := step9b.2

#eval stateAfterEpi
-- ArrestState.RhythmAnalysis

#eval msJonesAfterEpi.epinephrineCount
-- 1

#eval msJonesAfterEpi.timers
-- some { remaining := 240 }

#eval msJonesAfterEpi.vascularAccess
-- VascularAccess.IV_IO

-- Get the next actions and reminders from RhythmAnalysis.
-- Rhythm is still Asystole (non-shockable), so:
-- actions = [StartHighQualityCPR, TreatReversibleCauses]
-- reminders = ["Administer epinephrine as early as possible"]
-- (Epi has been given; next dose after timer expires in ~4 min)
#eval ACLSOutput stateAfterEpi msJonesAfterEpi
-- actions = [StartHighQualityCPR, TreatReversibleCauses]
-- reminders = ["Administer epinephrine as early as possible"]

-- Step 10: User reports "she's not breathing, blood pressure is good."
-- Not breathing is consistent with the ongoing cardiac arrest (pulse absent, asystole).
-- Blood pressure being "good" is an observation but does not correspond to a state-changing
-- event in the ACLS protocol — the patient remains in cardiac arrest with asystole.
-- The airway is still Basic. The user has not reported placing an advanced airway.
-- No new Event is triggered that changes the ArrestState or ArrestPatient fields.
--
-- The current state remains: RhythmAnalysis with Asystole (non-shockable).
-- The protocol output remains the same.

-- Verify current state and output remain unchanged:
#eval stateAfterEpi
-- ArrestState.RhythmAnalysis

#eval msJonesAfterEpi.rhythm
-- some (Rhythm.Asystole)

#eval msJonesAfterEpi.airway
-- Airway.Basic

#eval ACLSOutput stateAfterEpi msJonesAfterEpi
-- actions = [StartHighQualityCPR, TreatReversibleCauses]
-- reminders = ["Administer epinephrine as early as possible"]
