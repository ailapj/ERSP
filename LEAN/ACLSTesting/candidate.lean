import Tutorial.Lean.ACLS

-- Patient arrived unconscious. Pulse checked and found absent.
-- We apply Event.NoPulseDetected to update state.

def initialPatient : ArrestPatient :=
{
  rhythm := none
  pulse := none          -- pulse not yet checked at this point

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
    cpr := none
    epinephrine := none
    antiarrhythmic := none
  }
}

def initialState : ArrestState := ArrestState.InitialAssessment

-- User reports no pulse detected. Apply NoPulseDetected event.
def afterNoPulse := updateState initialState initialPatient Event.NoPulseDetected
-- This returns (InitialAssessment, { patient with pulse := some Pulse.Absent })

def state1 : ArrestState := afterNoPulse.1
def patient1 : ArrestPatient := afterNoPulse.2

-- Verify the state transition
#eval state1
-- Expected: ArrestState.InitialAssessment

#eval patient1.pulse
-- Expected: some Pulse.Absent

-- Get the next actions and reminders
#eval ACLSOutput state1 patient1
-- Expected output: actions = [StartHighQualityCPR], reminders = ["Start CPR immedietly"]
-- Since pulse is absent, the protocol says to start CPR immediately.

-- CPR has been started (implied by user proceeding). Apply CPRStarted event.
-- From InitialAssessment, CPRStarted transitions to InitialACLS.
def afterCPRStarted := updateState state1 patient1 Event.CPRStarted

def state2 : ArrestState := afterCPRStarted.1
def patient2 : ArrestPatient := afterCPRStarted.2

#eval state2
-- Expected: ArrestState.InitialACLS

-- User reports monitor has been attached. Apply MonitorAttached event.
def afterMonitorAttached := updateState state2 patient2 Event.MonitorAttached

def state3 : ArrestState := afterMonitorAttached.1
def patient3 : ArrestPatient := afterMonitorAttached.2

#eval state3
-- Expected: ArrestState.InitialACLS (state unchanged by equipment attachment)

#eval patient3.monitorAttached
-- Expected: true

-- Get the next actions and reminders
#eval ACLSOutput state3 patient3
-- Expected output for InitialACLS state:
-- actions = [GiveOxygen, AttachMonitor, AttachDefibrillator, ObtainIVIO]
-- reminders = ["Perform CPR for 2 minutes", "Maintain compression rate 100-120/min",
--              "Allow full chest recoil by pushing down at least 5cm (2inch)",
--              "Give enough air for visible chest rise"]
-- Note: Monitor is already attached, but the protocol still lists it.
-- Still need: defibrillator and IV/IO access.

-- User reports defibrillator attached. Apply DefibrillatorAttached event.
def afterDefibAttached := updateState state3 patient3 Event.DefibrillatorAttached

def state4 : ArrestState := afterDefibAttached.1
def patient4 : ArrestPatient := afterDefibAttached.2

#eval state4
-- Expected: ArrestState.InitialACLS (state unchanged by equipment attachment)

#eval patient4.defibrillatorAttached
-- Expected: true

-- User reports IV/IO access established. Apply IV_IOEstablished event.
def afterIVIO := updateState state4 patient4 Event.IV_IOEstablished

def state5 : ArrestState := afterIVIO.1
def patient5 : ArrestPatient := afterIVIO.2

#eval state5
-- Expected: ArrestState.InitialACLS (state unchanged by equipment attachment)

#eval patient5.vascularAccess
-- Expected: VascularAccess.IV_IO

#eval patient5.monitorAttached
-- Expected: true

#eval patient5.defibrillatorAttached
-- Expected: true

-- Get the next actions and reminders with all equipment now attached
#eval ACLSOutput state5 patient5
-- Expected output for InitialACLS state:
-- actions = [GiveOxygen, AttachMonitor, AttachDefibrillator, ObtainIVIO]
-- reminders = ["Perform CPR for 2 minutes", "Maintain compression rate 100-120/min",
--              "Allow full chest recoil by pushing down at least 5cm (2inch)",
--              "Give enough air for visible chest rise"]
-- All equipment is now attached. The protocol output still lists them
-- but the key next step is to identify the rhythm on the monitor.
-- User reports pulseless VT on the monitor. Apply RhythmObserved event.
def afterRhythmObserved := updateState state5 patient5 (Event.RhythmObserved Rhythm.PulselessVT)

def state6 : ArrestState := afterRhythmObserved.1
def patient6 : ArrestPatient := afterRhythmObserved.2

#eval state6
-- Expected: ArrestState.RhythmAnalysis

#eval patient6.rhythm
-- Expected: some (Rhythm.PulselessVT)

#eval ACLSOutput state6 patient6
-- Expected: actions = [DeliverShock], reminders = ["Resume CPR immediately after shock"]

-- User reports shock has been delivered. Apply ShockDelivered event.
-- ShockDelivered transitions to CPR state and increments shockCount.
def afterShockDelivered := updateState state6 patient6 Event.ShockDelivered

def state7 : ArrestState := afterShockDelivered.1
def patient7 : ArrestPatient := afterShockDelivered.2

#eval state7
-- Expected: ArrestState.CPR

#eval patient7.shockCount
-- Expected: 1

-- User reports patient is moving and responding to pain after the shock.
-- This indicates signs of life / return of spontaneous circulation (ROSC).
-- We should check for a pulse. The patient responding to pain suggests pulse may be present.
-- Apply PulseDetected event since the patient is moving and responding.
def afterPulseDetected := updateState state7 patient7 Event.PulseDetected

def state8 : ArrestState := afterPulseDetected.1
def patient8 : ArrestPatient := afterPulseDetected.2

#eval state8
-- Expected: ArrestState.ROSC

#eval patient8.pulse
-- Expected: some Pulse.Present

-- Get the next actions and reminders for ROSC
#eval ACLSOutput state8 patient8
-- Expected output for ROSC:
-- actions = []
-- reminders = ["Begin post-cardiac arrest care"]
-- Patient has achieved ROSC. Begin post-cardiac arrest care.
