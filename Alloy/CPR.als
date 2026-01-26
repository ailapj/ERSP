// Time
sig Time {
  next: lone Time
}

// Persons
abstract sig Person {}
sig Responder extends Person {
  hasTraining: one Bool
}
sig Victim extends Person {}

// Equipment and resources
abstract sig Equipment {}
sig PPE extends Equipment {}  // Gloves, masks
sig AED extends Equipment {}
sig BarrierDevice extends Equipment {}  // Face shield/mask for rescue breaths

// Environmental conditions
abstract sig Environment {}
one sig Safe, Unsafe extends Environment {}

// Boolean values
abstract sig Bool {}
one sig True, False extends Bool {}

// Protocol steps
abstract sig ProtocolStep {}
one sig 
  SceneSafety,
  AssessVictim,
  ActivateEmergency,
  ProvideCPR,
  UseAED,
  MinimizeInterruptions,
  InfectionControl
extends ProtocolStep {}

// Scene assessment results
abstract sig VictimCondition {}
one sig Responsive, Unresponsive extends VictimCondition {}

abstract sig BreathingStatus {}
one sig NormalBreathing, NotBreathing, OnlyGasping extends BreathingStatus {}

// CPR types
abstract sig CPRType {}
one sig HandsOnly, FullCPR extends CPRType {}

// State of the rescue scenario at each time point
sig State {
  time: one Time,
  
  // Environment and safety
  environment: one Environment,
  ppeAvailable: one Bool,
  ppeUsed: one Bool,
  
  // Victim status
  victimCondition: one VictimCondition,
  victimBreathing: one BreathingStatus,
  
  // Actions taken
  sceneChecked: one Bool,
  victimAssessed: one Bool,
  emergencyCalled: one Bool,
  aedRequested: one Bool,
  cprStarted: one Bool,
  cprType: lone CPRType,
  aedApplied: one Bool,
  
  // CPR quality metrics (simplified)
  compressionRate: lone Int,  // 100-120 per minute
  compressionDepth: lone Int,  // at least 2 inches (simplified to integer)
  interruptionTime: one Int   // seconds, should be < 10
}

// Facts about time
fact TimeStructure {
  // Time is linear
  all t: Time | lone t.~next
  // No cycles in time
  no t: Time | t in t.^next
}

// Facts about states
fact StateTimeMapping {
  // Each time has exactly one state
  all t: Time | one s: State | s.time = t
  // Each state belongs to exactly one time
  all s: State | one s.time
}

// STEP 1: Scene Safety
pred checkSceneSafety[s: State] {
  s.sceneChecked = True
  s.environment = Safe implies {
    // Can proceed if scene is safe
    s.ppeAvailable = True implies s.ppeUsed = True
  }
}
// STEP 2: Assess the Victim
pred assessVictim[s: State] {
  // Can only assess if scene is checked and safe
  s.sceneChecked = True
  s.environment = Safe
  s.victimAssessed = True
}
// STEP 3: Activate Emergency Response
pred activateEmergency[s: State] {
  // Only activate if victim is unresponsive and not breathing normally
  s.victimCondition = Unresponsive
  s.victimBreathing in (NotBreathing + OnlyGasping)
  s.emergencyCalled = True
  s.aedRequested = True
}
// STEP 4: Provide High-Quality CPR
pred provideCPR[s: State, r: Responder] {
  // Prerequisites
  s.victimAssessed = True
  s.emergencyCalled = True
  s.victimCondition = Unresponsive
  s.victimBreathing in (NotBreathing + OnlyGasping)
  
  s.cprStarted = True
  
  // Choose CPR type based on training
  r.hasTraining = False implies s.cprType = HandsOnly
  r.hasTraining = True implies s.cprType in CPRType
  
  // Quality requirements
  s.compressionRate >= 100
  s.compressionRate <= 120
  s.compressionDepth >= 2  // inches (simplified)
}
// STEP 5: Use AED
pred useAED[s: State] {
  // Can use AED once requested and available
  s.aedRequested = True
  s.aedApplied = True
  // Continue CPR until AED is ready
  s.cprStarted = True
}
// STEP 6: Minimize Interruptions
pred minimizeInterruptions[s: State] {
  s.cprStarted = True
  s.interruptionTime < 10  // Less than 10 seconds
}

// Safety constraint: Never proceed if scene is unsafe
fact NeverProceedIfUnsafe {
  all s: State | 
    s.environment = Unsafe implies {
      s.victimAssessed = False
      s.cprStarted = False
    }
}

// Temporal progression constraints
fact ProtocolOrder {
  all s, snext: State | snext.time = s.time.next implies {
    // Once scene is checked, stays checked
    s.sceneChecked = True implies snext.sceneChecked = True
    // Once emergency is called, stays called
    s.emergencyCalled = True implies snext.emergencyCalled = True
    // CPR continues once started (until victim recovers or help arrives)
    s.cprStarted = True implies snext.cprStarted = True
    // Can't assess before checking scene safety
    snext.victimAssessed = True implies s.sceneChecked = True
    // Can't start CPR before assessing victim
    snext.cprStarted = True implies s.victimAssessed = True
    // Can't start CPR before calling emergency
    snext.cprStarted = True implies s.emergencyCalled = True
  }
}

// Define a valid rescue scenario
pred validRescueScenario[r: Responder] {
  // Must have at least these temporal steps
  some s1, s2, s3, s4: State | {
    // Temporal ordering
    s2.time = s1.time.next
    s3.time = s2.time.next
    s4.time = s3.time.next
    
    // Step 1: Check scene
    s1.sceneChecked = True
    s1.environment = Safe
    // Step 2: Assess victim
    s2.sceneChecked = True
    s2.victimAssessed = True
    s2.victimCondition = Unresponsive
    s2.victimBreathing = NotBreathing
    // Step 3: Activate emergency
    s3.emergencyCalled = True
    s3.aedRequested = True
    // Step 4: Provide CPR
    s4.cprStarted = True
    s4.compressionRate >= 100
    s4.compressionRate <= 120
    s4.compressionDepth >= 2
    s4.interruptionTime < 10

    // Choose CPR type based on training
    r.hasTraining = False implies s4.cprType = HandsOnly
  }
}

// Simpler scenario to test
pred simpleScenario {
  some s: State | {
    s.sceneChecked = True
    s.environment = Safe
  }
}

// Assertion: If CPR is started, scene must be safe and emergency called
assert CPRRequiresPrerequisites {
  all s: State | s.cprStarted = True implies {
    s.sceneChecked = True
    s.environment = Safe
    s.victimAssessed = True
    s.emergencyCalled = True
  }
}
// Assertion: Untrained responders only use hands-only CPR
assert UntrainedUseHandsOnly {
  all s: State, r: Responder | 
    (s.cprStarted = True and r.hasTraining = False) 
    implies s.cprType = HandsOnly
}

// Run commands to explore scenarios
run simpleScenario for 3
run validRescueScenario for 5 but 4 Time, 1 Responder, 1 Victim

// Check assertions
check CPRRequiresPrerequisites for 5 but 4 Time
check UntrainedUseHandsOnly for 5 but 4 Time

// Example: Find a scenario where AED is used
pred scenarioWithAED {
  some s: State | s.aedApplied = True
  some r: Responder | validRescueScenario[r]
}

run scenarioWithAED for 5 but 5 Time, 1 Responder, 1 Victim
