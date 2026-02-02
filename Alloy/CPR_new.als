// Time
sig Time {
  next: lone Time
}

// Persons
abstract sig Person {}
sig Responder extends Person {}
sig Victim extends Person {}

// Equipment and resources
abstract sig Equipment {}
sig PPE extends Equipment {}
sig AED extends Equipment {}
sig BarrierDevice extends Equipment {}

// Environmental conditions
abstract sig Environment {}
one sig Safe, Unsafe extends Environment {}

// Boolean values
abstract sig Bool {}
one sig True, False extends Bool {}

// Assessment results
abstract sig VictimCondition {}
one sig Responsive, Unresponsive extends VictimCondition {}

abstract sig BreathingStatus {}
one sig NormalBreathing, NotBreathing, AbnormalBreathing extends BreathingStatus {}

abstract sig BleedingStatus {}
one sig NoBleeding, MinorBleeding, SevereBleeding extends BleedingStatus {}

// Surface types
abstract sig Surface {}
one sig FirmFlat, NotFirmFlat extends Surface {}

// Body position
abstract sig BodyPosition {}
one sig FaceUp, NotFaceUp extends BodyPosition {}

// Airway status
abstract sig AirwayStatus {}
one sig Open, Closed, PartiallyOpen extends AirwayStatus {}

// Chest rise
abstract sig ChestRise {}
one sig Rising, NotRising extends ChestRise {}

// State of the rescue scenario
sig State {
  time: one Time,
  
  // Environment and safety
  environment: one Environment,
  ppeAvailable: one Bool,
  ppeUsed: one Bool,
  
  // Victim assessment
  victimCondition: one VictimCondition,
  victimBreathing: one BreathingStatus,
  victimBleeding: one BleedingStatus,
  
  // Victim positioning
  surface: lone Surface,
  bodyPosition: lone BodyPosition,
  responderKneeling: one Bool,
  
  // Actions taken
  sceneChecked: one Bool,
  victimAssessed: one Bool,
  emergencyCalled: one Bool,
  aedRequested: one Bool,
  victimPositioned: one Bool,
  
  // CPR actions
  compressionsStarted: one Bool,
  compressionCount: lone Int,
  rescueBreathsGiven: one Bool,
  breathCount: lone Int,
  
  // CPR quality metrics
  handPosition: one Bool,
  shouldersOverHands: one Bool,
  elbowsStraight: one Bool,
  compressionRate: lone Int,
  compressionDepth: lone Int,
  chestRecoil: one Bool,
  
  // Airway and breathing
  airwayStatus: lone AirwayStatus,
  headTilted: one Bool,
  chinLifted: one Bool,
  nosePinched: one Bool,
  mouthSealed: one Bool,
  breathDuration: lone Int,
  chestRise: lone ChestRise,
  
  // AED
  aedApplied: one Bool,
  
  // Timing
  interruptionTime: one Int,
  cycleCount: lone Int
}

// Facts about time
fact TimeStructure {
  all t: Time | lone t.~next
  no t: Time | t in t.^next
}

fact StateTimeMapping {
  all t: Time | one s: State | s.time = t
  all s: State | one s.time
}

// Initialize integer fields to avoid inconsistencies
fact IntegerDefaults {
  all s: State | {
    s.compressionsStarted = False implies no s.compressionCount
    s.rescueBreathsGiven = False implies no s.breathCount
    s.compressionsStarted = False implies {
      no s.compressionRate
      no s.compressionDepth
    }
    s.rescueBreathsGiven = False implies no s.breathDuration
    s.victimPositioned = False implies {
      no s.surface
      no s.bodyPosition
    }
    s.rescueBreathsGiven = False implies no s.airwayStatus
    s.rescueBreathsGiven = False implies no s.chestRise
  }
}

// Safety constraint
fact NeverProceedIfUnsafe {
  all s: State | 
    s.environment = Unsafe implies {
      s.victimAssessed = False
      s.compressionsStarted = False
      s.victimPositioned = False
      s.rescueBreathsGiven = False
    }
}

// Temporal progression - simplified
fact ProtocolOrder {
  all s, snext: State | snext.time = s.time.next implies {
    // Persistence
    s.sceneChecked = True implies snext.sceneChecked = True
    s.victimAssessed = True implies snext.victimAssessed = True
    s.emergencyCalled = True implies snext.emergencyCalled = True
    snext.rescueBreathsGiven = True implies s.compressionsStarted = True
    
    // Prerequisites
    snext.victimAssessed = True implies s.sceneChecked = True
    snext.emergencyCalled = True implies s.victimAssessed = True
    snext.victimPositioned = True implies s.emergencyCalled = True
    snext.compressionsStarted = True implies s.victimPositioned = True
  }
}

// Simplified valid rescue scenario
pred validRescueScenario {
  // At least 6 time steps
  some disj s1, s2, s3, s4, s5, s6: State | {
    s2.time = s1.time.next
    s3.time = s2.time.next
    s4.time = s3.time.next
    s5.time = s4.time.next
    s6.time = s5.time.next
    
    // Step 1: Check scene
    s1.sceneChecked = True
    s1.environment = Safe
    s1.victimAssessed = False
    s1.emergencyCalled = False
    s1.victimPositioned = False
    s1.compressionsStarted = False
    s1.rescueBreathsGiven = False
    
    // Step 2: Assess victim
    s2.sceneChecked = True
    s2.victimAssessed = True
    s2.victimCondition = Unresponsive
    s2.victimBreathing = NotBreathing
    s2.victimBleeding = NoBleeding
    s2.emergencyCalled = False
    s2.victimPositioned = False
    s2.compressionsStarted = False
    
    // Step 3: Call emergency
    s3.sceneChecked = True
    s3.victimAssessed = True
    s3.emergencyCalled = True
    s3.aedRequested = True
    s3.victimPositioned = False
    s3.compressionsStarted = False
    
    // Step 4: Position victim
    s4.sceneChecked = True
    s4.victimAssessed = True
    s4.emergencyCalled = True
    s4.victimPositioned = True
    s4.responderKneeling = True
    s4.surface = FirmFlat
    s4.bodyPosition = FaceUp
    s4.compressionsStarted = False
    
    // Step 5: Start compressions
    s5.sceneChecked = True
    s5.victimAssessed = True
    s5.emergencyCalled = True
    s5.victimPositioned = True
    s5.compressionsStarted = True
    s5.handPosition = True
    s5.shouldersOverHands = True
    s5.elbowsStraight = True
    s5.compressionRate = 110
    s5.compressionDepth = 2
    s5.chestRecoil = True
    s5.compressionCount = 30
    s5.rescueBreathsGiven = False
    
    // Step 6: Give rescue breaths
    s6.sceneChecked = True
    s6.victimAssessed = True
    s6.emergencyCalled = True
    s6.victimPositioned = True
    s6.compressionsStarted = True
    s6.compressionCount = 30
    s6.rescueBreathsGiven = True
    s6.headTilted = True
    s6.chinLifted = True
    s6.nosePinched = True
    s6.mouthSealed = True
    s6.airwayStatus = Open
    s6.breathCount = 2
    s6.breathDuration = 1
    s6.chestRise = Rising
  }
}

// Simpler scenario to test basic structure
pred simpleScenario {
  some s: State | {
    s.sceneChecked = True
    s.environment = Safe
  }
}

// Assertions
assert CPRRequiresPrerequisites {
  all s: State | s.compressionsStarted = True implies {
    s.sceneChecked = True
    s.environment = Safe
    s.victimAssessed = True
    s.emergencyCalled = True
    s.victimPositioned = True
  }
}

assert BreathsRequireCompressions {
  all s: State | s.rescueBreathsGiven = True implies {
    s.compressionsStarted = True
  }
}

// Run commands
run simpleScenario for 3
run validRescueScenario for 6 but 6 Time, 1 Responder, 1 Victim

// Check assertions
check CPRRequiresPrerequisites for 6 but 6 Time
check BreathsRequireCompressions for 6 but 6 Time
