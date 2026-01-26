// Swimming Safety, Drowning Prevention, and Emergency Response Model
// Based on CDC Official Guidelines and AHA 2024 Drowning CPR Guidelines

// ============================================
// PART 1: PREVENTION - Original Model
// ============================================

// Core entities
abstract sig Person {}
sig Child extends Person {}
sig Adult extends Person {}

abstract sig WaterLocation {}
sig Pool extends WaterLocation {}
sig NaturalWater extends WaterLocation {}
sig Bathtub extends WaterLocation {}

// Safety measures
sig Supervision {
  supervisor: one Adult,
  supervised: set Child,
  location: one WaterLocation,
  isConstant: one Bool,
  isWithinArmsReach: one Bool,
  avoidingDistractions: one Bool
}

sig SwimmingLesson {
  participant: one Person,
  completed: one Bool
}

sig PoolBarrier {
  pool: one Pool,
  hasFourSidedFence: one Bool,
  fenceHeight_4ft: one Bool,
  hasSelfClosingGate: one Bool,
  hasSelfLatchingGate: one Bool,
  separatesFromHouse: one Bool
}

sig LifeJacket {
  wearer: one Person,
  coastGuardApproved: one Bool,
  properlyFitted: one Bool,
  location: one WaterLocation
}

sig CPRTraining {
  trained: one Adult,
  current: one Bool
}

abstract sig Bool {}
one sig True, False extends Bool {}

// ============================================
// PART 2: EMERGENCY RESPONSE 
// ============================================

// Drowning Incident and Victim Status
sig DrowningIncident {
  victim: one Person,
  location: one WaterLocation,
  victimStatus: one VictimStatus,
  response: lone EmergencyResponse  // May or may not have response
}

abstract sig VictimStatus {}
one sig Conscious, Unconscious, CardiacArrest extends VictimStatus {}

// Emergency Response Chain
sig EmergencyResponse {
  incident: one DrowningIncident,
  sceneAssessment: one SceneAssessment,
  rescue: one RescueAction,
  resuscitation: lone Resuscitation,  // Only if needed
  ems911Called: one Bool,
  aedAvailable: one Bool
}

// Scene Safety Assessment
sig SceneAssessment {
  sceneSafe: one Bool,              // Is it safe to approach?
  hazardsIdentified: one Bool,      // Strong currents, deep water, etc.
  rescuerCompetent: one Bool        // Can rescuer safely perform rescue?
}

// Rescue from Water
sig RescueAction {
  victimRemovedFromWater: one Bool,
  placedOnFirmSurface: one Bool,
  placedOnBack: one Bool,
  spinalPrecautions: one Bool       // Assume spinal injury in shallow water/diving
}

// Resuscitation Protocol (Based on AHA 2024 Guidelines)
sig Resuscitation {
  responsiveness: one ResponsivenessCheck,
  breathing: one BreathingCheck,
  cprPerformed: lone CPRProtocol,   // Only if not breathing
  aedUsed: one Bool
}

sig ResponsivenessCheck {
  victimResponsive: one Bool,
  shoutedForResponse: one Bool,
  tappedShoulder: one Bool
}

sig BreathingCheck {
  victimBreathing: one Bool,
  chestRising: one Bool,
  airwayOpen: one Bool
}

// CPR Protocol - CRITICAL: Drowning CPR differs from cardiac arrest CPR
sig CPRProtocol {
  protocol: one CPRType,
  rescueBreathsFirst: one Bool,     // KEY: Start with breaths for drowning!
  initialBreaths: one Int,          // Should be 2 or 5 breaths
  compressionDepth_inches: one Int, // 2 for adult/child, 1.5 for infant
  compressionRate: one Int,         // 100-120 per minute
  compressionBreathRatio: one CompressionBreathRatio,
  continueUntilEMS: one Bool
}

abstract sig CPRType {}
one sig DrowningCPR, CardiacCPR, HandsOnlyCPR extends CPRType {}

abstract sig CompressionBreathRatio {}
one sig Ratio_30_2, Ratio_15_2 extends CompressionBreathRatio {}  // 30:2 for adults, 15:2 for children with 2 rescuers

// ============================================
// PART 3: PREVENTION RULES 
// ============================================

fact ConstantSupervisionForYoungChildren {
  all s: Supervision | 
    (some c: s.supervised | c in Child) implies
      s.isConstant = True and s.isWithinArmsReach = True
}

fact SupervisorsAvoidDistractions {
  all s: Supervision |
    s.avoidingDistractions = True
}

fact PoolsMustHaveProperBarriers {
  all p: Pool | some b: PoolBarrier |
    b.pool = p and
    b.hasFourSidedFence = True and
    b.fenceHeight_4ft = True and
    b.hasSelfClosingGate = True and
    b.hasSelfLatchingGate = True and
    b.separatesFromHouse = True
}

fact ChildrenWearLifeJacketsInNaturalWater {
  all c: Child, w: NaturalWater |
    (some s: Supervision | c in s.supervised and s.location = w) implies
      (some lj: LifeJacket |
        lj.wearer = c and
        lj.location = w and
        lj.coastGuardApproved = True and
        lj.properlyFitted = True)
}

fact LifeJacketsForBoating {
  all p: Person, w: NaturalWater |
    (some lj: LifeJacket |
      lj.wearer = p and
      lj.location = w implies
      lj.coastGuardApproved = True)
}

fact SwimmingLessonsWithSupervision {
  all c: Child |
    (some sl: SwimmingLesson | sl.participant = c and sl.completed = True) implies
      (some s: Supervision | c in s.supervised)
}

fact SupervisorsShouldKnowCPR {
  all s: Supervision |
    some cpr: CPRTraining |
      cpr.trained = s.supervisor and cpr.current = True
}

fact RealisticSupervision {
  all s: Supervision | some s.supervised
  all c: Child, w: WaterLocation |
    (some s: Supervision | c in s.supervised and s.location = w)
}

fact NoUnsupervisedChildren {
  all c: Child | some s: Supervision | c in s.supervised
}

// ============================================
// PART 4: EMERGENCY RESPONSE RULES 
// ============================================

// Rule 1: Scene safety must be assessed before rescue
fact SceneSafetyFirst {
  all er: EmergencyResponse |
    er.sceneAssessment.sceneSafe = True and
    er.sceneAssessment.hazardsIdentified = True and
    er.sceneAssessment.rescuerCompetent = True
}

// Rule 2: All drowning incidents must call 911
fact Call911ForDrowning {
  all er: EmergencyResponse |
    er.ems911Called = True
}

// Rule 3: Victim must be removed from water and placed properly
fact ProperVictimPositioning {
  all er: EmergencyResponse |
    er.rescue.victimRemovedFromWater = True and
    er.rescue.placedOnFirmSurface = True and
    er.rescue.placedOnBack = True
}

// Rule 4: Assume spinal injury in shallow water/diving incidents
fact SpinalPrecautionsInShallowWater {
  all er: EmergencyResponse |
    er.incident.location in Pool implies
      er.rescue.spinalPrecautions = True
}

// Rule 5: Check responsiveness properly
fact ProperResponsivenessCheck {
  all r: Resuscitation |
    r.responsiveness.shoutedForResponse = True and
    r.responsiveness.tappedShoulder = True
}

// Rule 6: CRITICAL - Drowning CPR must start with rescue breaths
fact DrowningCPRStartsWithBreaths {
  all cpr: CPRProtocol |
    cpr.protocol = DrowningCPR implies (
      cpr.rescueBreathsFirst = True and
      (cpr.initialBreaths = 2 or cpr.initialBreaths = 5)
    )
}

// Rule 7: Use correct compression-breath ratio
fact CorrectCompressionBreathRatio {
  all cpr: CPRProtocol |
    cpr.protocol = DrowningCPR implies
      (cpr.compressionBreathRatio = Ratio_30_2 or 
       cpr.compressionBreathRatio = Ratio_15_2)
}

// Rule 8: Never use hands-only CPR for drowning
fact NeverHandsOnlyForDrowning {
  all cpr: CPRProtocol |
    cpr.protocol = DrowningCPR implies cpr.protocol != HandsOnlyCPR
}

// Rule 9: Correct compression depth
fact CorrectCompressionDepth {
  all cpr: CPRProtocol |
    cpr.protocol = DrowningCPR implies
      (cpr.compressionDepth_inches = 2 or cpr.compressionDepth_inches = 1)
}

// Rule 10: Correct compression rate (100-120/min)
fact CorrectCompressionRate {
  all cpr: CPRProtocol |
    cpr.compressionRate >= 100 and cpr.compressionRate <= 120
}

// Rule 11: Continue CPR until EMS arrives
fact ContinueCPRUntilEMS {
  all cpr: CPRProtocol |
    cpr.continueUntilEMS = True
}

// Rule 12: If victim not breathing, must perform resuscitation
fact ResuscitationIfNotBreathing {
  all er: EmergencyResponse |
    all r: Resuscitation | r in er.resuscitation implies
      (r.breathing.victimBreathing = False implies
        some cpr: CPRProtocol | cpr in r.cprPerformed)
}

// Rule 13: Emergency response exists for all incidents
fact AllIncidentsHaveResponse {
  all di: DrowningIncident |
    some er: EmergencyResponse | er.incident = di
}

// ============================================
// PART 5: PREDICATES 
// ============================================

// Safe scenario (prevention)
pred SafeScenario {
  all s: Supervision | 
    s.isConstant = True and 
    s.avoidingDistractions = True
  
  all b: PoolBarrier |
    b.hasFourSidedFence = True and
    b.hasSelfClosingGate = True and
    b.hasSelfLatchingGate = True
  
  all c: Child, s: Supervision |
    s.location in NaturalWater and c in s.supervised implies
      (some lj: LifeJacket | lj.wearer = c and lj.coastGuardApproved = True)
}

// Proper emergency response
pred ProperEmergencyResponse {
  all er: EmergencyResponse |
    // Scene safety
    er.sceneAssessment.sceneSafe = True and
    // 911 called
    er.ems911Called = True and
    // Victim properly positioned
    er.rescue.victimRemovedFromWater = True and
    er.rescue.placedOnFirmSurface = True and
    // If resuscitation needed, done correctly
    (all r: Resuscitation | r in er.resuscitation implies
      (some cpr: CPRProtocol | 
        cpr in r.cprPerformed and
        cpr.protocol = DrowningCPR and
        cpr.rescueBreathsFirst = True))
}

// Improper response (for learning)
pred ImproperEmergencyResponse {
  some er: EmergencyResponse |
    er.sceneAssessment.sceneSafe = False or
    er.ems911Called = False or
    (some r: Resuscitation | r in er.resuscitation and
      (some cpr: CPRProtocol |
        cpr in r.cprPerformed and
        cpr.rescueBreathsFirst = False))
}

// Complete drowning chain of survival
pred DrowningChainOfSurvival {
  // Prevention measures in place
  all s: Supervision | s.isConstant = True
  
  // If incident occurs, proper response
  all er: EmergencyResponse |
    er.sceneAssessment.sceneSafe = True and
    er.ems911Called = True and
    er.rescue.victimRemovedFromWater = True and
    (some r: er.resuscitation |
      some cpr: r.cprPerformed |
        cpr.protocol = DrowningCPR and
        cpr.rescueBreathsFirst = True)
}

// ============================================
// PART 6: ASSERTIONS
// ============================================

assert SupervisionAlwaysRequired {
  all c: Child | some s: Supervision | c in s.supervised
}

assert PoolsHaveBarriers {
  all p: Pool | some b: PoolBarrier | b.pool = p
}

assert AllIncidentsGet911Call {
  all er: EmergencyResponse | er.ems911Called = True
}

assert DrowningCPRNeverHandsOnly {
  all cpr: CPRProtocol |
    cpr.protocol = DrowningCPR implies cpr.protocol != HandsOnlyCPR
}

assert RescueBreathsAlwaysFirst {
  all cpr: CPRProtocol |
    cpr.protocol = DrowningCPR implies cpr.rescueBreathsFirst = True
}

// ============================================
// PART 7: RUN COMMANDS
// ============================================

// Prevention scenarios
run SafeScenario for 5

// Emergency response scenarios
run ProperEmergencyResponse for 5 but 3 Int
run ImproperEmergencyResponse for 5 but 3 Int
run DrowningChainOfSurvival for 5 but 3 Int

// Verification
check SupervisionAlwaysRequired for 5
check PoolsHaveBarriers for 5
check AllIncidentsGet911Call for 5 but 3 Int
check DrowningCPRNeverHandsOnly for 5 but 3 Int
check RescueBreathsAlwaysFirst for 5 but 3 Int
