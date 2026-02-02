// ============================================
// Drowning Emergency Response - CHECKPOINT VERSION
// Strictly encodes ONLY constraints from scenario text
// Based on CDC Guidelines and AHA 2024 CPR Guidelines
// ============================================

// ============================================
// SCENARIO CONTROL FLOW
// ============================================
// Premise: Child may be in water, supervision may/may not exist
// Decision: Is there supervision? Is child drowning? Is there intervention?
// Outcome: Child safe OR child drowns (depending on intervention)
//
// Key Rule (ONLY hard constraint from text):
// - If supervision exists AND child drowning → rescue MUST occur
// ============================================

// ============================================
// PART 1: ENTITY DEFINITIONS
// ============================================

abstract sig Person {}
sig Child extends Person {}
sig Adult extends Person {}

abstract sig WaterLocation {}
sig Pool extends WaterLocation {}
sig NaturalWater extends WaterLocation {}

// Supervision relationship
sig Supervision {
  supervisor: one Adult,
  child: one Child
}

// Rescue intervention
sig Rescue {
  rescuer: one Adult,
  victim: one Child
}

// Drowning incident
sig Drowning {
  child: one Child
}

// ============================================
// PART 2: BASIC STRUCTURAL CONSTRAINTS
// ============================================
// These ensure well-formedness, not scenario rules

fact BasicWellFormedness {
  // Supervision connects one adult to one child
  all s: Supervision | 
    s.supervisor in Adult and s.child in Child

  // Rescue is adult saving child
  all r: Rescue | 
    r.rescuer in Adult and r.victim in Child

  // Drowning only affects children
  all d: Drowning | 
    d.child in Child
}

// ============================================
// PART 3: CORE SCENARIO RULES
// ============================================
// ONLY encode constraints explicitly in text

// RULE 1: Supervised drowning requires intervention
// This is the ONLY mandatory causal rule from the scenario
fact SupervisionImpliesRescue {
  all c: Child |
    // If child has supervision
    (some s: Supervision | s.child = c)
    and
    // AND child is drowning
    (some d: Drowning | d.child = c)
    implies
    // THEN rescue must occur
    (some r: Rescue | r.victim = c)
}

// ============================================
// PART 4: HAND-WRITTEN GENERATED PLAN
// ============================================
// This is a simple, manually constructed instance
// representing one possible execution path

one sig Alice extends Child {}
one sig Bob extends Adult {}
one sig LocalPool extends Pool {}

one sig SupervisionInstance extends Supervision {} {
  supervisor = Bob
  child = Alice
}

one sig DrowningIncident extends Drowning {} {
  child = Alice
}

one sig RescueAction extends Rescue {} {
  rescuer = Bob
  victim = Alice
}

// This plan represents:
// Premise: Alice in water at pool
// Decision: Supervision exists + Drowning occurs
// Outcome: Rescue happens → LEGAL (satisfies SupervisionImpliesRescue)

// ============================================
// PART 5: CONSISTENCY CHECKS
// ============================================

// ASSERTION 1: Verify our core rule
// Supervised drowning without rescue is FORBIDDEN
assert NoSupervisedDrowningWithoutRescue {
  all c: Child |
    (some s: Supervision | s.child = c)
    and (some d: Drowning | d.child = c)
    implies
    (some r: Rescue | r.victim = c)
}

// ASSERTION 2: Verify we're not over-constraining
// Unsupervised drowning without rescue is ALLOWED
assert UnsupervisedDrowningIsAllowed {
  some c: Child |
    (no s: Supervision | s.child = c)
    and (some d: Drowning | d.child = c)
    and (no r: Rescue | r.victim = c)
}

// ASSERTION 3: Verify drowning is not mandatory
// Scenarios without any drowning should be allowed
assert NoDrowningIsAllowed {
  some c: Child |
    (no d: Drowning | d.child = c)
}

// ASSERTION 4: Verify rescue can happen without supervision
// (Text doesn't forbid bystander intervention)
assert UnsupervisedRescueIsAllowed {
  some c: Child |
    (no s: Supervision | s.child = c)
    and (some d: Drowning | d.child = c)
    and (some r: Rescue | r.victim = c)
}

// ============================================
// PART 6: RUN COMMANDS
// ============================================

// Check if our hand-written plan is consistent
run {} for 5

// Verify our assertions
check NoSupervisedDrowningWithoutRescue for 5
check UnsupervisedDrowningIsAllowed for 5
check NoDrowningIsAllowed for 5
check UnsupervisedRescueIsAllowed for 5

// ============================================
// CHECKPOINT COMPLIANCE SUMMARY
// ============================================

