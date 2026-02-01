// ----------------- ACTION DEFS -----------------

abstract sig Action {}

-- Main flow actions
one sig ProtectHeadAndSpine extends Action {}
one sig CheckCSM_Initial extends Action {}
one sig BeamLiftOrLogRoll extends Action {}
one sig MaintainHeadStabilization extends Action {}
one sig CheckCSM_Recheck extends Action {}
one sig Evacuate extends Action {}

-- CSM sub-actions
abstract sig CSM_Step extends Action {}
one sig CirculatoryCheck extends CSM_Step {}
one sig SensationCheck extends CSM_Step {}
one sig MotorCheck extends CSM_Step {}
one sig StrokeGripCheck extends CSM_Step {}

-- ----------------- DEPENDENCIES -----------------

sig Dependency {
    state: one Action,
    requires: set Action
}

fact Dependencies {
    some d: Dependency | d.state = CheckCSM_Initial and d.requires = ProtectHeadAndSpine
    some d: Dependency | d.state = CirculatoryCheck and d.requires = CheckCSM_Initial
    some d: Dependency | d.state = SensationCheck and d.requires = CirculatoryCheck
    some d: Dependency | d.state = MotorCheck and d.requires = SensationCheck
    some d: Dependency | d.state = StrokeGripCheck and d.requires = MotorCheck
    some d: Dependency | d.state = BeamLiftOrLogRoll and d.requires = StrokeGripCheck + CirculatoryCheck + SensationCheck
    some d: Dependency | d.state = MaintainHeadStabilization and d.requires = BeamLiftOrLogRoll
    some d: Dependency | d.state = CheckCSM_Recheck and d.requires = MaintainHeadStabilization
    some d: Dependency | d.state = Evacuate and d.requires = StrokeGripCheck + CheckCSM_Recheck
}

-- ----------------- PATIENT PARTIAL STATUS -----------------

sig PatientStatus {
    done: set Action
}

one sig P extends PatientStatus {}

-- Example scenario:
-- Patient has head/spine protected and motor check passed (change/add to this 
-- to see how NextActionToDo changes.
fact PatientScenario {
    P.done = ProtectHeadAndSpine  + StrokeGripCheck + BeamLiftOrLogRoll
}

-- ----------------- NEXT ACTION PREDICATE -----------------

//pred NextActionToDo[a: Action] {
//    a not in P.done
//    and all d: Dependency | d.state = a implies d.requires in P.a
//}

pred NextActionToDo[a: Action] {
    a not in P.done
    and some d: Dependency | d.state = a
    and all d: Dependency |
        d.state = a implies d.requires in P.done
}

-- Next actions set
one sig NextSteps {
    actions: set Action
}

-- ----------------- QUERY -----------------

-- Find all next required actions based on dependencies
run { some a: Action | NextActionToDo[a] } for 
    10 Action, 10 Dependency, 1 PatientStatus
