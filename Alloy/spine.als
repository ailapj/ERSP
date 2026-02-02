-- ----------------- SYMPTOMS -----------------

abstract sig Symptom {}

one sig VertebralPain extends Symptom {}
one sig SensoryChange extends Symptom {}
one sig WeaknessOrParalysis extends Symptom {}

----------------- ACTION DEFS -----------------

abstract sig Action {}
-- Main flow actions
one sig ProtectHeadAndSpine extends Action {}
one sig CheckCSM_Initial extends Action {}
one sig BeamLiftOrLogRoll extends Action {}
one sig MaintainHeadStabilization extends Action {}
one sig CheckCSM_Recheck extends Action {}
one sig Evacuate extends Action {}

--not a spine injury 
one sig NotSpineInjury extends Action {}

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

-- ----------------- PATIENT STATUS -----------------
sig PatientStatus {
    done: set Action,
    symptoms: set Symptom
}

one sig P extends PatientStatus {}

pred HasSpinalRedFlag[p: PatientStatus] {
    some p.symptoms
}



-- ----------------- NEXT ACTION PREDICATE -----------------


pred NextActionToDo[a: Action] {
    -- CASE 1: Spine injury suspected → normal dependency logic
    ( HasSpinalRedFlag[P] -- checking context 
      and a not in P.done
      and a != NotSpineInjury
      and some d: Dependency | d.state = a
      and all d: Dependency |
            d.state = a implies d.requires in P.done
    )

    or

    -- CASE 2: No spine injury → single fallback action
    ( not HasSpinalRedFlag[P]
      and a = NotSpineInjury
    )
}

-- Next actions set
one sig NextSteps {
    actions: set Action
}


-- Example scenario:
-- Patient has head/spine protected and motor check passed (change/add to this 
-- to see how NextActionToDo changes.
-- remove P.symptoms and the evaluator says it is notSpineInjury

fact PatientScenario {
    P.done = ProtectHeadAndSpine + StrokeGripCheck + BeamLiftOrLogRoll
    P.symptoms = VertebralPain + SensoryChange
}

-- ----------------- QUERY -----------------

-- Find all next required actions based on dependencies
run { some a: Action | NextActionToDo[a] } for 
    10 Action, 10 Dependency, 1 PatientStatus
