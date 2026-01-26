//action defs 

abstract sig Action {}

// Main flow actions
one sig ProtectHeadAndSpine extends Action {}
one sig CheckCSM_Initial extends Action {}
one sig BeamLiftOrLogRoll extends Action {}
one sig MaintainHeadStabilization extends Action {}
one sig CheckCSM_Recheck extends Action {}
one sig Evacuate extends Action {}

// CSM sub-actions
abstract sig CSM_Step extends Action {}

one sig CirculatoryCheck extends CSM_Step {}
one sig SensationCheck extends CSM_Step {}
one sig MotorCheck extends CSM_Step {}
one sig StrokeGripCheck extends CSM_Step {}


sig State {
    action: one Action,
    nextState: lone State
}

fact MainFlow {
    all s: State |
        s.action = ProtectHeadAndSpine implies
            s.nextState.action = CheckCSM_Initial

    all s: State |
        s.action = CheckCSM_Initial implies
            s.nextState.action = CirculatoryCheck

    all s: State |
        s.action = StrokeGripCheck and
        some start: State |
            start.action = CheckCSM_Initial and
            s in start.^nextState
        implies
            s.nextState.action = BeamLiftOrLogRoll

    all s: State |
        s.action = BeamLiftOrLogRoll implies
            s.nextState.action = MaintainHeadStabilization

    all s: State |
        s.action = MaintainHeadStabilization implies
            s.nextState.action = CheckCSM_Recheck

    all s: State |
        s.action = CheckCSM_Recheck implies
            s.nextState.action = CirculatoryCheck

    all s: State |
        s.action = StrokeGripCheck and
        some start: State |
            start.action = CheckCSM_Recheck and
            s in start.^nextState
        implies
            s.nextState.action = Evacuate
}


// CSM orders

fact CSMFlow {
    all s: State |
        s.action = CirculatoryCheck implies
            s.nextState.action = SensationCheck

    all s: State |
        s.action = SensationCheck implies
            s.nextState.action = MotorCheck

    all s: State |
        s.action = MotorCheck implies
            s.nextState.action = StrokeGripCheck

}
// evacuation step

fact EvacuationIsFinal {
    all s: State |
        s.action = Evacuate implies no s.nextState
}

fact NoCycles {
    no s: State | s in s.^nextState
}

// execution

run {} for 15 State
