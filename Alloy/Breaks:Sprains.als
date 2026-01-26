// Action definitions

abstract sig Action {}

// Main flow actions
one sig AssessInjury_LAF extends Action {}      // Look, Ask, Feel
one sig CheckCSM extends Action {}
one sig TractionInLine extends Action {}       // optional if CSM compromised
one sig Splint extends Action {}
one sig OpenFractureCare extends Action {}     // only if fracture open
one sig ManagePain extends Action {}
one sig Evacuate extends Action {}             

// CSM sub-actions for checking during traction/splint
abstract sig CSM_Step extends Action {}
one sig CirculatoryCheck extends CSM_Step {}
one sig SensationCheck extends CSM_Step {}
one sig MotorCheck extends CSM_Step {}
one sig StrokeGripCheck extends CSM_Step {}

//  state model

sig State {
    action: one Action,
    nextState: lone State
}

// main flow

fact MainFlow {
    // Assess the injury
    all s: State |
        s.action = AssessInjury_LAF implies
            s.nextState.action = CheckCSM

    // Initial CSM check after assessment
    all s: State |
        s.action = CheckCSM implies
            s.nextState.action = TractionInLine

    // After TIL (optional), splint
    all s: State |
        s.action = TractionInLine implies
            s.nextState.action = Splint

    // Splint always followed by CSM recheck
    all s: State |
        s.action = Splint implies
            s.nextState.action = CheckCSM

    // Optional open fracture care after splint
    all s: State |
        s.action = Splint implies
            s.nextState.action = OpenFractureCare

    // Pain management follows splint or open fracture care
    all s: State |
        (s.action = Splint or s.action = OpenFractureCare) implies
            s.nextState.action = ManagePain

    // Evacuation is final
    all s: State |
        s.action = ManagePain implies
            s.nextState.action = Evacuate
}

// CSM

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

// Evacuation

fact EvacuationIsFinal {
    all s: State |
        s.action = Evacuate implies no s.nextState
}

fact NoCycles {
    no s: State | s in s.^nextState
}

// Execution

run {} for 20 State, 10 Action, 4 CSM_Step
