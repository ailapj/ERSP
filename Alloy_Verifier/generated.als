module generated
open reference

pred GeneratedPlan {

    -- whatever your planner produced
    P.done = ProtectHeadAndSpine
    P.symptoms = none
    P.states = CannotMoveSpine

    -- maybe next action chosen:
    some a: Action | NextActionToDo[a] and a = AskForSymptoms
}
