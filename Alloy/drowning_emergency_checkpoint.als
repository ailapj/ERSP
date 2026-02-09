module ResuscitationProtocols
//THIS FILE IS FOR CPR AND BREATHING SITUATION(SAFETY PROTOCAL) AND VERIFICATION OF BAD LLM-GENERTED CASE
// ---------------------------------------------------------
// 1. DEFINITION 
// ---------------------------------------------------------

enum Status { Present, Absent }
enum Action { DoFullCPR, DoRescueBreathingOnly, DoNothing }

sig Victim {
    actualPulse: one Status,  // actual pulse status
    breathing: one Status     // breathing status
} 

sig Rescuer {
    target: one Victim,
    perceivedPulse: one Status, // rescuer percieve their might have pulse
    action: one Action          // taking action: CPR or breathing only
}

// ---------------------------------------------------------
// 2. GROUND FACT
// ---------------------------------------------------------

fact RealityCheck {
    // no breathing
    all v: Victim | v.breathing = Absent
}

// ---------------------------------------------------------
// 3. Predicates
// ---------------------------------------------------------

// Bad Protocol) ---
// depending on Rescuer, if they think victims have pulse, then breathing only or CPR+breathing
pred followBadProtocol[r: Rescuer] {
    // rescuer think there is pulse: doing breathing
    r.perceivedPulse = Present implies r.action = DoRescueBreathingOnly
    
    // rescuer think there is not pulse, doing cpr
    r.perceivedPulse = Absent implies r.action = DoFullCPR
}

// Godd protocal:
// No matter there is pulse, just do cpr
pred followGoodProtocol[r: Rescuer] {
    r.target.breathing = Absent implies r.action = DoFullCPR
}

// ---------------------------------------------------------
// 4. Safety Condition
// ---------------------------------------------------------

// fore rescuer r, if victims having cardiac arrest, must do cpr to be safe
pred VictimIsSafe[r: Rescuer] {
    (r.target.actualPulse = Absent) implies (r.action = DoFullCPR)
}

// ---------------------------------------------------------
// 5. Verification
// ---------------------------------------------------------

assert CheckBadProtocol {
    all r: Rescuer | followBadProtocol[r] implies VictimIsSafe[r]
}
check CheckBadProtocol for 3

assert CheckGoodProtocol {
    all r: Rescuer | followGoodProtocol[r] implies VictimIsSafe[r]
}
check CheckGoodProtocol for 3
