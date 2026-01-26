// Basic types representing person condition and age category
abstract sig Person {}
one sig Infant, Child, Adult extends Person {}

// Observations/signs that define choking severity
sig Sign {}
one sig CanCough, CanTalk, CannotBreathe, CannotSpeak extends Sign {}

// Rescue actions
abstract sig Action {}
one sig BackBlows, AbdominalThrusts, ChestThrusts, CPR, CallEmergency extends Action {}

// Choking state: whether obstruction is partial or complete
enum Obstruction { Partial, Complete }

// Context of a choking incident
sig Incident {
    person: Person,
    signs: set Sign,
    obstruction: Obstruction,
    actions: set Action
}

// Safety rule: If someone can cough or talk forcefully,
// do not apply first aid — let them clear airway.
fact letnAllowFirstAidIfCoughOrTalk =
    all inc: Incident |
        (CanCough in inc.signs or CanTalk in inc.signs) implies
            (BackBlows not in inc.actions and AbdominalThrusts not in inc.actions)

// If the obstruction is complete and the person cannot breathe or speak,
// first aid should be applied or emergency help should be called.
fact triageCompleteChoking {
    all inc: Incident |
        inc.obstruction = Complete and (CannotBreathe in inc.signs or CannotSpeak in inc.signs) implies
            (CallEmergency in inc.actions or BackBlows in inc.actions or AbdominalThrusts in inc.actions or ChestThrusts in inc.actions)
}

// Infants require modified sequence: back blows then chest thrusts
fact infantFirstAid {
    all inc: Incident |
        inc.person = Infant and inc.obstruction = Complete implies
            (BackBlows in inc.actions and ChestThrusts in inc.actions)
}

// Adults and older children: sequence of back blows and abdominal thrusts
fact adultChildFirstAid {
    all inc: Incident |
        (inc.person = Adult or inc.person = Child) and inc.obstruction = Complete implies
            (BackBlows in inc.actions and AbdominalThrusts in inc.actions)
}

// Unconscious leads to CPR
fact unconsciousCPR {
    all inc: Incident |
        inc.obstruction = Complete and cannot (CannotBreathe in inc.signs) and
        not (CanCough in inc.signs or CanTalk in inc.signs) implies
            CPR in inc.actions
}

// If alone and choking, emergency call and self-thrusts
pred selfHelp (inc: Incident) {
    inc.obstruction = Complete and
    (CannotBreathe in inc.signs or CannotSpeak in inc.signs) implies
        (CallEmergency in inc.actions and AbdominalThrusts in inc.actions)
}

// Example run specification
run triageCompleteChoking for 5
