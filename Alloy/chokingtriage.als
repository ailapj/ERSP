// Basic types representing person condition and age category

abstract sig Person {}
one sig Infant, NonInfant extends Person {}

abstract sig Airway {}
one sig Partial, Complete extends Airway {}

abstract sig Consciousness {}
one sig Conscious, Unconscious extends Consciousness {}

abstract sig Ability {}
one sig CanCoughOrTalk, CannotCoughOrTalk extends Ability {}

abstract sig Action {}
one sig
    EncourageCoughing,
    BackBlows,
    AbdominalThrusts,
    ChestThrusts,
    CPR,
    CallEmergency
extends Action


sig Incident {
    person: Person,
    airway: Airway,
    consciousness: Consciousness,
    ability: Ability,
    actions: set Action
}

fact ChokingControlFlow {

    all i: Incident | {

        /*************************************************
         * CASE 1: PARTIAL AIRWAY OBSTRUCTION
         * Premise:
         *   - Person can cough or talk
         * Decision:
         *   - Do not intervene
         * Outcome:
         *   - Encourage coughing only
         *************************************************/
        (i.airway = Partial and i.ability = CanCoughOrTalk) implies
            i.actions = EncourageCoughing


        /*************************************************
         * CASE 2: COMPLETE OBSTRUCTION + CONSCIOUS INFANT
         * Premise:
         *   - Airway completely blocked
         *   - Infant (<1 year)
         *   - Conscious
         * Decision:
         *   - Back blows + chest thrusts
         * Outcome:
         *   - No abdominal thrusts
         *************************************************/
        (i.airway = Complete and
         i.consciousness = Conscious and
         i.person = Infant) implies
            (BackBlows in i.actions and
             ChestThrusts in i.actions and
             AbdominalThrusts not in i.actions)


        /*************************************************
         * CASE 3: COMPLETE OBSTRUCTION + CONSCIOUS NON-INFANT
         * Premise:
         *   - Airway completely blocked
         *   - Child or adult
         *   - Conscious
         * Decision:
         *   - Back blows + abdominal thrusts
         *************************************************/
        (i.airway = Complete and
         i.consciousness = Conscious and
         i.person = NonInfant) implies
            (BackBlows in i.actions and
             AbdominalThrusts in i.actions)


        /*************************************************
         * CASE 4: UNCONSCIOUS PERSON
         * Premise:
         *   - Person becomes unconscious
         * Decision:
         *   - Begin CPR
         *************************************************/
        (i.consciousness = Unconscious) implies
            CPR in i.actions


        /*************************************************
         * CASE 5: COMPLETE OBSTRUCTION → CALL EMERGENCY
         * Premise:
         *   - Severe choking
         * Decision:
         *   - Emergency services must be contacted
         *************************************************/
        (i.airway = Complete) implies
            CallEmergency in i.actions
    }
}
