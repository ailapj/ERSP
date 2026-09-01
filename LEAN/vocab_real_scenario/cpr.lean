-- Vocabulary for the CPR domain. Every field records only what the caller said or
-- asked, never a clinical conclusion or an answer. Leave every unmentioned field
-- unconstrained; do not set it to `unknown`, `no`, or `none` by default.

inductive Tri where
  | yes
  | no
  | unknown
  deriving DecidableEq

inductive PrecedingEvent where
  | choking
  | drowning
  | none
  | unknown
  deriving DecidableEq

structure Ctx where
  -- Question fields record the caller's question, not the correct response.
  asksWhetherCPR                  : Tri
  asksWhetherToKeepCheckingPulse : Tri
  asksWhatRespondersDo           : Tri
  asksWhetherBreathingWithoutPulse : Tri
  asksWhyCPR                     : Tri
  asksForHelp                    : Tri
  nursingHome                    : Tri
  adultSaid                      : Tri
  fell                           : Tri
  foundDown       : Tri   -- collapsed, fainted, passed out, found on the floor
  responsive      : Tri   -- answers, reacts, wakes up
  breathing       : Tri   -- the caller said the person is breathing
  troubleBreathing : Tri
  breathingNormal : Tri   -- the caller called that breathing normal, regular, quiet
  gasping         : Tri   -- caller explicitly reports snoring, gurgling, or gasping
  breathingPauses : Tri   -- breathing happens intermittently and then stops/pauses
  pausesGettingLonger : Tri
  fluidSound       : Tri   -- fluid/gurgling sound reported while breathing
  turnedBlue      : Tri
  pulseFelt       : Tri
  pulseFaint      : Tri
  warmSkin        : Tri
  aedNearby       : Tri
  priorAngioplasty : Tri
  cardiacArrestMentioned : Tri
  emtMentioned    : Tri
  precededBy      : PrecedingEvent
