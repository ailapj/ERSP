-- Vocabulary for the drowning domain. Every field records only what the caller said
-- or asked, never a clinical conclusion or an answer. Leave every unmentioned field
-- unconstrained; do not set it to `unknown` or `no` by default.

inductive Tri where
  | yes
  | no
  | unknown
  deriving DecidableEq

inductive AgeSaid where
  | baby        -- "1-year-old baby", infant
  | child       -- "my son", "the kid", "my nephew"
  | adult
  | unspecified
  deriving DecidableEq

inductive QuestionAsked where
  | whatToDo                 -- what action/measures should be taken
  | whetherConcerned         -- "should I be worried/concerned?"
  | whySymptom               -- asks why coughing or another symptom occurs
  | aboutRecovery            -- asks about recovery after inhaling water
  | whatWasDone              -- asks what someone did after the event
  | whetherExpelWaterFirst   -- asks about expelling water before CPR
  deriving DecidableEq

inductive TimeSaid where
  | now         -- happening as the caller speaks
  | earlier     -- minutes or hours ago
  | dayOrMore   -- "it's 24 hours later"
  | unspecified
  deriving DecidableEq

structure Ctx where
  ageSaid        : AgeSaid
  timeSaid       : TimeSaid
  -- This records the question itself, not its answer or a recommended action.
  questionAsked  : QuestionAsked
  nearDrowningMentioned : Tri
  swimming       : Tri
  fellIntoWater  : Tri   -- fell/entered the water; does not imply going underwater
  wasSubmerged   : Tri   -- explicitly went under or was underwater
  missingFromView : Tri  -- person was in sight and then could no longer be seen
  outOfWater     : Tri   -- pulled out, rescued, got him out
  cannotSwim     : Tri
  responsive     : Tri   -- awake, talking, answers
  breathing      : Tri
  heartbeat      : Tri
  coughing       : Tri
  swallowedWater : Tri   -- swallowed water; does not imply inhalation into lungs
  swallowedWaterMoreThanOnce : Tri
  inhaledWater   : Tri   -- caller said water was breathed/inhaled into the lungs
  symptomsPresent : Tri  -- caller explicitly reports symptoms present or absent
  seemsRecovered : Tri   -- woke up, seems okay now
  lungsBelievedFullOfWater : Tri
  cprMentioned   : Tri
  rescueBreathsMentioned : Tri
  believesRescueBreathsIneffective : Tri
