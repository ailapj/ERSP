-- Vocabulary for the choking / swallowed-object domain. Every field records only
-- what the caller said or asked, never a clinical conclusion or an answer.
-- A rule must leave every unmentioned field unconstrained. In particular, do not
-- set an unmentioned field to `unknown` or `no`.

inductive Tri where
  | yes
  | no
  | unknown
  deriving DecidableEq

inductive AgeSaid where
  | baby        -- "my baby", "the infant", "nine week-old"
  | child       -- "my toddler", "my daughter", "the kid"
  | adult       -- "my husband", "my father", "my mom"
  | unspecified
  deriving DecidableEq

inductive QuestionAsked where
  | whatToDo          -- "what do I do?", "what should I do now?"
  | whetherFatal      -- "can the person die?"
  | whetherConcerned  -- "should I still be worried?"
  deriving DecidableEq

inductive ItemSaid where
  | food
  | coin
  | button
  | other
  deriving DecidableEq

inductive TimeSaid where
  | now
  | aboutOneDay
  | multipleDays
  deriving DecidableEq

structure Ctx where
  ageSaid           : AgeSaid
  -- This records the question itself, not its answer and not a recommended action.
  questionAsked     : QuestionAsked
  saidChoking       : Tri   -- the caller used the word "choking"
  eatingOrItemInMouth : Tri  -- was eating or had food in the mouth; not actual ingestion
  itemSaid           : ItemSaid
  itemStuckInThroat  : Tri   -- caller said food/an object is stuck in the throat
  attemptedSwallow   : Tri   -- tried to swallow; does not imply it was swallowed
  itemSwallowed      : Tri   -- actual ingestion; use this instead of inferring from eating
  pickedUpFromFloor  : Tri
  itemSeenInMouth    : Tri
  itemRecovered      : Tri   -- item was later found outside the person's body
  itemPassed         : Tri   -- item came out / passed through
  itemStillInside    : Tri   -- caller believes the item remains inside
  timeSaid           : TimeSaid
  actingNormal       : Tri   -- acting/feeling normal or recovered
  clutchingThroat   : Tri   -- grabbing at the throat or neck
  makingSound       : Tri   -- can talk, cry, or make any sound
  coughing          : Tri
  breathing         : Tri
  turnedBlue        : Tri
  responsive        : Tri   -- answers, reacts, has not passed out
  helpPresent       : Tri   -- someone other than the casualty is there to act
