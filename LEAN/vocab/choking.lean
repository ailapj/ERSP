-- Vocabulary for the choking domain, written in what a caller actually reports.
--
-- Every field is something a person can observe and say: whether the casualty is
-- making a sound, whether they are coughing, whether they went blue. Nothing here
-- is a clinical conclusion. "Not crying means no air is moving" and "no air moving
-- means a complete obstruction" are inferences, and inferences belong in the rule,
-- where the roundtrip check can verify them -- not inside the formalization step,
-- where nothing checks them.
--
-- Age is recorded as the word the caller used. Whether "toddler" follows the
-- infant protocol or the child protocol is a clinical decision, so the rule makes
-- it, not this file.
--
-- Every field carries `unknown`: a caller states less than the full situation, and
-- the formalization has to be able to say so instead of guessing.

inductive Tri where
  | yes
  | no
  | unknown
  deriving DecidableEq

inductive AgeSaid where
  | baby        -- "my baby", "the infant"
  | child       -- "my toddler", "my daughter", "the kid"
  | adult       -- "my husband", "my father", "my dad"
  | unspecified
  deriving DecidableEq

structure Ctx where
  ageSaid           : AgeSaid
  saidChoking       : Tri   -- the caller used the word "choking"
  swallowedOrEating : Tri   -- swallowed something, had food in the mouth, was eating
  clutchingThroat   : Tri   -- grabbing at the throat or neck
  makingSound       : Tri   -- can talk, cry, or make any sound
  coughing          : Tri
  breathing         : Tri
  turnedBlue        : Tri
  responsive        : Tri   -- answers, reacts, has not passed out
