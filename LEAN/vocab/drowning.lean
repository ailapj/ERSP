-- Vocabulary for the drowning domain, written in what a caller actually reports.
--
-- Every field is an observation. "Out of the water and not breathing means start
-- CPR" is a clinical inference and lives in the rule, not here.
--
-- `wasSubmerged` and `outOfWater` are kept apart on purpose. "He was underwater"
-- says nothing about whether anyone has got him out yet, and that gap is exactly
-- what several of the underspecified cases turn on.
--
-- `seemsRecovered` holds the caller's own reading of the situation -- "he woke
-- up", "he seems okay now". It is a report, not a clinical judgement, which is
-- why the rule has to be the thing that decides whether going home is safe.

inductive Tri where
  | yes
  | no
  | unknown
  deriving DecidableEq

inductive AgeSaid where
  | child       -- "my son", "my daughter", "the kid"
  | adult
  | unspecified
  deriving DecidableEq

structure Ctx where
  ageSaid        : AgeSaid
  wasSubmerged   : Tri   -- went under, fell in, was in the water
  outOfWater     : Tri   -- pulled out, rescued, got him out
  responsive     : Tri   -- awake, talking, answers
  breathing      : Tri
  coughing       : Tri
  inhaledWater   : Tri   -- swallowed or breathed in water
  seemsRecovered : Tri   -- woke up, seems okay now
