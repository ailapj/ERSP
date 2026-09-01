-- Vocabulary for the speed-limit requirement. Exercises the enum path: the
-- equivalence proof case-splits `zone` the same way it splits a `Bool`.

inductive Zone where
  | school
  | residential
  | highway
  deriving DecidableEq

structure Ctx where
  speedKph    : Int
  zone        : Zone
  hasPermit   : Bool
  isViolation : Bool
