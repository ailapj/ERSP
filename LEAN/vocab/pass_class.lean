-- Vocabulary for the "passing a class" requirement. Hand-written; every stage
-- of the pipeline is held to it.

structure Ctx where
  passes         : Bool
  cheated        : Bool
  finalExamScore : Int
  attendancePct  : Int
