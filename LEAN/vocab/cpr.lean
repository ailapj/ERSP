-- Vocabulary for the CPR domain, written in what a caller actually reports.
--
-- Every field is an observation. "Collapsed and not breathing means cardiac
-- arrest" is a clinical inference and lives in the rule, not here.
--
-- `pulseFelt` is recorded because callers report it ("my husband has no pulse"),
-- not because the protocol uses it -- lay rescuer protocols deliberately do not
-- check a pulse. What the rule does with the field is the rule's business; this
-- file only has to be able to hold what was said.
--
-- `warmSkin` exists for the same reason: one caller asks whether CPR is needed
-- "if he's warm", and that observation has to be representable to be answered.
--
-- No age field. Every CPR case in the test set reports an adult, and none of the
-- expected outcomes turns on age.

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
  foundDown  : Tri   -- collapsed, fainted, passed out, found on the floor
  responsive : Tri   -- answers, reacts, wakes up
  breathing  : Tri   -- breathing, and breathing normally
  pulseFelt  : Tri
  warmSkin   : Tri
  aedNearby  : Tri
  precededBy : PrecedingEvent
