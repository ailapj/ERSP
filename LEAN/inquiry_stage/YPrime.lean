import Vocab

namespace YPrime
def rule (c : Patient) : Prop :=
  c.ageInMonth = some 36 ∧
  c.breathing = some Breathing.slow ∧
  c.emotion = some Emotion.crying ∧
  c.temperature = some Temperature.highFever

example : Patient → Prop := rule
end YPrime
