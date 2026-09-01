import YOriginal
import YPrime

theorem rule_equiv : ∀ c, YOriginal.rule c ↔ YPrime.rule c := by
  intro c
  grind [YOriginal.rule, YPrime.rule]
