"""Build the Lean theorem that compares the two imported rule modules."""

from __future__ import annotations

#checking equivalence
def theorem_source() -> str:
    return """import YOriginal
import YPrime

theorem rule_equiv : ∀ c, YOriginal.rule c ↔ YPrime.rule c := by
  intro c
  grind [YOriginal.rule, YPrime.rule]
"""
