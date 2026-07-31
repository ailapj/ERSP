
/-
  Timed traces for Metric Temporal Logic (MTL)
-/

/-
Defining the state type by having the state + timestamp
-/
structure TimedEvent (σ : Type) where
  time  : Nat
  state : σ
deriving Repr


/--
A timed trace is simply a finite list of timestamped states.
The ordering of the list represents the temporal ordering.
-/
abbrev Trace (σ : Type) := List (TimedEvent σ)


namespace Trace

variable {σ : Type}


/--
Return the state stored at index `i`.
-/
def state
    (t : Trace σ)
    (i : Nat)
    (h : i < t.length) : σ :=
  (t.get ⟨i, h⟩).state


/--
Return the timestamp stored at index `i`.
-/
def time
    (t : Trace σ)
    (i : Nat)
    (h : i < t.length) : Nat :=
  (t.get ⟨i, h⟩).time


/--
Data type of valid intervals.
-/
structure Interval where
  lower : Nat
  upper : Option Nat
  valid : match upper with
        | some u => lower ≤ u
        | none => True
deriving Repr


/--
Checks whether a duration is contained in an interval.
-/
def Interval.contains (I : Interval) (d : Nat) : Prop :=
  I.lower ≤ d ∧
  match I.upper with
  | some u => d ≤ u
  | none => True


/--
Computes the elapsed time between two positions in a trace.
-/
def elapsed
    (t : Trace σ)
    (i j : Nat)
    (hi : i < t.length)
    (hj : j < t.length) : Nat :=
  t.time j hj - t.time i hi


/--
Describing the syntax of MTL formulas.
-/
inductive Formula (σ : Type) where
| atom : (σ → Prop) → Formula σ
| not : Formula σ → Formula σ
| and : Formula σ → Formula σ → Formula σ
| or : Formula σ → Formula σ → Formula σ
| implies : Formula σ → Formula σ → Formula σ
| next : Formula σ → Formula σ
| until : Formula σ → Formula σ → Formula σ
| eventually : Interval → Formula σ → Formula σ
| always : Interval → Formula σ → Formula σ
| untilWithin : Interval → Formula σ → Formula σ → Formula σ


/--
MTL semantics.
-/
def satisfies
    (t : Trace σ)
    (i : Nat)
    (h : i < t.length)
    : Formula σ → Prop

-- atomic proposition
| Formula.atom P =>
    P (t.state i h)

-- negation
| Formula.not φ =>
    ¬ satisfies t i h φ

-- conjunction
| Formula.and φ ψ =>
    satisfies t i h φ ∧ satisfies t i h ψ

-- disjunction
| Formula.or φ ψ =>
    satisfies t i h φ ∨ satisfies t i h ψ

-- implication
| Formula.implies φ ψ =>
    satisfies t i h φ → satisfies t i h ψ

-- next state
| Formula.next φ =>
    if hnext : i + 1 < t.length then
      satisfies t (i + 1) hnext φ
    else
      False

-- φ holds until ψ becomes true
| Formula.until φ ψ =>
    ∃ j,
      ∃ hj : j < t.length,
        i ≤ j ∧
        satisfies t j hj ψ ∧
        (∀ k,
          ∀ hk : k < t.length,
            i ≤ k →
            k < j →
            satisfies t k hk φ)

-- φ eventually holds within interval
| Formula.eventually I φ =>
    ∃ j,
      ∃ hj : j < t.length,
        i ≤ j ∧
        I.contains (t.elapsed i j h hj) ∧
        satisfies t j hj φ

-- φ always holds within interval
| Formula.always I φ =>
    ∀ j,
      ∀ hj : j < t.length,
        i ≤ j →
        I.contains (t.elapsed i j h hj) →
        satisfies t j hj φ

-- φ holds until ψ becomes true within interval
| Formula.untilWithin I φ ψ =>
    ∃ j,
      ∃ hj : j < t.length,
        i ≤ j ∧
        I.contains (t.elapsed i j h hj) ∧
        satisfies t j hj ψ ∧
        ∀ k,
          ∀ hk : k < t.length,
            i ≤ k →
            k < j →
            satisfies t k hk φ


end Trace


-- ===========================
-- below is another version of the above where teh trace is more complicated and some qualities/proofs in itself to make sure
-- the trace is valid, but it was making proofs more complicated so above example is used for now
-- ===========================

-- /-
--   Timed traces for Metric Temporal Logic (MTL)
-- -/

-- /-
-- Defining the state type by having the state + timestamp
-- -/
-- structure TimedState (σ : Type) where
--   time  : Nat
--   state : σ
-- deriving Repr

-- /--
-- A timed trace is a finite sequence of timestamped states.
-- -/
-- structure Trace (σ : Type) where
--   lookup : Nat → Option (TimedState σ)
--   length : Nat
--   defined :
--     ∀ i, i < length ↔ (lookup i).isSome
--   monotone :
--     ∀ i j
--       (hi : i < length)
--       (hj : j < length),
--       i < j →
--       ((lookup i).get ((defined i).mp hi)).time ≤
--       ((lookup j).get ((defined j).mp hj)).time


-- namespace Trace

-- variable {σ : Type}


-- /--
-- Return the state stored at index `i`.
-- -/
-- def state
--     (t : Trace σ)
--     (i : Nat)
--     (h : i < t.length) : σ :=
--   ((t.lookup i).get ((t.defined i).mp h)).state

-- /--
-- Return the timestamp stored at index `i`.
-- -/
-- def time
--     (t : Trace σ)
--     (i : Nat)
--     (h : i < t.length) : Nat :=
--   ((t.lookup i).get ((t.defined i).mp h)).time


-- /--
-- Data type of valid intervals
-- -/
-- structure Interval where
--   lower : Nat
--   upper : Option Nat
--   valid : match upper with
--         | some u => lower ≤ u
--         | none => True
-- deriving Repr

-- /--
-- Since all time intervals are valid, this checks to see if a given time is in a given interval
-- -/
-- def Interval.contains (I : Interval) (d : Nat) : Prop :=
--   I.lower ≤ d ∧
--   match I.upper with
--   | some u => d ≤ u
--   | none => True

-- /--
-- Computes the elapsed time between two positions in a trace.
-- -/
-- def elapsed
--     (t : Trace σ)
--     (i j : Nat)
--     (hi : i < t.length)
--     (hj : j < t.length) : Nat :=
--   t.time j hj - t.time i hi

-- /--
-- Describing the syntax of MTL formulas. Each constructor builds a formula.
-- -/
-- inductive Formula (σ : Type) where
-- | atom : (σ → Prop) → Formula σ -- predicate on states
-- | not : Formula σ → Formula σ -- logical negation
-- | and : Formula σ → Formula σ → Formula σ -- logical conjunction
-- | or : Formula σ → Formula σ → Formula σ
-- | implies : Formula σ → Formula σ → Formula σ
-- | next : Formula σ → Formula σ -- next: formula holds at the next state
-- | until : Formula σ → Formula σ → Formula σ --until: σ must continue to hold until b eventually becomes true
-- | eventually : Interval → Formula σ → Formula σ -- eventually: σ becomes true sometime within the given interval
-- | always : Interval → Formula σ → Formula σ --always: σ must hold throughout the entire interval
-- | untilWithin : Interval → Formula σ → Formula σ → Formula σ -- until within: σ must keep holding until b becomes true, and b must become true within the specified time interval

-- /--
-- This is the semantics step, going from formulas to prop.
-- Since Formula is inductive, this is defined by recursion on the formula
-- -/
-- def satisfies
--     (t : Trace σ)
--     (i : Nat)
--     (h : i < t.length)
--     : Formula σ → Prop
-- -- P holds
-- | Formula.atom P =>
--     P (t.state i h)

-- -- negation of φ holding
-- | Formula.not φ =>
--     ¬ satisfies t i h φ

-- -- both φ ψ hold
-- | Formula.and φ ψ =>
--     satisfies t i h φ ∧ satisfies t i h ψ

-- | Formula.or φ ψ =>
--     satisfies t i h φ ∨ satisfies t i h ψ

-- | Formula.implies φ ψ =>
--     satisfies t i h φ → satisfies t i h ψ

-- -- if there exists a next state, then φ holds there
-- | Formula.next φ =>
--     if hnext : i + 1 < t.length then
--       satisfies t (i + 1) hnext φ
--     else
--       False

-- -- φ is true until ψ is true
-- | Formula.until φ ψ =>
--     ∃ j,
--       ∃ hj : j < t.length,
--         i ≤ j ∧
--         satisfies t j hj ψ ∧
--         (∀ k,
--           ∀ hk : k < t.length,
--             i ≤ k →
--             k < j →
--             satisfies t k hk φ)

-- -- there exists some valid future index j such that i <= j that elapsed time from i to j is inside the interval I
-- -- and φ is satisfied at j
-- | Formula.eventually I φ =>
--     ∃ (j : Nat),
--       ∃ (hj : j < t.length),
--         i ≤ j ∧
--         I.contains (t.elapsed i j h hj) ∧
--         satisfies t j hj φ

-- -- for every valid future index j, if j is at or after i and the elapsed time from i to j is inside the interval,
-- -- then φ must hold at j
-- | Formula.always I φ =>
--     ∀ (j : Nat),
--       ∀ (hj : j < t.length),
--         i ≤ j →
--         I.contains (t.elapsed i j h hj) →
--         satisfies t j hj φ

-- -- combination of until and adding the interval from eventually
-- -- there exists a future index j s.t. j is a valid position in the trace, j is at or after current pos i,
-- -- the elapsed time from i to j is inside the interval I. ψ holds at j. φ holds at every position [i, j)
-- | Formula.untilWithin I φ ψ =>
--     ∃ (j : Nat),
--       ∃ (hj : j < t.length),
--         i ≤ j ∧
--         I.contains (t.elapsed i j h hj) ∧
--         satisfies t j hj ψ ∧
--         ∀ (k : Nat),
--           ∀ (hk : k < t.length),
--             i ≤ k →
--             k < j →
--             satisfies t k hk φ


-- end Trace
