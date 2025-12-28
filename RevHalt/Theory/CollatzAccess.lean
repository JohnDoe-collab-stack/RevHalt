/-
  CollatzAccess.lean  (self-contained)

  What this formalizes, cleanly and without any RevHalt dependencies:

  - A primitive recursive Collatz iterator on ℕ.
  - The local Σ₁ predicate  ReachOne(n) := ∃t, iter(t,n)=1.
  - Its Π₁ complement AvoidOne(n) := ∀t, iter(t,n)≠1, with the constructive equivalence
      ¬ReachOne(n) ↔ AvoidOne(n).
  - The global Collatz statement is Π₂:
      Collatz := ∀n, ∃t, iter(t,n)=1.
  - Its negation is Σ₂ (classically):
      ¬Collatz ↔ ∃n, ∀t, iter(t,n)≠1.
  - A “local fork by certificates”: you can move left with a Σ₁ witness,
    or move right with a Π₁ stabilization certificate; both certificates cannot coexist.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Parity

namespace CollatzAccess

/-- One Collatz step on ℕ. -/
def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iteration of Collatz, definitional and PR. -/
def iter : ℕ → ℕ → ℕ
| 0,     n => n
| t + 1, n => iter t (step n)

/-- Decidable atomic matrix: R(n,t) := iter(t,n)=1. -/
def R (n t : ℕ) : Prop := iter t n = 1

instance (n t : ℕ) : Decidable (R n t) := by
  unfold R
  infer_instance

/-- Local “reaches 1”: Σ₁ shape. -/
def ReachOne (n : ℕ) : Prop := ∃ t : ℕ, R n t

/-- Local “never reaches 1”: Π₁ shape. -/
def AvoidOne (n : ℕ) : Prop := ∀ t : ℕ, ¬ R n t

/-- Constructive complementarity: ¬(∃t R) ↔ ∀t ¬R. -/
theorem not_reachOne_iff_avoidOne (n : ℕ) :
    ¬ ReachOne n ↔ AvoidOne n := by
  unfold ReachOne AvoidOne
  constructor
  · intro h t ht
    exact h ⟨t, ht⟩
  · intro h hex
    rcases hex with ⟨t, ht⟩
    exact h t ht

/-- Σ₁ witness type: a concrete time t with iter(t,n)=1. -/
def ReachCert (n : ℕ) : Type := { t : ℕ // R n t }

/-- Π₁ certificate type: a stabilization proof ∀t, iter(t,n)≠1. -/
def AvoidCert (n : ℕ) : Prop := ∀ t : ℕ, ¬ R n t

theorem reachOne_iff_nonempty_cert (n : ℕ) :
    ReachOne n ↔ Nonempty (ReachCert n) := by
  unfold ReachOne ReachCert
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨⟨t, ht⟩⟩
  · rintro ⟨⟨t, ht⟩⟩
    exact ⟨t, ht⟩

/-- Exclusion: you cannot have both a Σ₁ witness and a Π₁ stabilization certificate. -/
theorem cert_exclusion (n : ℕ) :
    ¬ (Nonempty (ReachCert n) ∧ AvoidCert n) := by
  intro h
  rcases h with ⟨⟨⟨t, ht⟩⟩, hAvoid⟩
  exact hAvoid t ht

/-- Global Collatz statement: Π₂ shape. -/
def Collatz : Prop := ∀ n : ℕ, ReachOne n

/-- Classical prenex move: ¬(∀n ∃t R) ↔ ∃n ∀t ¬R. -/
theorem not_Collatz_iff_exists_avoidOne :
    ¬ Collatz ↔ ∃ n : ℕ, AvoidOne n := by
  classical
  unfold Collatz
  constructor
  · intro h
    -- derive ∃n, ¬ReachOne n (classical)
    have : ∃ n : ℕ, ¬ ReachOne n := by
      by_contra h'
      have hall : ∀ n : ℕ, ReachOne n := by
        intro n
        by_contra hn
        exact h' ⟨n, hn⟩
      exact h hall
    rcases this with ⟨n, hn⟩
    exact ⟨n, (not_reachOne_iff_avoidOne n).1 hn⟩
  · rintro ⟨n, hAvoid⟩ hAll
    have hReach : ReachOne n := hAll n
    have : ¬ ReachOne n := (not_reachOne_iff_avoidOne n).2 hAvoid
    exact this hReach

/-
  Summary you can reuse inside RevHalt-style statements:

  - ReachOne(n) is Σ₁ with matrix R(n,t).
  - AvoidOne(n) is Π₁ (and constructively equivalent to ¬ReachOne(n)).
  - Collatz is Π₂: ∀n ∃t R(n,t).
  - ¬Collatz is Σ₂ (classically): ∃n ∀t ¬R(n,t).
  - The “missing Π₁” is exactly the AvoidCert(n) object:
      a stabilization certificate ∀t, iter(t,n)≠1.
-/

end CollatzAccess
