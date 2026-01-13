import RevHalt.Base.Trace
import RevHalt.Base.Kit

/-!
# RevHalt.Base.QuotientUp (Axiom-Free)

Goal: make the “quotient + closure” geometry explicit without `funext`/`propext`.

We do **not** use `up T = up T'` (function equality). Instead we use pointwise equivalence:
  UpEqv T T' :≡ ∀ n, up T n ↔ up T' n

Then we show:
1) UpEqv is an equivalence relation.
2) Under DetectsMonotone K, `Rev_K K` is invariant under UpEqv (so it descends to the quotient).
3) The “negative class” is exactly the UpEqv-class of ⊥ₜ, and it is the unique class where Rev_K is false.
-/

namespace RevHalt

/-- Pointwise equivalence of the *monotonized* traces. This is the axiom-free stand-in for `up T = up T'`. -/
def UpEqv (T T' : Trace) : Prop :=
  ∀ n : ℕ, up T n ↔ up T' n

/-- UpEqv is reflexive. -/
lemma UpEqv_refl (T : Trace) : UpEqv T T := by
  intro n; exact Iff.rfl

/-- UpEqv is symmetric. -/
lemma UpEqv_symm {T T' : Trace} : UpEqv T T' → UpEqv T' T := by
  intro h n; exact (h n).symm

/-- UpEqv is transitive. -/
lemma UpEqv_trans {T T' T'' : Trace} : UpEqv T T' → UpEqv T' T'' → UpEqv T T'' := by
  intro h1 h2 n
  exact (h1 n).trans (h2 n)

/-- Helper: UpEqv transports existential truth of `up`. -/
lemma exists_up_congr {T T' : Trace} (h : UpEqv T T') :
    (∃ n, up T n) ↔ (∃ n, up T' n) := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (h n).1 hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (h n).2 hn⟩

/-- Main descent lemma: Rev_K is invariant under UpEqv (hence well-defined on the quotient). -/
lemma revK_congr_of_UpEqv (K : RHKit) (hK : DetectsMonotone K)
    {T T' : Trace} (h : UpEqv T T') :
    Rev_K K T ↔ Rev_K K T' := by
  -- reduce both sides to existence on up, then transport existence via UpEqv
  have rT  : Rev_K K T  ↔ ∃ n, up T n  := revK_iff_exists_up (K := K) hK T
  have rT' : Rev_K K T' ↔ ∃ n, up T' n := revK_iff_exists_up (K := K) hK T'
  have hex : (∃ n, up T n) ↔ (∃ n, up T' n) := exists_up_congr (T := T) (T' := T') h
  exact rT.trans (hex.trans rT'.symm)

/-!
## The “negative class” and uniqueness of the anti-case

We formalize “anti-case” as: `¬ Rev_K K T`.

Then we show it coincides with “`up T` is pointwise bottom”, hence it is exactly the UpEqv-class of ⊥ₜ.
-/

/-- “up is bottom” in axiom-free form: pointwise equivalence to ⊥ₜ. -/
def UpIsBottom (T : Trace) : Prop :=
  ∀ n, up T n ↔ (⊥ₜ) n

/-- UpIsBottom is exactly “never”: ∀ n, ¬ T n. -/
lemma UpIsBottom_iff_forall_not (T : Trace) :
    UpIsBottom T ↔ ∀ n, ¬ T n := by
  -- this is exactly your lemma, just via the definitional abbreviation
  unfold UpIsBottom
  exact up_iff_bottom_iff_forall_not T

/-- Anti-case predicate for a given Kit: Rev_K is false. -/
def Anti (K : RHKit) (T : Trace) : Prop := ¬ Rev_K K T

/-- Under DetectsMonotone, Anti is equivalent to “never”: ∀ n, ¬T n. -/
lemma Anti_iff_forall_not (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    Anti K T ↔ ∀ n, ¬ T n := by
  -- reuse your existing lemma
  unfold Anti
  have h1 : ¬ Rev_K K T ↔ ∀ n, ¬ T n := not_revK_iff_forall_not K hK T
  exact h1

/-- Under DetectsMonotone, Anti is equivalent to UpIsBottom. -/
lemma Anti_iff_UpIsBottom (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    Anti K T ↔ UpIsBottom T := by
  have hA : Anti K T ↔ ∀ n, ¬ T n := Anti_iff_forall_not (K := K) hK T
  have hB : UpIsBottom T ↔ ∀ n, ¬ T n := UpIsBottom_iff_forall_not (T := T)
  exact hA.trans hB.symm

/-- The canonical negative representative is ⊥ₜ itself: its `up` is pointwise bottom. -/
lemma UpIsBottom_bottom : UpIsBottom (⊥ₜ) := by
  intro n
  constructor
  · intro hup
    -- up ⊥ₜ n gives a witness k with False, contradiction
    obtain ⟨k, hk, hkF⟩ := hup
    exact False.elim hkF
  · intro hbot
    -- bottom n is False, so this direction is trivial
    exact False.elim hbot

/-- If UpIsBottom T holds, then T is UpEqv-equivalent to ⊥ₜ (i.e., same `up` pointwise). -/
lemma UpEqv_to_bottom_of_UpIsBottom {T : Trace} (h : UpIsBottom T) :
    UpEqv T (⊥ₜ) := by
  intro n
  -- UpEqv T ⊥ₜ means up T n ↔ up ⊥ₜ n
  -- from h we have up T n ↔ ⊥ₜ n, and UpIsBottom_bottom gives up ⊥ₜ n ↔ ⊥ₜ n
  have hb : UpIsBottom (⊥ₜ) := UpIsBottom_bottom
  -- rewrite via ⊥ₜ n as the middle
  -- (up T n ↔ ⊥ₜ n) and (up ⊥ₜ n ↔ ⊥ₜ n) give (up T n ↔ up ⊥ₜ n)
  exact (h n).trans ((hb n).symm)

/-- Conversely, if T is UpEqv-equivalent to ⊥ₜ then UpIsBottom T holds. -/
lemma UpIsBottom_of_UpEqv_to_bottom {T : Trace} (h : UpEqv T (⊥ₜ)) :
    UpIsBottom T := by
  intro n
  have hb : UpIsBottom (⊥ₜ) := UpIsBottom_bottom
  -- up T n ↔ up ⊥ₜ n, and up ⊥ₜ n ↔ ⊥ₜ n, hence up T n ↔ ⊥ₜ n
  exact (h n).trans (hb n)

/-- “⊥ₜ is the unique anti-case (modulo UpEqv)”: Anti ↔ UpEqv-to-bottom, under DetectsMonotone. -/
lemma Anti_iff_UpEqv_bottom (K : RHKit) (hK : DetectsMonotone K) (T : Trace) :
    Anti K T ↔ UpEqv T (⊥ₜ) := by
  -- Anti ↔ UpIsBottom ↔ UpEqv-to-bottom
  have h1 : Anti K T ↔ UpIsBottom T := Anti_iff_UpIsBottom (K := K) hK T
  constructor
  · intro hA
    exact UpEqv_to_bottom_of_UpIsBottom (T := T) ((h1).1 hA)
  · intro hEq
    have hBot : UpIsBottom T := UpIsBottom_of_UpEqv_to_bottom (T := T) hEq
    exact (h1).2 hBot

/-- If two traces are both anti-cases, then they are UpEqv-equivalent (they collapse to the same bottom class). -/
lemma Anti_unique_class (K : RHKit) (hK : DetectsMonotone K) {T T' : Trace} :
    Anti K T → Anti K T' → UpEqv T T' := by
  intro hA hA'
  have hTb  : UpEqv T  (⊥ₜ) := (Anti_iff_UpEqv_bottom (K := K) hK T).1 hA
  have hT'b : UpEqv T' (⊥ₜ) := (Anti_iff_UpEqv_bottom (K := K) hK T').1 hA'
  -- T ~ ⊥ and T' ~ ⊥  ⇒  T ~ T'
  exact UpEqv_trans hTb (UpEqv_symm hT'b)

end RevHalt

-- Axiom checks:
#print axioms RevHalt.UpEqv
#print axioms RevHalt.revK_congr_of_UpEqv
#print axioms RevHalt.UpIsBottom
#print axioms RevHalt.Anti
#print axioms RevHalt.Anti_unique_class
