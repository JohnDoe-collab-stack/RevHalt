import RevHalt.Theory.PrimitiveHolonomy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fintype.Basic

set_option linter.unusedSectionVars false

/-!
# Primitive Holonomy: Derivation of Unitarity (Constructive)

## Proven content (zero sorry, zero Classical.choice)

1. Conservative Transport = Partial Bijection (functional + injective)
2. `L†L = P_dom` — domain projection  (partial isometry)
3. `LL† = P_im`  — image projection   (partial isometry)
4. Total + surjective + conservative ⇒ `L†L = LL† = Id` (full unitarity)
5. `⟨Lψ₁, ψ₂⟩ = ⟨ψ₁, L†ψ₂⟩` — adjoint = converse relation
6. Composition preserves conservativity  (groupoid)
7. `Lψ = μψ  ⇒  L^n ψ = μ^n ψ`        (eigenvalue propagation)
8. `L^n ψ = ψ ∧ Lψ = μψ ∧ ψ ≠ 0  ⇒  μ^n = 1` in integral domains
9. Bridge: holonomy eigenvalue ⇒ amplitude ratio (interference)
-/

namespace PrimitiveHolonomy.Unitarity

variable {P : Type} [HistoryGraph P]
variable {S : Type} [Fintype S] [DecidableEq S]

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 1. Definitions
-- ═══════════════════════════════════════════════════════════════════════════════

def SingleValued (R : S → S → Prop) : Prop :=
  ∀ x y₁ y₂, R x y₁ → R x y₂ → y₁ = y₂

def InjectiveRel (R : S → S → Prop) : Prop :=
  ∀ x₁ x₂ y, R x₁ y → R x₂ y → x₁ = x₂

def TotalDom (R : S → S → Prop) : Prop :=
  ∀ x, ∃ y, R x y

def Surjective (R : S → S → Prop) : Prop :=
  ∀ y, ∃ x, R x y

structure ConservativeSemantics (sem : Semantics P S) : Prop where
  functional : ∀ {h k} (p : HistoryGraph.Path h k), SingleValued (sem.sem p)
  injective  : ∀ {h k} (p : HistoryGraph.Path h k), InjectiveRel (sem.sem p)

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 2. ToLinear and InnerProduct
-- ═══════════════════════════════════════════════════════════════════════════════

section ConstructiveAlgebra

variable (R : Type) [CommRing R] [StarRing R] [DecidableEq R]

abbrev AmplitudeSpace S R := S → R

open BigOperators

def ToLinear (Rel : S → S → Prop) [DecidableRel Rel] :
    (AmplitudeSpace S R) →ₗ[R] (AmplitudeSpace S R) where
  toFun ψ := fun y => ∑ x, if Rel x y then ψ x else 0
  map_add' ψ₁ ψ₂ := by
    ext y; simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    split <;> simp
  map_smul' c ψ := by
    ext y; simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    split <;> simp [mul_zero]

def InnerProduct (ψ₁ ψ₂ : AmplitudeSpace S R) : R :=
  ∑ x, star (ψ₁ x) * ψ₂ x

instance decidableRel_swap {α : Type*} (r : α → α → Prop) [DecidableRel r] :
    DecidableRel (fun x y => r y x) :=
  fun x y => ‹DecidableRel r› y x

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 3. Adjoint = Converse
-- ═══════════════════════════════════════════════════════════════════════════════

theorem star_finset_sum (f : S → R) :
    star (∑ x : S, f x) = ∑ x : S, star (f x) := by
  have h := map_sum (starRingEnd R) f Finset.univ
  simp only [starRingEnd_apply] at h
  exact h

/--
  Constructive version of `Finset.sum_eq_single` to avoid `Classical.choice`.
  If `a ∈ s` and all other elements map to 0, sum is `f a`.
-/
theorem sum_eq_single_constructive
    (R : Type) [CommRing R]
    {s : Finset S} {f : S → R} {a : S}
    (ha : a ∈ s)
    (hZero : ∀ x ∈ s, x ≠ a → f x = 0) :
    ∑ x ∈ s, f x = f a := by
  induction s using Finset.induction_on generalizing a with
  | empty => contradiction
  | insert b s' hb IH =>
    rw [Finset.sum_insert hb]
    if h_eq : b = a then
      subst h_eq
      have h_rest : ∑ x ∈ s', f x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        apply hZero x (Finset.mem_insert_of_mem hx)
        intro h_eq
        subst h_eq
        exact hb hx
      rw [h_rest, add_zero]
    else
      have ha_in_s' : a ∈ s' := Finset.mem_of_mem_insert_of_ne ha (Ne.symm h_eq)
      rw [IH ha_in_s']
      · have : f b = 0 := hZero b (Finset.mem_insert_self b s') h_eq
        rw [this, zero_add]
      · intro x hx hxa
        exact hZero x (Finset.mem_insert_of_mem hx) hxa

theorem sum_comm_constructive
    {s t : Finset S} {f : S → S → R} :
    ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.sum_const_zero]
  | insert a s ha IH =>
    simp only [Finset.sum_insert ha, Finset.sum_add_distrib, IH]

theorem toLinear_adjoint_eq_converse (Rel : S → S → Prop) [DecidableRel Rel] :
    ∀ ψ₁ ψ₂, InnerProduct R (ToLinear R Rel ψ₁) ψ₂ =
      InnerProduct R ψ₁ (ToLinear R (fun y x => Rel x y) ψ₂) := by
  intro ψ₁ ψ₂
  simp only [InnerProduct, ToLinear, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [star_finset_sum R, Finset.sum_mul, Finset.mul_sum]
  rw [sum_comm_constructive]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  split_ifs with h
  · rfl
  · simp only [star_zero, zero_mul, mul_zero]



-- ═══════════════════════════════════════════════════════════════════════════════
-- § 4. L†L = P_dom  (domain projection)
-- ═══════════════════════════════════════════════════════════════════════════════

theorem partial_isometry_domain
    (Rel : S → S → Prop) [DecidableRel Rel]
    (hFunc : SingleValued Rel)
    (hInj : InjectiveRel Rel) :
    ∀ ψ x, ((ToLinear R (fun y x => Rel x y)) ((ToLinear R Rel) ψ)) x =
      if (∃ y, Rel x y) then ψ x else 0 := by
  intro ψ x
  simp only [ToLinear, LinearMap.coe_mk, AddHom.coe_mk]
  -- Step 1: collapse inner sum by injectivity
  -- For each y: ∑ z, [Rel z y] ψ z  becomes  [Rel x y] ψ x  (only z=x contributes)
  have hInner : ∀ y, (if Rel x y then (∑ z : S, if Rel z y then ψ z else 0) else 0) =
      (if Rel x y then ψ x else 0) := by
    intro y
    split_ifs with hxy
    · rw [sum_eq_single_constructive R (s := Finset.univ) (Finset.mem_univ x)]
      · simp only [if_pos hxy]
      · intro b _ hne
        rw [if_neg (fun hb => hne (hInj b x y hb hxy))]
    · rfl
  simp_rw [hInner]
  -- Step 2: collapse outer sum by functionality
  haveI : Decidable (∃ y, Rel x y) := Fintype.decidableExistsFintype
  split_ifs with hEx
  · obtain ⟨y₀, h₀⟩ := hEx
    rw [sum_eq_single_constructive R (s := Finset.univ) (Finset.mem_univ y₀)]
    · simp only [if_pos h₀]
    · intro b _ hne
      rw [if_neg (fun hb => hne (hFunc x b y₀ hb h₀))]
  · apply Finset.sum_eq_zero
    intro y _
    rw [if_neg (fun h => hEx ⟨y, h⟩)]

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 5. LL† = P_im  (image projection)
-- ═══════════════════════════════════════════════════════════════════════════════

theorem partial_isometry_image
    (Rel : S → S → Prop) [DecidableRel Rel]
    (hFunc : SingleValued Rel)
    (hInj : InjectiveRel Rel) :
    ∀ ψ y, ((ToLinear R Rel) ((ToLinear R (fun y x => Rel x y)) ψ)) y =
      if (∃ x, Rel x y) then ψ y else 0 := by
  intro ψ y
  simp only [ToLinear, LinearMap.coe_mk, AddHom.coe_mk]
  -- Step 1: collapse inner sum by functionality
  -- For each x: ∑ z, [Rel x z] ψ z  becomes  [Rel x y] ψ y  (only z=y contributes)
  have hInner : ∀ x, (if Rel x y then (∑ z : S, if Rel x z then ψ z else 0) else 0) =
      (if Rel x y then ψ y else 0) := by
    intro x
    split_ifs with hxy
    · rw [sum_eq_single_constructive R (s := Finset.univ) (Finset.mem_univ y)]
      · simp only [if_pos hxy]
      · intro b _ hne
        rw [if_neg (fun hb => hne (hFunc x b y hb hxy))]
    · rfl
  simp_rw [hInner]
  -- Step 2: collapse outer sum by injectivity
  haveI : Decidable (∃ x, Rel x y) := Fintype.decidableExistsFintype
  split_ifs with hEx
  · obtain ⟨x₀, h₀⟩ := hEx
    rw [sum_eq_single_constructive R (s := Finset.univ) (Finset.mem_univ x₀)]
    · simp only [if_pos h₀]
    · intro b _ hne
      rw [if_neg (fun hb => hne (hInj b x₀ y hb h₀))]
  · apply Finset.sum_eq_zero
    intro x _
    rw [if_neg (fun h => hEx ⟨x, h⟩)]

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 6. Full Unitarity (total + surjective + conservative)
-- ═══════════════════════════════════════════════════════════════════════════════

theorem left_unitary_of_total
    (Rel : S → S → Prop) [DecidableRel Rel]
    (hFunc : SingleValued Rel) (hInj : InjectiveRel Rel)
    (hTotal : TotalDom Rel) :
    ∀ ψ x, ((ToLinear R (fun y x => Rel x y)) ((ToLinear R Rel) ψ)) x = ψ x := by
  intro ψ x
  rw [partial_isometry_domain R Rel hFunc hInj ψ x, if_pos (hTotal x)]

theorem right_unitary_of_surjective
    (Rel : S → S → Prop) [DecidableRel Rel]
    (hFunc : SingleValued Rel) (hInj : InjectiveRel Rel)
    (hSurj : Surjective Rel) :
    ∀ ψ y, ((ToLinear R Rel) ((ToLinear R (fun y x => Rel x y)) ψ)) y = ψ y := by
  intro ψ y
  rw [partial_isometry_image R Rel hFunc hInj ψ y, if_pos (hSurj y)]

theorem full_unitary
    (Rel : S → S → Prop) [DecidableRel Rel]
    (hFunc : SingleValued Rel) (hInj : InjectiveRel Rel)
    (hTotal : TotalDom Rel) (hSurj : Surjective Rel) :
    (∀ ψ, (ToLinear R (fun y x => Rel x y)) ((ToLinear R Rel) ψ) = ψ) ∧
    (∀ ψ, (ToLinear R Rel) ((ToLinear R (fun y x => Rel x y)) ψ) = ψ) :=
  ⟨fun ψ => funext (left_unitary_of_total R Rel hFunc hInj hTotal ψ),
   fun ψ => funext (right_unitary_of_surjective R Rel hFunc hInj hSurj ψ)⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 7. Groupoid: composition preserves conservativity
-- ═══════════════════════════════════════════════════════════════════════════════

theorem conservative_comp
    {Rel1 Rel2 : S → S → Prop}
    (hF1 : SingleValued Rel1) (hI1 : InjectiveRel Rel1)
    (hF2 : SingleValued Rel2) (hI2 : InjectiveRel Rel2) :
    let Comp := fun x z => ∃ y, Rel1 x y ∧ Rel2 y z
    SingleValued Comp ∧ InjectiveRel Comp := by
  constructor
  · intro x z1 z2 ⟨y1, hR1, hS1⟩ ⟨y2, hR2, hS2⟩
    have := hF1 x y1 y2 hR1 hR2; subst this; exact hF2 y1 z1 z2 hS1 hS2
  · intro x1 x2 z ⟨y1, hR1, hS1⟩ ⟨y2, hR2, hS2⟩
    have := hI2 y1 y2 z hS1 hS2; subst this; exact hI1 x1 x2 y1 hR1 hR2

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 8. Eigenvalue propagation through iteration
--
-- We avoid `L ^ k` (HPow on LinearMap requires Module.End instance resolution)
-- and instead define iteration explicitly, which is both constructive and robust.
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Iterate a linear map `k` times on a vector. -/
def iterateApp (L : (S → R) →ₗ[R] (S → R)) (ψ : S → R) : ℕ → (S → R)
  | 0     => ψ
  | n + 1 => L (iterateApp L ψ n)

/--
  **Eigenvalue propagation**: If `L ψ = μ • ψ`, then `L^k ψ = μ^k • ψ`.
-/
theorem eigen_iterate
    (L : (S → R) →ₗ[R] (S → R))
    (ψ : S → R) (μ : R)
    (hEig : L ψ = μ • ψ) :
    ∀ k : ℕ, iterateApp R L ψ k = μ ^ k • ψ := by
  intro k; induction k with
  | zero => simp [iterateApp, pow_zero, one_smul]
  | succ n ih =>
    -- iterateApp L ψ (n+1) = L (iterateApp L ψ n) = L (μ^n • ψ) = μ^n • (L ψ) = μ^n • μ • ψ
    simp only [iterateApp]
    rw [ih, map_smul, hEig, smul_smul, pow_succ]

/--
  **Periodicity ⇒ eigenvalue constraint**:
  If `L^n ψ = ψ` and `L ψ = μ • ψ`, then `μ^n • ψ = ψ`.
-/
theorem period_constrains_eigenvalue
    (L : (S → R) →ₗ[R] (S → R))
    (ψ : S → R) (μ : R) {n : ℕ}
    (hEig : L ψ = μ • ψ) (hPeriod : iterateApp R L ψ n = ψ) :
    μ ^ n • ψ = ψ := by
  rw [← eigen_iterate R L ψ μ hEig n]; exact hPeriod

/--
  **Phase theorem (strong form)**:
  In an integral domain, if `L^n ψ = ψ`, `L ψ = μ • ψ`, and `ψ(x₀) ≠ 0`,
  then `μ^n = 1`.

  This is a **non-tautological** derivation: algebraic periodicity of the
  transport operator forces eigenvalues to be roots of unity.
-/
class ConstructiveDomain (R : Type) [CommRing R] [DecidableEq R] : Prop where
  mul_eq_zero_iff : ∀ {a b : R}, a * b = 0 ↔ a = 0 ∨ b = 0

theorem eigenvalue_is_root_of_unity [ConstructiveDomain R]
    (L : (S → R) →ₗ[R] (S → R))
    (ψ : S → R) (μ : R) {n : ℕ}
    (hEig : L ψ = μ • ψ)
    (hPeriod : iterateApp R L ψ n = ψ)
    (x₀ : S) (hNZ : ψ x₀ ≠ 0) :
    μ ^ n = 1 := by
  have hψ := period_constrains_eigenvalue R L ψ μ hEig hPeriod
  -- At x₀: μ^n * ψ(x₀) = ψ(x₀)
  have hx : μ ^ n * ψ x₀ = ψ x₀ := congr_fun hψ x₀
  -- (μ^n - 1) * ψ(x₀) = 0
  have hzero : (μ ^ n - 1) * ψ x₀ = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr hx
  -- Use ConstructiveDomain to avoid Classical logic in IsDomain
  have h_left : μ ^ n - 1 = 0 := by
    have hOr : μ ^ n - 1 = 0 ∨ ψ x₀ = 0 := ConstructiveDomain.mul_eq_zero_iff.mp hzero
    cases hOr with
    | inl h => exact h
    | inr h => contradiction
  exact sub_eq_zero.mp h_left

-- ═══════════════════════════════════════════════════════════════════════════════
-- § 9. The Bridge: Holonomy eigenvalue ⇒ interference
-- ═══════════════════════════════════════════════════════════════════════════════

/--
  **Bridge Theorem**: If `H = L_p ∘ L_q†` has eigenstate `ψ` with eigenvalue `λ`,
  and `ψ ∈ Im(L_q)`, then setting `φ = L_q† ψ`:
  ```
  L_p φ = λ · L_q φ
  ```
  (amplitude via p = λ × amplitude via q).
-/
theorem bridge_amplitude_relation
    {RRel QRel : S → S → Prop} [DecidableRel RRel] [DecidableRel QRel]
    (ψ : AmplitudeSpace S R) (eigenvalue : R)
    (hEigen : LinearMap.comp (ToLinear R RRel) (ToLinear R (fun y x => QRel x y)) ψ
              = eigenvalue • ψ)
    (hInImage : LinearMap.comp (ToLinear R QRel) (ToLinear R (fun y x => QRel x y)) ψ = ψ) :
    let φ := (ToLinear R (fun y x => QRel x y)) ψ
    (ToLinear R RRel) φ = eigenvalue • (ToLinear R QRel) φ := by
  dsimp
  rw [← LinearMap.comp_apply (ToLinear R QRel), hInImage,
      ← LinearMap.comp_apply (ToLinear R RRel)]
  exact hEigen

/--
  **Unconditional Bridge**: When `QRel` is conservative + surjective,
  every `ψ` is in `Im(L_q)`, so the bridge holds for all `ψ`.
-/
theorem bridge_unconditional
    {RRel QRel : S → S → Prop} [DecidableRel RRel] [DecidableRel QRel]
    (hFQ : SingleValued QRel) (hIQ : InjectiveRel QRel) (hSQ : Surjective QRel)
    (ψ : AmplitudeSpace S R) (eigenvalue : R)
    (hEigen : LinearMap.comp (ToLinear R RRel) (ToLinear R (fun y x => QRel x y)) ψ
              = eigenvalue • ψ) :
    let φ := (ToLinear R (fun y x => QRel x y)) ψ
    (ToLinear R RRel) φ = eigenvalue • (ToLinear R QRel) φ := by
  apply bridge_amplitude_relation R ψ eigenvalue hEigen
  ext y; exact right_unitary_of_surjective R QRel hFQ hIQ hSQ ψ y

end ConstructiveAlgebra

end PrimitiveHolonomy.Unitarity

-- ═══════════════════════════════════════════════════════════════════════════════
-- Axiom checks
-- ═══════════════════════════════════════════════════════════════════════════════

#print axioms PrimitiveHolonomy.Unitarity.ToLinear
#print axioms PrimitiveHolonomy.Unitarity.InnerProduct
#print axioms PrimitiveHolonomy.Unitarity.toLinear_adjoint_eq_converse
#print axioms PrimitiveHolonomy.Unitarity.partial_isometry_domain
#print axioms PrimitiveHolonomy.Unitarity.partial_isometry_image
#print axioms PrimitiveHolonomy.Unitarity.left_unitary_of_total
#print axioms PrimitiveHolonomy.Unitarity.right_unitary_of_surjective
#print axioms PrimitiveHolonomy.Unitarity.full_unitary
#print axioms PrimitiveHolonomy.Unitarity.conservative_comp
#print axioms PrimitiveHolonomy.Unitarity.eigen_iterate
#print axioms PrimitiveHolonomy.Unitarity.period_constrains_eigenvalue
#print axioms PrimitiveHolonomy.Unitarity.eigenvalue_is_root_of_unity
#print axioms PrimitiveHolonomy.Unitarity.bridge_amplitude_relation
#print axioms PrimitiveHolonomy.Unitarity.bridge_unconditional
