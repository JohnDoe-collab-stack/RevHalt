# TheoryDynamics — Analyse technique

Ce document présente l'analyse formelle du module TheoryDynamics et sa distinction fondamentale avec les théorèmes de points fixes classiques (Tarski, Lawvere).

---

## 1. Vue d'ensemble

Le module TheoryDynamics formalise un **système dynamique sur les théories formelles**. L'objectif est de comprendre comment une théorie évolue lorsqu'elle tente d'internaliser un prédicat externe (halting).

### 1.1 Fichiers concernés

| Fichier | Lignes | Rôle |
|---------|--------|------|
| `TheoryDynamics.lean` | 1410 | Noyau : F, S1Rel, trilemme |
| `TheoryDynamics_RouteII.lean` | 285 | Connexion T2, frontière forcée |
| `TheoryDynamics_Trajectory.lean` | 388 | Escape structurel, incarnation |
| `TheoryDynamics_TwoSided.lean` | 237 | Extension bidirectionnelle |
| `TheoryDynamics_Transfinite.lean` | 885 | Ordinaux, Fork Law |
| `TheoryDynamics_Transfinite_Jump.lean` | 246 | Opérateurs limite avec saut |
| `TheoryDynamics_Transfinite_JumpFixpoint.lean` | 233 | Points fixes depuis continuité |
| `TheoryDynamics_ProofCarrying.lean` | 208 | Dérivations witness-carrying |
| `TheoryDynamics_ComplexityBounds.lean` | 111 | IsPoly, PolyPosWC |
| `TheoryDynamics_CanonizationWC.lean` | 214 | PosComplete, compression |
| `TheoryDynamics_PriceOfP_Nontriviality.lean` | 148 | Séparations Price-of-P |

---

## 2. Définitions fondamentales

### 2.1 La frontière dynamique S1Rel

```
S1Rel(Γ) := { encode_halt(e) | Rev0_K(Machine(e)) ∧ ¬Provable(Γ, encode_halt(e)) }
```

**Fichier** : `TheoryDynamics.lean`, ligne 134

C'est l'ensemble des énoncés :

- Certifiés par le Kit externe (Rev0_K)
- Mais non prouvables dans la théorie courante Γ

### 2.2 Les opérateurs de pas

**F0** (sans closure) — ligne 179 :

```
F0(Γ) := Γ ∪ S1Rel(Γ)
```

**F** (avec closure) — ligne 187 :

```
F(Γ) := Cn(Γ ∪ S1Rel(Γ))
```

### 2.3 Propriétés structurelles

| Définition | Signature | Ligne |
|------------|-----------|-------|
| `Absorbable(Γ)` | `∀p, p ∈ Γ → Provable(Γ, p)` | 392 |
| `OmegaAdmissible(ωΓ)` | `Cn(ωΓ) = ωΓ ∧ ProvClosed(ωΓ)` | 944 |
| `RouteIIAt(ωΓ)` | `S1Rel(ωΓ).Nonempty` | 1232 |
| `OmegaContinuousSet(F)` | `F(⋃Uₙ) = ⋃F(Uₙ)` pour chaînes croissantes | 304 |

---

## 3. L'anti-monotonicité de S1Rel

**Théorème** (`S1Rel_anti_monotone`, ligne 155) :

```
Γ ⊆ Δ  →  S1(Δ) ⊆ S1(Γ)
```

Quand la théorie grandit, la frontière **rétrécit**. Mais F injecte S1 dans le pas suivant, régénérant la frontière.

---

## 4. Le phénomène de collapse ordinal

### 4.1 Collapse à ω

**Théorème** (`S1Rel_omegaΓ_eq_empty_of_absorbable_succ`, ligne 1113) :

Si `Absorbable(Γ₁)`, alors `S1Rel(ωΓ) = ∅`.

**Preuve** :

1. Soit p dans S1(ωΓ), donc p = encode_halt(e), Rev0_K(e), ¬Provable(ωΓ, p)
2. Par anti-monotonicité : ¬Provable(Γ₀, p), donc p ∈ S1(Γ₀)
3. p est injecté dans Γ₁ par F0
4. Par Absorbable(Γ₁) : Provable(Γ₁, p)
5. Par monotonicité Γ₁ ⊆ ωΓ : Provable(ωΓ, p)
6. Contradiction avec (1)

### 4.2 Collapse transfinite

**Théorème** (`limit_collapse_schema`, Transfinite ligne 398) :

Pour tout ordinal λ limite :

```
(∃β < λ, Absorbable(Γ_{β+1})) → S1Rel(Γ_λ) = ∅
```

Le collapse se reproduit à **tout ordinal limite** où l'absorption a eu lieu avant.

---

## 5. Le trilemme

### 5.1 Énoncé

**Théorème** (`omega_trilemma_not_all`, ligne 1296) :

Les trois conditions suivantes sont mutuellement exclusives :

1. `Absorbable(Γ₁)`
2. `OmegaAdmissible(ωΓ)`  
3. `RouteIIAt(ωΓ)`

### 5.2 Chaîne de dérivation

```
S1Rel_omegaΓ_eq_empty_of_absorbable_succ : Absorbable(Γ₁) → S1(ωΓ) = ∅
            +
RouteIIAt(ωΓ) : S1(ωΓ).Nonempty
            ↓
       Contradiction
            ↓
    omega_trilemma_not_all
```

### 5.3 Corollaires directionnels

| Théorème | Énoncé | Ligne |
|----------|--------|-------|
| `omega_trilemma` | RouteII → ¬Absorbable | 1194 |
| `omega_trilemma_disjunction` | ¬Abs ∨ ¬OmegaAdm ∨ ¬RouteII | 1260 |
| `omega_collapse_structural` | Abs + OmegaAdm + RouteIIApplies → False | 1323 |

---

## 6. La rupture de continuité

### 6.1 Théorème principal

**Théorème** (`structural_escape_explicit`, Trajectory ligne 319) :

```
Absorbable(Γ₁) + RouteIIApplies(ωΓ) → ¬OmegaContinuousSet(F)
```

### 6.2 Mécanisme

1. Si F était ω-continue, par Kleene, ωΓ serait un point fixe : F(ωΓ) = ωΓ
2. Point fixe + hypothèses algébriques → OmegaAdmissible(ωΓ)
3. RouteII + OmegaAdmissible → S1(ωΓ).Nonempty
4. Mais Absorbable → S1(ωΓ) = ∅ (collapse)
5. Contradiction

Donc les **hypothèses de Kleene ne peuvent pas être satisfaites**.

---

## 7. Distinction avec Tarski/Lawvere

### 7.1 Ce que Tarski prouve

Dans un treillis complet, toute fonction monotone a un plus petit point fixe. Pour les fonctions ω-continues, ce point fixe est la limite de l'itération.

### 7.2 Ce que TheoryDynamics prouve

**L'inverse** : les conditions qui permettraient d'obtenir ce point fixe (ω-continuité) sont **incompatibles** avec les propriétés structurelles du système (RouteII).

| Tarski/Lawvere | TheoryDynamics |
|----------------|----------------|
| Prouve existence de points fixes | Prouve **impossibilité** de conditions pour points fixes |
| Hypothèse : F ω-continue | Conclusion : F **non** ω-continue |
| Construction | Obstruction |

### 7.3 Pourquoi le point fixe de Tarski n'aide pas

Le treillis `Set PropT` est complet, F est monotone. Par Tarski, un point fixe existe.

**Mais** : ce point fixe n'est pas ωΓ (la limite de la chaîne). Il faudrait continuer au-delà de ω.

TheoryDynamics montre que cette continuation **ne résout pas le problème** : le collapse se répète à tout ordinal limite où Absorbable a tenu.

---

## 8. Extension transfinite : Fork Law

### 8.1 Énoncé

**Théorème** (`fork_law_False`, Transfinite ligne 747) :

Les 7 conditions suivantes sont mutuellement contradictoires :

1. ProvRelMonotone
2. CnExtensive
3. CnIdem
4. ProvClosedCn
5. Absorbable à un successeur < lim
6. RouteIIApplies à lim
7. ContinuousAtL à lim

### 8.2 Interprétation

Il n'existe **aucun** ordinal limite λ où toutes les propriétés structurelles (1-4), l'absorption (5), RouteII (6) et la continuité (7) peuvent coexister.

---

## 9. Connexions

### 9.1 RouteII et T2

**Théorème** (`frontier_nonempty_T2`, RouteII ligne 268) :

Sous les hypothèses de T2 (Soundness, NegativeComplete, semi-décidabilité), la frontière est **forcément non-vide**.

C'est le pont entre l'impossibilité computationnelle (T2) et la dynamique des théories.

### 9.2 Dépendances axiomatiques

| Théorème | Axiomes |
|----------|---------|
| `S1Rel_anti_monotone` | aucun |
| `omega_trilemma_not_all` | propext |
| `structural_escape_explicit` | propext |
| `limit_collapse_schema` | propext |
| `frontier_nonempty_T2` | Classical.choice (via T2) |

Les résultats structurels (collapse, trilemme, escape) sont **constructifs** (modulo propext). Seule la connexion à T2 utilise choice.

---

## 10. Conclusion

TheoryDynamics établit une **obstruction catégorielle** à la convergence des systèmes dynamiques de théories. Cette obstruction :

1. **N'est pas** une reformulation de Tarski — c'est l'**inverse** (non-existence de conditions)
2. **Explique** pourquoi les hypothèses de Kleene (ω-continuité) échouent
3. **S'étend** à tous les ordinaux limites via le Fork Law
4. **Connecte** T2 (impossibilité computationnelle) à une rupture structurelle

Le résultat principal : la tentative d'internaliser un prédicat externe (halting) dans une théorie formelle produit une dynamique qui **ne peut pas converger** vers un état stable admissible, à quelque ordinal limite que ce soit.
