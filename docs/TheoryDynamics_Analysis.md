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
| `RouteIIApplies(ωΓ)` | `OmegaAdmissible(ωΓ) → S1Rel(ωΓ).Nonempty` | 1250 |
| `OmegaContinuousSet(F)` | `F(⋃Uₙ) = ⋃F(Uₙ)` pour chaînes croissantes | 304 |

### 2.4 Distinction RouteIIAt / RouteIIApplies

- **RouteIIAt(Γ)** : assertion directe que la frontière est non-vide à Γ
- **RouteIIApplies(Γ)** : assertion conditionnelle — si Γ est admissible, alors la frontière est non-vide

`structural_escape_explicit` utilise **RouteIIApplies** (pas seulement RouteIIAt), car la non-continuité se prouve en exploitant la façon dont RouteII interagit avec la dynamique, pas uniquement la non-vacuité brute.

---

## 3. L'anti-monotonicité de S1Rel

**Théorème** (`S1Rel_anti_monotone`, ligne 155) :

```
Γ ⊆ Δ  →  S1(Δ) ⊆ S1(Γ)
```

Quand la théorie grandit, la frontière **rétrécit**. Mais F injecte S1 dans le pas suivant, régénérant la frontière.

---

## 4. Le phénomène de collapse ordinal

### 4.1 Collapse à ω (conditionnel)

**Théorème** (`S1Rel_omegaΓ_eq_empty_of_absorbable_succ`, ligne 1113) :

```
Absorbable(Γ₁) → S1Rel(ωΓ) = ∅
```

**Important** : Ce résultat est **conditionnel** à l'hypothèse Absorbable(Γ₁).

**Preuve** :

1. Soit p dans S1(ωΓ), donc p = encode_halt(e), Rev0_K(e), ¬Provable(ωΓ, p)
2. Par anti-monotonicité : ¬Provable(Γ₀, p), donc p ∈ S1(Γ₀)
3. p est injecté dans Γ₁ par F0
4. Par Absorbable(Γ₁) : Provable(Γ₁, p)
5. Par monotonicité Γ₁ ⊆ ωΓ : Provable(ωΓ, p)
6. Contradiction avec (1)

### 4.2 Collapse transfinite (conditionnel)

**Théorème** (`limit_collapse_schema`, Transfinite ligne 398) :

Pour tout ordinal limite λ :

```
(∃β < λ, Absorbable(Γ_{β+1})) → S1Rel(Γ_λ) = ∅
```

**Lecture** : Toute limite successeur après une absorption antérieure subit le collapse.

Si l'absorption **n'arrive jamais**, le schéma ne conclut rien sur S1Rel aux limites.

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

## 6. L'obstruction de continuité aux limites

### 6.1 Ce que "point fixe" veut dire ici

Le projet **ne nie pas l'existence** d'un point fixe au sens de Tarski (monotonie sur treillis complet). Il montre l'échec de la stratégie **à la Kleene** : atteindre un point fixe via limite d'itération.

Le point fixe pertinent pour RevHalt est le **point fixe accessible par la procédure limite** (union aux limites). `structural_escape_explicit` prouve que cette accessibilité est structurellement impossible dès que (Absorption précoce + RouteII) sont imposées.

### 6.2 Théorème principal

**Théorème** (`structural_escape_explicit`, Trajectory ligne 319) :

```
Absorbable(Γ₁) + RouteIIApplies(ωΓ) → ¬OmegaContinuousSet(F)
```

### 6.3 Mécanisme

1. Si F était ω-continue, par Kleene, ωΓ serait un point fixe : F(ωΓ) = ωΓ
2. Point fixe + hypothèses algébriques → OmegaAdmissible(ωΓ)
3. RouteIIApplies + OmegaAdmissible → S1(ωΓ).Nonempty
4. Mais Absorbable → S1(ωΓ) = ∅ (collapse)
5. Contradiction

Donc la dynamique **ne peut pas satisfaire les hypothèses de Kleene** permettant d'obtenir un point fixe par limite ω.

---

## 7. Distinction avec Tarski/Lawvere

### 7.1 Ce que Tarski prouve

Dans un treillis complet, toute fonction monotone a un plus petit point fixe. Pour les fonctions ω-continues, ce point fixe est la limite de l'itération.

### 7.2 Ce que TheoryDynamics prouve

**L'inverse** : les conditions qui permettraient d'obtenir ce point fixe **par limite** (ω-continuité) sont incompatibles avec les propriétés structurelles du système (RouteII + Absorption).

| Tarski/Lawvere | TheoryDynamics |
|----------------|----------------|
| Prouve existence de points fixes | Prouve impossibilité d'**accès** par continuité |
| Hypothèse : F ω-continue | Conclusion : F **non** ω-continue |
| Construction | Obstruction de continuité aux limites |

### 7.3 Pourquoi le point fixe de Tarski n'aide pas

Le treillis `Set PropT` est complet, F est monotone. Par Tarski, un point fixe existe.

**Mais** : ce point fixe n'est pas ωΓ (la limite de la chaîne). Toute limite successeur après une absorption antérieure subit de nouveau le collapse.

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

Sous les hypothèses de T2 (Soundness, NegativeComplete, semi-décidabilité), la frontière est forcément non-vide.

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

## 10. Théorème principal (version robuste)

### 10.1 Énoncés

Pour tout ordinal limite successeur λ :

**1. Collapse conditionnel à la limite** :

```
(∃β < λ, Absorbable(Γ_{β+1})) → S1Rel(Γ_λ) = ∅
```

**2. Incompatibilité avec RouteII** :

Donc, si RouteIIAt(Γ_λ) (frontière non vide à la limite), alors :

```
∀β < λ, ¬Absorbable(Γ_{β+1})
```

**3. Escape** :

Sous Absorbable(Γ₁) + RouteIIApplies(ωΓ), on a ¬OmegaContinuousSet(F).

### 10.2 Lecture opérationnelle

- **RouteII** force un régime de **non-absorption persistante**, ou bien impose de modifier l'opérateur de limite (les fichiers `Jump` cadrent cette option).
- Dès qu'une absorption apparaît à un successeur, les limites ultérieures "lavent" la frontière (S1Rel = ∅), ce qui est incompatible avec RouteIIAt.

### 10.3 Alternative structurelle

Soit l'absorption survient à un certain successeur, et alors toute limite successeur ultérieure recolle la frontière à vide ;

Soit RouteII est imposé aux limites, et alors aucun successeur antérieur ne peut être absorbable.

---

## 11. Triade majeure

Les trois résultats suivants constituent le cœur de TheoryDynamics :

| Résultat | Fichier | Contenu |
|----------|---------|---------|
| `limit_collapse_schema` | Transfinite:398 | Phénomène transfini universel, conditionnel à absorption |
| `structural_escape_explicit` | Trajectory:319 | Obstruction d'ω-continuité sous RouteII |
| `fork_law_False` | Transfinite:747 | Impossibilité structure + absorption + RouteII + continuité |

Cette triade dit : **le passage au limite par union est le lieu de la pathologie**. C'est un diagnostic structurel sur une dynamique monotone qui échoue à être continue aux limites en présence d'une frontière anti-monotone mais réinjectée.
