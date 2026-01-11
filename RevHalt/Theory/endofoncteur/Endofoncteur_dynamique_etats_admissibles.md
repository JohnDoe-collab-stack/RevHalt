# Endofoncteur dynamique sur les états admissibles

## Données et notations

On fixe :

* un type de formules `PropT` ;
* une prouvabilité relative `Provable : Set PropT × PropT → Prop` ;
* des codes `Code`, des traces `Trace`, et une exécution `Machine : Code → Trace` ;
* un kit `K` et un prédicat de certification `Rev0_K(K, ·) : Trace → Prop` ;
* un encodage `encode_halt : Code → PropT` ("ce code s’arrête") ;
* une clôture `Cn : Set PropT → Set PropT`.

### Axiomes (structure)

On supposera typiquement :

* **(PMon) Monotonie de la prouvabilité :**
  `Γ ⊆ Δ ⇒ (Provable(Γ, p) ⇒ Provable(Δ, p))`.
* **(CnExt) Extensivité :** `Γ ⊆ Cn(Γ)`.
* **(CnMon) Monotonie :** `Γ ⊆ Δ ⇒ Cn(Γ) ⊆ Cn(Δ)`.
* **(CnIdem) Idempotence :** `Cn(Cn(Γ)) = Cn(Γ)`.
* **(PCn) Production de `ProvClosed` :** `∀ Γ, ProvClosed(Cn(Γ))`.

On travaille en logique classique lorsque l’on utilise un raisonnement par cas sur `Provable(Δ, p)`.

### Admissibilité

On définit :

```
ProvClosed(Γ) :⇔ ∀ p, Provable(Γ, p) → p ∈ Γ
```

On définit aussi l’**absorbabilité** :

```
Absorbable(Γ) :⇔ ∀ p, p ∈ Γ → Provable(Γ, p)
```

(En pratique, `Absorbable` est une moitié de "post-splitter" : appartenance ⇔ prouvabilité.)

## Frontière dynamique et pas sur corpus

Pour `Γ ⊆ PropT`, on définit la **frontière relative** :

```
S1(Γ) = { p | ∃ e ∈ Code, p = encode_halt(e) ∧ Rev0_K(K, Machine(e)) ∧ ¬Provable(Γ, encode_halt(e)) }
```

On pose ensuite :

```
F0(Γ) := Γ ∪ S1(Γ)
F(Γ) := Cn(F0(Γ)) = Cn(Γ ∪ S1(Γ))
```

Le caractère **dynamique** vient du fait que `S1(Γ)` dépend de `Γ` via `¬Provable(Γ, ·)` et doit être recalculée à chaque pas.

## Catégorie mince des états admissibles

On définit `ThState` comme la catégorie (préordre) dont :

* les objets sont les états admissibles `A = (Γ, Cn(Γ)=Γ, ProvClosed(Γ))` ;
* les morphismes `A → B` sont les inclusions `A.Γ ⊆ B.Γ`.

La catégorie est mince : entre deux objets, il y a au plus une flèche.

## Résultats principaux

### Proposition (Anti-monotonie de la frontière) (`S1Rel_anti_monotone`)

Sous (PMon), si `Γ ⊆ Δ` alors :

```
S1(Δ) ⊆ S1(Γ)
```

**Preuve (Idée) :**
Si `p ∈ S1(Δ)`, alors `p = encode_halt(e)`, `Rev0_K(K, Machine(e))` et `¬Provable(Δ, p)`.
Si `Provable(Γ, p)`, alors par (PMon) on aurait `Provable(Δ, p)`, contradiction.
Donc `¬Provable(Γ, p)` et `p ∈ S1(Γ)`.

### Lemme (Monotonie relative de F0) (`F0_monotone_of_provClosed`)

Si `Γ ⊆ Δ` et `ProvClosed(Δ)`, alors :

```
F0(Γ) ⊆ F0(Δ)
```

**Preuve (Schéma) :**
Soit `p ∈ F0(Γ)`.

* Si `p ∈ Γ`, alors `p ∈ Δ`, donc `p ∈ F0(Δ)`.
* Si `p ∈ S1(Γ)`, on a `p = encode_halt(e)`, `Rev0_K(K, Machine(e))` et `¬Provable(Γ, p)`.
  Par cas sur `Provable(Δ, p)` :
  * Si `Provable(Δ, p)`, alors `ProvClosed(Δ)` implique `p ∈ Δ`, donc `p ∈ F0(Δ)`.
  * Sinon `¬Provable(Δ, p)`, donc `p ∈ S1(Δ) ⊆ F0(Δ)`.

### Théorème (Endofoncteur dynamique) (`TheoryStepFunctor`)

Sous (CnIdem), (CnMon), (PCn), l’application

```
Step(A).Γ := F(A.Γ) = Cn(A.Γ ∪ S1(A.Γ))
```

définit un endofoncteur

```
TheoryStepFunctor : ThState → ThState
```

**Preuve (Idée) :**

* *(Bien-définition sur objets)* : (CnIdem) donne `Cn(Step(A).Γ) = Step(A).Γ`, et (PCn) donne `ProvClosed(Step(A).Γ)`.
* *(Action sur morphismes)* : Si `A.Γ ⊆ B.Γ`, alors `B.ProvClosed` et le lemme précédent donnent `F0(A.Γ) ⊆ F0(B.Γ)`, puis (CnMon) donne `Cn(F0(A.Γ)) ⊆ Cn(F0(B.Γ))`.
* *(Lois fonctorielles)* : La catégorie étant mince, `map_id` et `map_comp` sont immédiats.

### Définition (Chaîne itérée) (`chainState`)

Pour `A_0 ∈ ThState`, on définit :

```
A_0 := A_0
A_{n+1} := TheoryStepFunctor(A_n)
```

Ainsi,

```
A_{n+1}.Γ = Cn(A_n.Γ ∪ S1(A_n.Γ))
```

## Invariants et phénomènes de limite

### Définition (Défaut relatif)

Pour `Γ ⊆ PropT` et `Δ ⊆ PropT`, on pose :

```
MissingFrom(Γ, Δ) := { p | p ∈ Δ ∧ ¬Provable(Γ, p) }
```

### Proposition ("Conservation" : Missing = S1) (`missing_F0_eq_S1_of_absorbable`)

Si `Absorbable(Γ)`, alors :

```
MissingFrom(Γ, F0(Γ)) = S1(Γ)
```

**Preuve (Idée) :**
Si `p ∈ MissingFrom(Γ, F0(Γ))`, alors `p ∈ F0(Γ) = Γ ∪ S1(Γ)` et `¬Provable(Γ, p)`.
Le cas `p ∈ Γ` contredit `Absorbable(Γ)`, donc `p ∈ S1(Γ)`.
La réciproque est immédiate : `S1(Γ) ⊆ F0(Γ)` et, par définition, `p ∈ S1(Γ) ⇒ ¬Provable(Γ, p)`.

### Théorème (Croissance stricte sous témoin) (`strict_F_of_absorbable` / `strict_step_state`)

Sous (CnExt), si `Absorbable(Γ)` et il existe un témoin de frontière :

```
∃ e, Rev0_K(K, Machine(e)) ∧ ¬Provable(Γ, encode_halt(e))
```

alors

```
Γ ⊂ F(Γ)
```

**Preuve (Idée) :**
Le témoin donne `encode_halt(e) ∈ S1(Γ)`, donc `encode_halt(e) ∈ Γ ∪ S1(Γ)` puis, par (CnExt), `encode_halt(e) ∈ Cn(Γ ∪ S1(Γ)) = F(Γ)`.
Si `Γ = F(Γ)`, alors `encode_halt(e) ∈ Γ`, donc par `Absorbable(Γ)` on aurait `Provable(Γ, encode_halt(e))`, contradiction.

### Définition (Limite ω)

On définit le porteur limite :

```
ωΓ := ⋃_{n ∈ ℕ} A_n.Γ
(i.e. p ∈ ωΓ ⇔ ∃ n, p ∈ A_n.Γ)
```

### Théorème (ω-collapse) (`S1Rel_omegaΓ_eq_empty_of_absorbable_succ`)

Sous (PMon), (CnExt), (CnIdem), (PCn), si `Absorbable(A_1.Γ)` alors :

```
S1(ωΓ) = ∅
```

**Preuve (Idée) :**
Supposons `p = encode_halt(e) ∈ S1(ωΓ)`. Alors `¬Provable(ωΓ, p)`.
Par contraposée de (PMon) appliquée à `A_0.Γ ⊆ ωΓ`, on obtient `¬Provable(A_0.Γ, p)`, donc `p ∈ S1(A_0.Γ)`.
Ainsi `p ∈ A_0.Γ ∪ S1(A_0.Γ)`, puis par (CnExt) on a `p ∈ A_1.Γ`.
Par `Absorbable(A_1.Γ)` on obtient `Provable(A_1.Γ, p)`, puis (PMon) via `A_1.Γ ⊆ ωΓ` donne `Provable(ωΓ, p)`, contradiction.

### Définition (Admissibilité à ω et Route II)

On pose :

```
OmegaAdmissible(ωΓ) :⇔ Cn(ωΓ) = ωΓ ∧ ProvClosed(ωΓ)
RouteIIAt(ωΓ) :⇔ S1(ωΓ) ≠ ∅
```

### Théorème (Trilemme à ω) (`omega_trilemma_disjunction`)

Sous (PMon), (CnExt), (CnIdem), (PCn), pour toute orbite issue de `A_0` on a :

```
¬Absorbable(A_1.Γ) ∨ ¬OmegaAdmissible(ωΓ) ∨ ¬RouteIIAt(ωΓ)
```

**Preuve (Idée) :**
Si `Absorbable(A_1.Γ)` et `OmegaAdmissible(ωΓ)` tenaient, alors le théorème de ω-collapse impose `S1(ωΓ) = ∅`, donc `¬RouteIIAt(ωΓ)`.

## Lecture ("punchline")

La nouveauté n’est pas la clôture `Cn` (statique), mais le couplage dynamique :

```
Γ ↦ Cn(Γ ∪ S1(Γ))
```

où `S1` dépend de `¬Provable(Γ, ·)`.
La restriction aux états admissibles rend ce pas **fonctoriel**, et permet ensuite d’obtenir des phénomènes intrinsèquement dynamiques (croissance stricte, collapse à ω, trilemmes structuraux) invisibles dans une présentation purement statique.
