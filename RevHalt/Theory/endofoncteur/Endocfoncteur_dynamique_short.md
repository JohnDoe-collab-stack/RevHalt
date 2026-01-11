# Endofoncteur dynamique : version compacte

## Cadre

On fixe :

* un type de formules `PropT` ;
* une prouvabilité relative `Provable : Set PropT × PropT → Prop` ;
* des codes `Code`, des traces `Trace`, une exécution `Machine : Code → Trace` ;
* un kit `K` et une certification `Rev0_K(K, ·) : Trace → Prop` ;
* un encodage `encode_halt : Code → PropT` ;
* une clôture `Cn : Set PropT → Set PropT`.

### Hypothèses

* **(PMon) Monotonie de la prouvabilité :** `Γ ⊆ Δ ⇒ (Provable(Γ, p) ⇒ Provable(Δ, p))`.
* **(CnMon) Monotonie de Cn :** `Γ ⊆ Δ ⇒ Cn(Γ) ⊆ Cn(Δ)`.
* **(CnIdem) Idempotence :** `Cn(Cn(Γ)) = Cn(Γ)`.
* **(CnExt) Extensivité :** `Γ ⊆ Cn(Γ)`.
* **(PCn) Production de ProvClosed :** `∀ Γ, ProvClosed(Cn(Γ))`.

On travaille en logique classique quand un raisonnement par cas sur `Provable(Δ, p)` est utilisé.

### Admissibilité

On définit :

```
ProvClosed(Γ) :⇔ ∀ p, Provable(Γ, p) → p ∈ Γ
```

On définit aussi l’absorbabilité :

```
Absorbable(Γ) :⇔ ∀ p, p ∈ Γ → Provable(Γ, p)
```

## Frontière dynamique et pas

### Frontière

Pour `Γ ⊆ PropT`, on pose :

```
S1(Γ) = { p | ∃ e ∈ Code, p = encode_halt(e) ∧ Rev0_K(K, Machine(e)) ∧ ¬Provable(Γ, encode_halt(e)) }
```

### Pas

On pose :

```
F0(Γ) := Γ ∪ S1(Γ)
F(Γ) := Cn(F0(Γ)) = Cn(Γ ∪ S1(Γ))
```

**Point central.** `S1(Γ)` dépend de `Γ` via `¬Provable(Γ, ·)` : c’est une **frontière recalculée** à chaque pas. Le caractère non trivial est que `S1` est anti-monotone, mais `F` peut tout de même devenir fonctoriel sur une classe d’états admissibles.

## États admissibles et catégorie mince

On définit la catégorie (préordre) `ThState` :

* objets : `A = (Γ, Cn(Γ)=Γ, ProvClosed(Γ))` ;
* morphismes `A → B` : inclusions `A.Γ ⊆ B.Γ`.

La catégorie est mince : entre deux objets il y a au plus une flèche.

## Lemme-clé : monotonie relative du pas minimal

### Lemme (Monotonie relative de F0)

Si `Γ ⊆ Δ` et `ProvClosed(Δ)`, alors :

```
F0(Γ) ⊆ F0(Δ)
```

**Preuve (Idée) :**
Soit `p ∈ F0(Γ)`.

* Si `p ∈ Γ`, alors `p ∈ Δ`, donc `p ∈ F0(Δ)`.
* Si `p ∈ S1(Γ)`, on a `p = encode_halt(e)`, `Rev0_K(K, Machine(e))` et `¬Provable(Γ, p)`.
  Par cas sur `Provable(Δ, p)` :
  * Si `Provable(Δ, p)`, alors `ProvClosed(Δ)` implique `p ∈ Δ ⊆ F0(Δ)` ;
  * Sinon `¬Provable(Δ, p)`, donc `p ∈ S1(Δ) ⊆ F0(Δ)`.

## Endofoncteur dynamique

### Théorème (Endofoncteur)

Sous (CnIdem), (CnMon), (PCn), l’application

```
Step(A).Γ := F(A.Γ) = Cn(A.Γ ∪ S1(A.Γ))
```

définit un endofoncteur

```
TheoryStepFunctor : ThState → ThState
```

**Preuve (Esquisse) :**

* *Objets* : (CnIdem) donne `Cn(Step(A).Γ) = Step(A).Γ` et (PCn) donne `ProvClosed(Step(A).Γ)`.
* *Morphismes* : si `A.Γ ⊆ B.Γ`, alors `B.ProvClosed` donne `F0(A.Γ) ⊆ F0(B.Γ)` par le lemme précédent, puis (CnMon) donne `F(A.Γ) ⊆ F(B.Γ)`.
* *Lois fonctorielles* : trivial dans une catégorie mince.

## Dynamique itérée

### Définition (Chaîne)

Pour `A_0 ∈ ThState`, on définit :

```
A_0 := A_0,
A_{n+1} := TheoryStepFunctor(A_n)
```

Donc

```
A_{n+1}.Γ = Cn(A_n.Γ ∪ S1(A_n.Γ))
```

## Phénomènes : croissance stricte, ω-collapse, trilemme

### Témoin de frontière

On dira que `Γ` admet un témoin si :

```
FrontierWitness(Γ) :⇔ ∃ e, Rev0_K(K, Machine(e)) ∧ ¬Provable(Γ, encode_halt(e))
```

### Théorème (Croissance stricte sous absorbabilité + témoin)

Sous (CnExt), si `Absorbable(Γ)` et `FrontierWitness(Γ)`, alors :

```
Γ ⊂ F(Γ)
```

**Preuve (Idée) :**
Le témoin donne `p = encode_halt(e) ∈ S1(Γ) ⊆ Γ ∪ S1(Γ)`, donc `p ∈ F(Γ)` par (CnExt).
Si `Γ = F(Γ)`, alors `p ∈ Γ`, donc `Provable(Γ, p)` par `Absorbable(Γ)`, contradiction avec la définition de `S1(Γ)`.

### Limite ω

On pose le porteur limite :

```
ωΓ := ⋃_{n ∈ ℕ} A_n.Γ
(i.e. p ∈ ωΓ ⇔ ∃ n, p ∈ A_n.Γ)
```

### Théorème (ω-collapse)

Sous (PMon), (CnExt), (CnIdem), (PCn), si `Absorbable(A_1.Γ)` alors :

```
S1(ωΓ) = ∅
```

**Preuve (Idée) :**
Supposons `p = encode_halt(e) ∈ S1(ωΓ)`, donc `¬Provable(ωΓ, p)`.
Par contraposée de (PMon) et `A_0.Γ ⊆ ωΓ`, on a `¬Provable(A_0.Γ, p)`, donc `p ∈ S1(A_0.Γ)`.
Ainsi `p ∈ A_0.Γ ∪ S1(A_0.Γ)` et donc `p ∈ A_1.Γ` par (CnExt).
Puis `Absorbable(A_1.Γ)` donne `Provable(A_1.Γ, p)`, et (PMon) via `A_1.Γ ⊆ ωΓ` donne `Provable(ωΓ, p)`, contradiction.

### Route II et admissibilité à ω

On définit :

```
OmegaAdmissible(ωΓ) :⇔ Cn(ωΓ) = ωΓ ∧ ProvClosed(ωΓ)
RouteIIAt(ωΓ) :⇔ S1(ωΓ) ≠ ∅
```

### Théorème (Trilemme à ω)

Sous (PMon), (CnExt), (CnIdem), (PCn), on a :

```
¬Absorbable(A_1.Γ) ∨ ¬OmegaAdmissible(ωΓ) ∨ ¬RouteIIAt(ωΓ)
```

**Preuve (Idée) :**
Si `Absorbable(A_1.Γ)` tenait, alors le théorème de ω-collapse donne `S1(ωΓ) = ∅`, donc `¬RouteIIAt(ωΓ)`.

## Conclusion (message structurel)

Le pas

```
Γ ↦ Cn(Γ ∪ S1(Γ))
```

couple une clôture statique `Cn` à une frontière dynamique `S1` définie via `¬Provable(Γ, ·)`.
La restriction aux états admissibles (où la prouvabilité s’absorbe en appartenance) rend ce pas **fonctoriel**.
Cette fonctorialité rend ensuite accessibles des phénomènes intrinsèquement dynamiques (croissance stricte, collapse à ω, trilemme) qui n’apparaissent pas dans une lecture purement statique des théories.
