# Endofoncteur dynamique sur les états admissibles

## 1. Données

On fixe :

* `PropT` : type des formules.
* `Provable : Set PropT -> PropT -> Prop` : prouvabilité relative.
* `Code` : type des programmes/codes.
* `Trace` : type des traces.
* `Machine : Code -> Trace` : exécution d’un code en une trace.
* `K` : un kit de certification.
* `Rev0_K K : Trace -> Prop` : certification d’une trace par le kit.
* `encode_halt : Code -> PropT` : encodage de “ce code s’arrête”.
* `Cn : Set PropT -> Set PropT` : opérateur de clôture.

On définit :

```
ProvClosed(Gamma) := forall p, Provable(Gamma, p) -> p ∈ Gamma
```

---

## 2. Frontière et pas dynamique sur corpus

Pour `Gamma : Set PropT`, on définit la frontière :

```
S1Rel(Gamma) :=
  { p | exists e : Code,
      p = encode_halt e
      ∧ Rev0_K K (Machine e)
      ∧ not Provable(Gamma, encode_halt e) }
```

Puis :

```
F0(Gamma) := Gamma ∪ S1Rel(Gamma)
F (Gamma) := Cn (F0(Gamma))
```

Le caractère dynamique vient de ce que `S1Rel(Gamma)` dépend de l’état courant `Gamma` via `not Provable(Gamma, ...)`, et est donc recalculé à chaque pas.

---

## 3. Catégorie des états admissibles

### Objets

Un objet est un état admissible `A` composé de :

* `A.Gamma : Set PropT`
* `A.cn_closed : Cn A.Gamma = A.Gamma`
* `A.prov_closed : ProvClosed(A.Gamma)`

On appelle cette structure `ThState`.

### Morphismes

Un morphisme `A ⟶ B` est une inclusion :

```
A.Gamma ⊆ B.Gamma
```

Cette catégorie est mince (préordre).

---

## 4. Hypothèses sur Cn

On suppose :

1. Idempotence :

```
CnIdempotent := forall X, Cn (Cn X) = Cn X
```

2. Production de ProvClosed :

```
ProvClosedCn := forall X, ProvClosed (Cn X)
```

3. Monotonie :

```
CnMonotone := forall X Y, X ⊆ Y -> Cn X ⊆ Cn Y
```

Hypothèse logique : on utilise un raisonnement par cas sur `Provable(Delta, p)` (cadre classique ou décidabilité suffisante) dans le lemme de monotonie relative ci-dessous.

---

## 5. Construction de l’état suivant (pas sur états)

Pour `A : ThState`, on définit l’état suivant `Step(A) : ThState` par :

### 5.1 Porteur

```
(Step(A)).Gamma := F(A.Gamma) := Cn (A.Gamma ∪ S1Rel(A.Gamma))
```

### 5.2 Conditions d’admissibilité

* `CnIdempotent` assure `Cn (Step(A).Gamma) = Step(A).Gamma`.
* `ProvClosedCn` assure `ProvClosed(Step(A).Gamma)`.

Donc `Step(A)` est bien un objet de `ThState`.

---

## 6. Lemme clé : monotonie relative de F0

Si `Gamma ⊆ Delta` et `ProvClosed(Delta)`, alors :

```
F0(Gamma) ⊆ F0(Delta)
```

Preuve (schéma) : si `p ∈ F0(Gamma)` :

* soit `p ∈ Gamma`, alors `p ∈ Delta`, donc `p ∈ F0(Delta)`;
* soit `p ∈ S1Rel(Gamma)`, donc `p = encode_halt e` avec certification, et `not Provable(Gamma, p)`.
  On raisonne par cas sur `Provable(Delta, p)` :

  * si `Provable(Delta, p)`, alors `ProvClosed(Delta)` donne `p ∈ Delta`, donc `p ∈ F0(Delta)`;
  * sinon `not Provable(Delta, p)`, donc `p ∈ S1Rel(Delta)`, donc `p ∈ F0(Delta)`.

---

## 7. Endofoncteur dynamique

### 7.1 Définition

On définit un endofoncteur :

```
TheoryStepFunctor : ThState ⥤ ThState
```

par :

* sur objets :

  ```
  TheoryStepFunctor.obj A := Step(A)
  ```

* sur morphismes : pour `h : A ⟶ B` (i.e. `A.Gamma ⊆ B.Gamma`), on définit `TheoryStepFunctor.map h` comme l’inclusion

  ```
  Step(A).Gamma ⊆ Step(B).Gamma
  ```

  obtenue par :

  * le lemme de monotonie relative : `F0(A.Gamma) ⊆ F0(B.Gamma)` (car `B.prov_closed`),
  * puis `CnMonotone` : `Cn(F0(A.Gamma)) ⊆ Cn(F0(B.Gamma))`,
  * donc `F(A.Gamma) ⊆ F(B.Gamma)`.

### 7.2 Lois fonctorielles

La catégorie étant mince, dès que l’on a défini l’action sur morphismes (préservation des inclusions), les lois `map_id` et `map_comp` sont immédiates.

---

## 8. Dynamique induite (itération)

Pour un état initial `A0 : ThState`, on définit une suite d’états par itération du pas :

```
chainState 0     := A0
chainState (n+1) := TheoryStepFunctor.obj (chainState n)
```

Donc :

```
(chainState (n+1)).Gamma = Cn ((chainState n).Gamma ∪ S1Rel((chainState n).Gamma))
```

---

## 9. Résultat

Sous `CnIdempotent`, `ProvClosedCn`, `CnMonotone` (et le cadre logique permettant le raisonnement par cas utilisé dans le lemme clé), l’application

```
A ↦ Cn (A.Gamma ∪ S1Rel(A.Gamma))
```

définit :

* un endofoncteur `TheoryStepFunctor : ThState ⥤ ThState`,
* et une dynamique discrète `chainState` donnée par l’itération de cet endofoncteur.
