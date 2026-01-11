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

1. Production de ProvClosed :

```
ProvClosedCn := forall X, ProvClosed (Cn X)
```

1. Monotonie :

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

xxxxx

xxxxx

### Motivation

Les cadres logiques usuels traitent une théorie `Γ ⊆ PropT` comme un **objet statique** : on fixe `Γ`, on étudie sa clôture déductive `Cn(Γ)`, puis on raisonne sur `Provable(Γ, ·)`. Cette posture convient tant que la “frontière” de la théorie — ce qu’elle ne prouve pas — reste un simple complément passif.

Or, dès qu’on couple une théorie à un mécanisme externe de détection (un *kit* `K` certifiant des traces d’exécution), la frontière devient **active** : ce que la théorie ne prouve pas n’est plus seulement “inconnu”, mais peut être *signalé* comme devant être ajouté (p. ex. des énoncés `Σ₁` de terminaison, certifiés par le kit). Cette situation impose une lecture intrinsèquement **dynamique** : la théorie se réécrit en absorbant une frontière qui dépend de l’état courant.

### Définition de la frontière dynamique

On fixe :

* un prédicat de prouvabilité relative `Provable : Set PropT -> PropT -> Prop`,
* un espace de codes `Code`, des traces `Trace`, une exécution `Machine : Code -> Trace`,
* un kit `K` et un prédicat de certification `Rev0_K K : Trace -> Prop`,
* un encodage `encode_halt : Code -> PropT` pour “ce code s’arrête”.

On définit alors la **frontière relative** de `Γ` :

```
S1(Γ) = { p | ∃ e, p = encode_halt e ∧ Rev0_K K (Machine e) ∧ ¬ Provable(Γ, encode_halt e) }
```

Cette frontière est *dynamique* au sens strict : elle dépend de `Γ` via un prédicat négatif de prouvabilité.

### Le pas de théorie comme endofoncteur (idée centrale)

On considère le pas minimal :

```
F0(Γ) = Γ ∪ S1(Γ)
```

puis le pas complet :

```
F(Γ) = Cn(F0(Γ)) = Cn(Γ ∪ S1(Γ))
```

où `Cn` est un opérateur de clôture (extensif, monotone, idempotent).

Le point surprenant n’est pas l’usage de `Cn`, ni l’itération, mais le fait que `S1` est **anti-monotone** : lorsque `Γ` grandit, il devient plus difficile d’être “non prouvable”, donc `S1(Γ)` tend à rétrécir. A priori, cela compromet la monotonie de `F0`, donc la possibilité de voir `F` comme un endofoncteur.

La clé est de restreindre l’univers à une catégorie d’**états admissibles** où l’appartenance capture la prouvabilité :

```
ProvClosed(Γ) ↔ ∀ p, Provable(Γ, p) -> p ∈ Γ
```

Dans cet univers, si un énoncé sort de la frontière parce qu’il devient prouvable dans un état plus grand `Δ`, alors `ProvClosed(Δ)` impose qu’il est déjà **absorbé** en tant que membre de `Δ`. Ainsi, l’anti-monotonie de `S1` est neutralisée par l’absorption.

On définit donc une catégorie mince `ThState` :

* objets : `A = (Γ, Cn(Γ) = Γ, ProvClosed(Γ))`,
* morphismes : inclusions `Γ ⊆ Δ`.

Sous des hypothèses structurelles naturelles (monotonie/idempotence de `Cn`, et le fait que `Cn` produise des ensembles `ProvClosed`), l’application :

```
A ↦ (Cn(A.Γ ∪ S1(A.Γ)), ...)
```

définit un **endofoncteur** `ThState -> ThState`. On obtient alors une dynamique discrète canonique :

```
A_{n+1} = F(A_n)
```

et la théorie pertinente devient l’**orbite** `(A_n)`, plutôt qu’un état isolé.

### Conséquence conceptuelle

Ce passage du statique au dynamique rend visibles des phénomènes structurels (croissance stricte, comportement aux limites, “collapse” à `ω`, trilemmes de compatibilité entre absorption, admissibilité et non-vacuité de frontière) qui ne se formulent pas dans le cadre statique classique. En bref : on ne se demande plus seulement “qu’est-ce qui est prouvable dans `Γ` ?”, mais “qu’est-ce qui peut se stabiliser quand la frontière est recalculée à chaque pas ?”.

---

## Option 3 — Théorèmes (style “énoncé + interprétation”)

Je reprends tes dénominations (`S1Rel`, `F0`, `F`, `ThState`, `FState`, `TheoryStepFunctor`, `chainState`, `omegaΓ`, etc.) et j’explicite ce que chaque résultat “veut dire”.

### (T1) Anti-monotonie de la frontière

**Énoncé (dans ton code : `S1Rel_anti_monotone`).**
Sous la monotonie de `Provable` (si `Γ ⊆ Δ` alors `Provable(Γ, p) => Provable(Δ, p)`), on a :

```
Γ ⊆ Δ => S1Rel(Δ) ⊆ S1Rel(Γ)
```

**Interprétation.**
Plus une théorie est forte, plus la “frontière non prouvable” se contracte. C’est la source de la non-fonctorialité “naïve”.

---

### (T2) Monotonie relative de F0 grâce à `ProvClosed`

**Énoncé (dans ton code : `F0_monotone_of_provClosed`).**
Si `Γ ⊆ Δ` et `ProvClosed Δ`, alors :

```
F0(Γ) ⊆ F0(Δ)
```

**Interprétation.**
C’est la pièce maîtresse : on récupère une croissance monotone du “pas minimal” malgré la présence d’un composant anti-monotone, parce que ce qui “sort” de la frontière est automatiquement absorbé comme membre de `Δ`. C’est le mécanisme exact qui rend possible un endofoncteur.

---

### (T3) Endofoncteur dynamique sur les états admissibles

**Énoncé (dans ton code : `TheoryStepFunctor`).**
Sous :

* `CnIdem`,
* `CnMonotone`,
* `ProvClosedCn : ∀ Γ, ProvClosed (Cn Γ)`,

on a un endofoncteur :

```
TheoryStepFunctor : ThState -> ThState
```

dont l’action sur objets est :

```
A ↦ FState(A), (FState(A)).Γ = Cn(A.Γ ∪ S1Rel(A.Γ))
```

**Interprétation.**
Tu ne fais pas “une itération ad hoc”, tu mets la dynamique dans un cadre catégorique propre : sur une catégorie mince, c’est l’équivalent exact de dire “c’est un opérateur monotone sur une classe d’états admissibles”.

---

### (T4) Loi de conservation “Missing = S1” (version dynamique)

**Énoncé (dans ton code : `missing_F0_eq_S1_of_absorbable`).**
Si `Γ` est `Absorbable` (i.e. `p ∈ Γ => Provable(Γ, p)`), alors :

```
MissingFrom(Γ, F0(Γ)) = S1Rel(Γ)
```

**Interprétation.**
Ce que le pas ajoute “au-delà de la prouvabilité de `Γ`” coïncide exactement avec la frontière définie par non-prouvabilité. C’est l’invariant structurel qui explique pourquoi la frontière est le bon objet à suivre : elle n’est pas décorative, elle mesure précisément le “défaut” résiduel.

---

### (T5) Croissance stricte sous témoin de frontière

**Énoncé (dans ton code : `strict_F_of_absorbable` / `strict_step_state`).**
Sous `Absorbable Γ` et l’existence d’un `FrontierWitness` à `Γ`, on obtient une extension stricte :

```
Γ ⊂ F(Γ)
```

**Interprétation.**
Si la théorie “absorbe” ce qu’elle prouve (aucun résidu interne), alors tout témoin de frontière force un vrai gain : la dynamique ne peut pas être stationnaire tant que la frontière est non vide.

---

### (T6) Théorème de “ω-collapse”

**Énoncé (dans ton code : `S1Rel_omegaΓ_eq_empty_of_absorbable_succ`).**
Sous :

* monotonie de `Provable`,
* `CnExtensive`,
* les hypothèses d’admissibilité (`CnIdem`, `ProvClosedCn`),
  et si le stade successeur `Γ₁` est `Absorbable`, alors la frontière au **ω-limite** est vide :
  
```
S1Rel(ωΓ) = ∅
```

**Interprétation.**
Phénomène limite essentiel : même si la frontière peut rester non vide à chaque stade fini, une condition d’absorption à un stade successeur suffit à forcer l’évaporation complète de la frontière à la limite `ω`. Cela met en évidence que “prendre l’union” + clôture n’est pas neutre : la dynamique possède un vrai comportement ordinal.

---

### (T7) Trilemme à ω

**Énoncé (dans ton code : `omega_trilemma` et `omega_trilemma_disjunction`).**
Si Route II impose que `S1Rel(ωΓ)` est non vide (ou plus généralement, si l’on suppose `RouteIIAt ωΓ`), alors on ne peut pas avoir simultanément l’absorption au stade 1 et la non-vacuité de la frontière au ω-limite. Forme typique :

```
¬ Absorbable(Γ₁) ∨ ¬ OmegaAdmissible(ωΓ) ∨ ¬ RouteIIAt(ωΓ)
```

**Interprétation.**
C’est la conséquence structurante : si tu exiges un principe “type Route II” (frontière jamais vide pour les états admissibles), alors l’absorption “trop forte” à un stade successeur ou l’admissibilité au ω-limite doivent casser. Ce genre de résultat n’existe pas dans une présentation statique : il dépend intrinsèquement de l’itération et des limites.
