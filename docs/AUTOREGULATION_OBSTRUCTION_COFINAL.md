# AutoRegulatedCofinal vs ObstructionCofinal (relation exacte)

Ce document fixe, sans ambiguïté, la relation logique entre les deux notions suivantes du fichier
`RevHalt/Theory/PrimitiveHolonomy.lean` :

- `AutoRegulatedCofinal`
- `ObstructionCofinal`

L’objectif est d’éliminer toute lecture “ET/OU” implicite au niveau du langage naturel, en mettant
les **quantificateurs** à nu et en indiquant ce qui est (ou n’est pas) déductible **constructivement**.

---

## 0) Cadre minimal (objets manipulés)

On fixe :

- un type `P` de “préfixes” et une instance `[HistoryGraph P]` (chemins `Path` + 2-cellules `Deformation`),
- une sémantique `sem : Semantics P S` vers un espace d’états `S`,
- une observation `obs : S → V` et une observation-cible `target_obs : P → V`,
- des fibres `FiberPt obs target_obs h` au-dessus des préfixes `h : P`.

Le “futur cofinal” (un “tail”) est capturé par `C : Set P` via `Cofinal C` : chaque préfixe se prolonge
vers un préfixe dans `C`.

---

## 1) Définitions Lean (verbatim, donc non contestables)

Les définitions suivantes sont celles du fichier `RevHalt/Theory/PrimitiveHolonomy.lean` (mêmes noms,
mêmes quantificateurs, même ordre).

### 1.1 Le “tail” cofinal et les cellules restreintes

```lean
def Reach (h k : P) : Prop :=
  Nonempty (HistoryGraph.Path h k)

def Cofinal (C : Set P) : Prop :=
  ∀ h : P, ∃ k : P, k ∈ C ∧ Reach h k

def CellsOver (C : Set P) : Set (Cell (P := P)) :=
  { c | CellSrc c ∈ C ∧ CellTgt c ∈ C }
```

### 1.2 Auto-régulation locale (sur un ensemble fixé `J`)

```lean
def AutoRegulated {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∃ φ : Gauge (P := P) obs target_obs,
    ∀ c, c ∈ J →
      let ⟨_h, _, _, _, ⟨α⟩⟩ := c
      ∀ x x',
        CorrectedHolonomy sem obs target_obs φ α x x' ↔ x = x'
```

Lecture brute (sans paraphrase) : il existe une **seule** jauge `φ` telle que, pour toute cellule `c ∈ J`,
la relation `CorrectedHolonomy ... φ α` est exactement la diagonale (`↔ x = x'`).

### 1.3 Obstruction locale (sur un ensemble fixé `J`, version positive à témoins)

```lean
def Obstruction {S : Type w} {V : Type w}
    (sem : Semantics P S) (obs : S → V) (target_obs : P → V)
    (J : Set (Cell (P := P))) : Prop :=
  ∀ φ : Gauge (P := P) obs target_obs,
    ∃ c, c ∈ J ∧
      let ⟨h, _, _, _, ⟨α⟩⟩ := c
      ∃ x x' : FiberPt (P := P) obs target_obs h,
        x ≠ x' ∧ CorrectedHolonomy sem obs target_obs φ α x x'
```

Lecture brute : pour **toute** jauge `φ`, on exhibe une cellule `c ∈ J`, puis on exhibe deux points distincts
`x ≠ x'` dans la fibre source, tels que la holonomie corrigée relie `x` à `x'` (donc “pas diagonale”).

### 1.4 Les versions “cofinales” (les deux portent sur `∃ C`)

```lean
def AutoRegulatedCofinal {S V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∃ C : Set P, Cofinal C ∧ AutoRegulated sem obs target_obs (CellsOver C)

def ObstructionCofinal {S : Type w} {V : Type w}
  (sem : Semantics P S) (obs : S → V) (target_obs : P → V) : Prop :=
  ∃ C : Set P, Cofinal C ∧ Obstruction sem obs target_obs (CellsOver C)
```

---

## 2) Mise en forme logique (quantificateurs explicites)

Ici on ne change **rien** au contenu, on ne fait que remplacer les notations par des schémas de quantificateurs.

### 2.1 Sur un ensemble fixé `J`

Auto-régulation :

```
AutoRegulated(J)  :=
  ∃ φ,  ∀ c, (c ∈ J → Diagonal(φ, c))
```

Obstruction :

```
Obstruction(J) :=
  ∀ φ,  ∃ c, (c ∈ J ∧ ∃ x x', x ≠ x' ∧ Twist(φ, c, x, x'))
```

Ici :
- `Diagonal(φ,c)` est exactement `∀ x x', CorrectedHolonomy ... φ α x x' ↔ x = x'` pour la cellule `c`.
- `Twist(φ,c,x,x')` est exactement `CorrectedHolonomy ... φ α x x'` avec la contrainte `x ≠ x'`.

### 2.2 Au niveau “cofinal”

Auto-régulation cofinale :

```
AutoRegulatedCofinal :=
  ∃ C, (Cofinal(C) ∧ AutoRegulated(CellsOver C))
```

Obstruction cofinale :

```
ObstructionCofinal :=
  ∃ C, (Cofinal(C) ∧ Obstruction(CellsOver C))
```

Point critique : les deux ont `∃ C` en tête. Le `C` n’est pas imposé a priori.

---

## 3) Relation stricte sur un même `J` (donc sur un même `C`)

### 3.1 Obstruction(J) implique non AutoRegulated(J)

C’est un théorème Lean déjà présent :

- `PrimitiveHolonomy.not_AutoRegulated_of_Obstruction`

Lecture :

```
Obstruction(J) → ¬ AutoRegulated(J)
```

### 3.2 AutoRegulated(J) implique non Obstruction(J)

C’est vrai **constructivement** (simple instanciation) :

```
AutoRegulated(J) → ¬ Obstruction(J)
```

Preuve (format “quantificateurs”, sans rhétorique) :

1) Supposons `AutoRegulated(J)`. Alors il existe `φ0` tel que `∀ c, c ∈ J → Diagonal(φ0,c)`.
2) Supposons `Obstruction(J)`. Alors en particulier, appliqué à `φ0`, on obtient un `c ∈ J` et des `x ≠ x'`
   tels que `Twist(φ0,c,x,x')`.
3) Mais `Diagonal(φ0,c)` donne `CorrectedHolonomy ... φ0 α x x' ↔ x = x'`. Donc `Twist` implique `x = x'`,
   contradiction avec `x ≠ x'`.

### 3.3 Conclusion sur un `J` fixé

Sur un même ensemble `J` :

- elles sont **incompatibles** (pas les deux à la fois),
- mais elles ne sont **pas** des compléments logiques : on n’a pas `Obstruction(J) ↔ ¬AutoRegulated(J)`.

Pourquoi pas complémentaires ? Parce que `Obstruction(J)` est une forme **positive** (“témoin pour chaque φ”),
alors que `¬AutoRegulated(J)` est une forme **négative** (“il n’existe pas de φ qui marche partout”).

Le point technique exact est :

- de `¬∃ φ, A(φ)` on déduit constructivement `∀ φ, ¬A(φ)`,
- mais de `¬∀ c, P(c)` on ne peut pas (en général) déduire `∃ c, ¬P(c)` sans principe classique.

Or `Obstruction(J)` contient précisément un schéma “`∃ c` témoin” (et même `∃ x x'`) pour chaque `φ`.

---

## 4) Relation au niveau cofinal : pas un OU exclusif (et pas d’implication globale)

### 4.1 Pourquoi `AutoRegulatedCofinal` et `ObstructionCofinal` peuvent coexister

Parce que :

- `AutoRegulatedCofinal` ne dit pas “pour tout futur cofinal”, il dit “il existe un futur cofinal `C_good`”.
- `ObstructionCofinal` ne dit pas “pour tout futur cofinal”, il dit “il existe un futur cofinal `C_bad`”.

Logiquement, on peut avoir :

- un `C_good` cofinal où une jauge uniforme existe,
- et un `C_bad` cofinal où toute jauge échoue avec témoin.

Donc au niveau “∃C”, ce n’est pas un XOR.

Exemple logique (100% standard) : sur `ℕ` avec `≤`, les ensembles `C_even = {n | n est pair}` et
`C_odd = {n | n est impair}` sont tous deux cofinaux. Donc on peut avoir une propriété vraie sur `C_even`
et une propriété incompatible vraie sur `C_odd`, et conclure simultanément `∃ C, Cofinal(C) ∧ Prop(C)`
et `∃ C, Cofinal(C) ∧ ¬Prop(C)`.

C’est exactement la situation des définitions cofinales actuelles : elles ne sélectionnent pas un “tail” unique.

### 4.2 Ce qu’on peut dire malgré tout (déductions exactes)

En utilisant `Obstruction(J) → ¬AutoRegulated(J)` :

```
ObstructionCofinal → ∃ C, Cofinal(C) ∧ ¬ AutoRegulated(CellsOver C)
```

et symétriquement :

```
AutoRegulatedCofinal → ∃ C, Cofinal(C) ∧ ¬ Obstruction(CellsOver C)
```

Ce sont des conséquences “propres” : elles disent qu’il existe un tail où l’un des deux comportements est forcé.

### 4.3 Ce qu’on ne peut pas dire (et pourquoi)

On ne peut pas déduire, en général :

```
ObstructionCofinal → ¬AutoRegulatedCofinal
AutoRegulatedCofinal → ¬ObstructionCofinal
```

Raison : les deux énoncés ont la forme `∃ C, ...` et les témoins `C` peuvent être différents.

---
## 5) Résumé (forme “théorèmes”)

- (Fixe `J`) `Obstruction(J) → ¬AutoRegulated(J)`.
- (Fixe `J`) `AutoRegulated(J) → ¬Obstruction(J)`.
- (Fixe `J`) pas d’équivalence constructive `Obstruction(J) ↔ ¬AutoRegulated(J)`.
- (Cofinal `∃C`) pas de dichotomie globale : `AutoRegulatedCofinal` et `ObstructionCofinal` peuvent coexister.
