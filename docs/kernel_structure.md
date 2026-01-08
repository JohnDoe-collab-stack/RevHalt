# RevHalt : Structure des Noyaux

## La Big Picture

### Phrase-guide

> **RevHalt est un principe de conservation de l'incomplétude** dérivé d'une géométrie de clôture finitaire : *dès qu'un détecteur exact mesure le noyau (Pi1) à partir du signal (Sigma1), la globalisation interne est interdite et une frontière est forcée*.

### Le schéma universel

Ce n'est pas spécifique à Collatz, ni même à la calculabilité stricte. Le pattern se déclenche dès que :

1. **Approximation finitaire** (Scott/dirigée)
2. **Clôture monotone** (opérateur `up`)
3. **Couche interne r.e.** qui tente de totaliser la décision

→ **Obstruction de globalisation** → **Frontière forcée**

### Ce qui est stable

Pas S1. Pas le noyau. C'est **l'obstruction elle-même** : l'impossibilité de globaliser la détection du noyau.

### Le triptyque

| Plan | Contenu |
|------|---------|
| **Syntaxe** | Ce que le système peut prouver |
| **Sémantique** | Vérité externe |
| **Valuation** | Opérateur up, accès finitaire (Sigma1 = ouvert, Pi1 = fermé) |

L'invariant dépend du **type d'accès** (finitaire/monotone), pas du contenu.

### La hiérarchie comme compilateur

La hiérarchie (Splitter → Up2 → Up1) n'est pas un gadget. C'est l'interface qui transporte des preuves locales structurées vers des invariants globaux Pi1.

---

## Introduction technique

RevHalt définit la stabilisation (non-arrêt) non pas comme une simple négation logique, mais comme une **appartenance à un noyau algébrique**. Cette caractérisation opérative est la contribution fondamentale du projet.

---

## Qu'est-ce qu'un noyau ?

### Définition

Le **noyau** d'un opérateur f est l'ensemble des éléments "annihilés" par cet opérateur :

```
Ker(f) = { x | f(x) = 0 }
```

Dans RevHalt, `Ker(up) = { T | up T = bot }` — les traces envoyées sur "faux partout".

### Pourquoi un noyau ?

1. **Du logique à l'algébrique** : Au lieu de "forall n, not T n" (assertion infinie), on dit "T in Ker(up)" (appartenance structurelle).

2. **Opérativité** : L'opérateur `up` peut être appliqué pour détecter l'appartenance. Ce n'est plus une assertion, c'est une mesure.

3. **Hiérarchie** : Avec deux noyaux (Avoid2Set, Ker(up)), on peut construire des inclusions : Queue → Avoid2Set → Ker(up).

4. **Explication de l'incomplétude** : Le Kit détecte le noyau, mais le système formel ne peut pas l'internaliser. D'où la frontière S1 non-vide.

---

## Niveau Up1 : Noyau Temporel

### Définition

```
Ker(up) = { T | up T = bot }
```

Où `up T n = exists m >= n, T m` ("éventuellement vrai à partir de n").

### Théorème clé

```
Stabilizes T  <->  up T = bot  <->  T in Ker(up)
```

- **Fichier**: `Theory/Categorical.lean`, lignes 119-136
- **Théorème**: `up_eq_bot_iff`

### Signification

L'opérateur `up` agit comme un **projecteur/filtre** :
- Si T contient un signal (Halts) : `up T != bot`
- Si T est du bruit pur (Stabilizes) : `up T = bot`

La stabilisation devient une **nullité structurelle** détectée par l'opérateur, pas une simple négation.

### Propriétés de `up` comme projecteur

1. **Idempotence** : `up (up T) = up T`
2. **Conservation du signal** : `(exists n, up T n) <-> (exists n, T n)`
3. **Annihilation du bruit** : `up T = bot <-> forall n, not T n`

### Nature Purement Ordre-Théorique de Up

L'opérateur `up` et la notion de stabilisation ne dépendent pas de l'arithmétique de Peano. Ils reposent uniquement sur la structure d'ordre (préordre) `(Time, ≤)`.

1. **Indépendance de Peano** : `up T i` signifie `∃ j (i ∝ j) ∧ T j`. Cela ne requiert pas l'addition ou l'induction de Peano, seulement un préordre.
2. **Variantes** :
   - **upFut (Futur/Suffixe)** : `∃ j ≥ i, T j` (Antitone). C'est la stabilisation classique (`Stabilizes`).
   - **upPast (Passé/Préfixe)** : `∃ j ≤ i, T j` (Monotone). C'est une accumulation d'historique.

Tout cela est purement **ordre-théorique**.

---

## Niveau Up2 : Noyau Structurel

### Définition

```
Avoid2Set(G, S) = { p | exists X, AvoidClosed(G, S, X) and p in X }
```

C'est le **plus grand post-fixe** (gfp) de `AvoidStep`.

### Dualité lfp/gfp

| Ensemble | Type | Définition | Signification |
|----------|------|------------|---------------|
| `Up2Set` | lfp | Intersection des ensembles Up2-clos | Région gagnante pour P |
| `Avoid2Set` | gfp | Union des post-fixes de AvoidStep | Région de sécurité pour O |

### Théorème clé

```
kernel_iff_of_DetOpen2 :
  p in Avoid2Set(G, S)  <->  not Up2Mem(G, S, p)
```

- **Fichier**: `Theory/Up2.lean`, lignes 530-537
- **Condition**: Sous `DetOpen2` (déterminisme ouvert structurel)

### Signification

`Avoid2Set` est le noyau de Up2 au sens où il capture exactement les positions qui ne sont **pas** dans la région gagnante. C'est une caractérisation **coinductive** : appartenir au noyau signifie pouvoir exhiber un témoin de fermeture.

---

## Niveau Splitter : Noyau Arithmétique

### Définition

```
Queue(Pos, Next, S, d, I0, n) =
  Sat(I0, n) and forall t, ResEquiv(S, d, I0, n, iterate(Next, t, n))
```

Un point `n` est dans la Queue si :
1. Il satisfait l'état d'information initial
2. Toute son orbite reste dans la même classe de résidu

### Théorème clé

```
queue_splitter_subset_avoid2 :
  Queue(n)  ->  embed(n) in Avoid2Set(G, Target)
```

- **Fichier**: `Theory/Splitter/AvoidanceBridge.lean`, lignes 17-71

### Signification

La Queue est un **certificat arithmétique fini** qui implique l'appartenance au noyau Up2. C'est la passerelle entre structure arithmétique et sécurité structurelle.

---

## Le Kit comme Détecteur de Noyau

### Le théorème central

```
KitStabilizes_iff_up_eq_bot :
  KitStabilizes K T  <->  up T = bot
```

- **Fichier**: `Theory/Stabilization.lean`, lignes 70-73
- **Condition**: Le Kit doit être valide (`DetectsMonotone K`)

### La chaîne complète des équivalences

```
not Rev0_K K T  <->  not Halts T  <->  Stabilizes T  <->  up T = bot
(observationnel)     (Sigma-1)        (Pi-1)            (algébrique)
```

### Signification

Le Kit n'est pas juste un "test" arbitraire. C'est un **instrument de mesure algébrique** :
- Son verdict négatif (`KitStabilizes`) équivaut exactement à l'appartenance au noyau
- Il détecte la **nullité structurelle** de la trace

### Propriété constructive

Le théorème `Stabilizes_up_iff` est prouvé **sans axiomes classiques** :
```
Stabilizes (up T)  <->  Stabilizes T
```

Cela signifie que l'opérateur `up` préserve la stabilisation de manière constructive.

---

## Up2Kit : Détecteur de Noyau Structurel

Le même pattern de Kit-détecteur existe pour Up2.

### Structure

```
structure Up2Kit (G : Game) where
  eval : Set G.Pos -> G.Pos -> Bool
```

- **`WinK K S p`** : Le Kit dit "P gagne depuis p"
- **`AvoidK K S p`** : Le Kit dit "O peut éviter depuis p"

### Validité

```
DetectsWin K = KitSound K and KitComplete K
```

Parallèle exact à `DetectsMonotone` pour RHKit.

### Théorèmes T1 pour Up2

```
T1_Up2 :           WinK K S p    <->  Up2Mem G S p
T1_Avoid_neg :     AvoidK K S p  <->  not Up2Mem G S p
T1_Avoid2 :        AvoidK K S p  <->  Avoid2Mem G S p  (sous DetOpen2)
```

- **Fichier**: `Theory/Up2.lean`, lignes 356-574

### Kernel Detector Theorem pour Up2

```
AvoidK_iff_not_in_Up2Set :
  AvoidK K S p  <->  p not in Up2Set G S
```

Le Kit Up2 détecte l'appartenance au noyau `Avoid2Set` exactement comme le Kit Up1 détecte l'appartenance à `Ker(up)`.

### Parallélisme complet

| Up1 | Up2 |
|-----|-----|
| `RHKit` | `Up2Kit` |
| `DetectsMonotone` | `DetectsWin` |
| `Rev0_K <-> Halts` | `WinK <-> Up2Mem` |
| `KitStabilizes <-> Stabilizes` | `AvoidK <-> not Up2Mem` |
| `KitStabilizes <-> up T = bot` | `AvoidK <-> p not in Up2Set` |

---

## La Chaîne des Noyaux

```
Queue  -->  Avoid2Set  -->  Ker(up)
(arithmétique)  (structurel)  (temporel)
```

### Implications formalisées

1. **Splitter -> Up2** : `splitter_implies_avoid2` (Hierarchy.lean:93)
2. **Up2 -> Up1** : `up2_implies_up1_pointwise` (Hierarchy.lean:73)
3. **Chaîne complète** : `hierarchy_chain` (Hierarchy.lean:113)

### Les trois formes du verdict final

| Forme | Énoncé | Fichier |
|-------|--------|---------|
| Logique | `Stabilizes (TimeTrace emb)` | `stabilization_chain_up1` |
| Opérative | `up (TimeTrace emb) = bot` | `stabilization_chain_up1_upEqBot` |
| Catégorique | `TimeTrace emb in upKernel` | `stabilization_chain_up1_mem_upKernel` |

---

## Contribution Fondamentale

### L'insight central

Ce n'est pas "le noyau existe".

C'est : **la détection du noyau (Kit) force une frontière S1 non absorbable par S2**.

### Le mécanisme

1. Le Kit **détecte** l'appartenance au noyau (`Rev0_K` détecte `Ker(up)`)
2. Cette détection **crée** une frontière :
   ```
   S1 = { p | Kit-certified and not Provable }
   ```
3. S1 != vide est une **nécessité structurelle** (théorème `frontier_necessary`)
4. S1 **ne peut pas être absorbée** par S2 — sinon on aurait un `InternalHaltingPredicate`

### Explication structurelle de l'incomplétude

| Propriété | Statut |
|-----------|--------|
| Le noyau Ker(up) | **existe** |
| Le Kit | **détecte** l'appartenance au noyau |
| Le système formel S2 | **ne peut pas internaliser** cette détection pour tous les codes |

Cette asymétrie (détectable mais non-internalisable) **force** l'existence de S1 != vide.

### Différence avec Gödel

- **Gödel** : l'incomplétude vient de l'auto-référence
- **RevHalt** : l'incomplétude vient de l'asymétrie détection/internalisation du noyau

### La frontière comme point de stabilité

La frontière S1 **est** l'incomplétude. Mais au lieu de la voir comme une limitation, RevHalt l'utilise comme **point de stabilité** :

| Propriété de S1 | Signification |
|-----------------|---------------|
| **Forcée** | `frontier_necessary` garantit S1 != vide |
| **Stable** | Cette non-vacuité est une nécessité structurelle |
| **Utilisable** | On construit S3 = S2 ∪ S1 en s'appuyant sur cette stabilité |

C'est un renversement de perspective :
- **Gödel** : l'incomplétude est une limitation ("il existe des vérités non prouvables")
- **RevHalt** : l'incomplétude est un point fixe stable sur lequel on peut **construire**

### Conséquence pratique

Un certificat fini (Queue) induit une preuve formelle de non-terminaison via la chaîne des noyaux. C'est un **compilateur de certificats** : structure finie -> garantie infinie.

---

## Références

- `RevHalt/Theory/Categorical.lean` : Noyau Up1, opérateur de clôture
- `RevHalt/Theory/Up2.lean` : Noyau Up2, dualité lfp/gfp
- `RevHalt/Theory/Splitter/Core.lean` : Queue, équivalence résiduelle
- `RevHalt/Theory/Splitter/AvoidanceBridge.lean` : Pont Queue -> Avoid2Set
- `RevHalt/Theory/Hierarchy.lean` : Chaîne unifiée des noyaux
