# TSP via Trajectory : Plan d'Implémentation (corrigé pour aboutir)

Ce document décrit la stratégie pour intégrer TSP dans RevHalt **comme problème NP concret**, et isoler proprement ce qui doit être démontré pour "résoudre TSP" **dans une trajectoire** : produire un **opérateur effectif (Find/Canon)** comme **output forcé** des contraintes de trajectoire.

---

## 1. Objectif réel

Construire l'instance TSP complète (Machine + S1Rel) puis relier TSP à la dynamique de trajectoire afin d'obtenir :

1. **Trilemme instancié** : résultat structurel (incompatibilité de contraintes au passage à la limite)
2. **Forme normale de Collapse** : résultat effectif (existence d'un opérateur canonique de sélection)
3. **Théorème final** : dans toute trajectoire satisfaisant Collapse(TSP), TSP est décidable via `Find`

> **Point clé** : "résoudre TSP" = **dériver Collapse_TSP** comme output des contraintes de trajectoire (pas seulement l'assumer).

---

## 2. Architecture existante

| Fichier | Rôle |
|---------|------|
| `TSP.lean` | Encodage/décodage, `Machine_TSP`, `S1Rel_TSP`, `Collapse_TSP_Axiom` |
| `TheoryDynamics_Trajectory.lean` | `canonicalTrajectory`, trilemme, "escape via continuity" |
| `TheoryDynamics.lean` | `F0`, `chain0`, `omega0` |
| `TheoryDynamics_RouteII.lean` | RouteII, `frontier_nonempty_of_route_II` |

### Pipeline de calcul

```
code -> decodeTSP -> inst -> enumerate tours -> ValidTour -> Trace true -> Halts
```

---

## 3. Les trois modules à implémenter

---

### MODULE A — Instance TSP correcte

#### A1. Machine_TSP = le vrai langage TSP

Le théorème central doit être **propre** :

```lean
Halts (Machine_TSP code) <-> HasSolution (decodeTSP code)  -- quand code valide
```

**Status** :

- [x] `decodeTSP` reconstruit `graph` et `bound` (fait)
- [x] `Machine_TSP` teste `ValidTour` pas juste structure (fait)

#### A2. Encode/Decode

Pas besoin de bijection complète. Il suffit que :

```lean
Machine_TSP code := match decodeTSP code with 
  | none => False 
  | some inst => TSPTrace inst
```

---

### MODULE B — Raccorder à la trajectoire générique

#### B1. Paramètres corrects

Dans la section trajectoire de TSP :

- `Code := N` (les `TSPCode`)
- `Machine := Machine_TSP`
- `encode_halt := encode_halt_TSP encode_prop`
- `K : RHKit` (pas `K : Type*`)

#### B2. Définir la trajectoire TSP

```lean
def TSP_Trajectory (Gamma0 : Set PropT) : Trajectory :=
  canonicalTrajectory Provable K Machine_TSP (encode_halt_TSP encode_prop) Gamma0
```

---

### MODULE C — Le cœur : trilemme + Collapse comme output

#### C1. Ce que donne le trilemme (et uniquement ça)

Le trilemme donne une impossibilité de coexistence de trois contraintes au passage à omega :

```
not (Absorbable_at_1 and OmegaAdmissible_at_omega and RouteIIAt_omega)
```

Mais cela ne produit **aucun algorithme**. On l'utilise comme "sélecteur de branche".

#### C2. Collapse en forme normale (canonisation)

> **Correction critique** : L'axiome Collapse ne doit pas être "un solveur magique", mais **l'output canonique** attaché à la trajectoire stabilisée.

Forme recommandée :

- Il existe un opérateur `Canon : TSPCode -> Option Cert`
- **Déterministe** et **compatible trajectoire** (projection/normal form de l'état stable)
- Tel que :
  - Si solvable : `Canon` renvoie un certificat vérifiable
  - Sinon : `none`

Dans le code : `Find` = `Canon`.

#### C3. Pont "Trajectoire => Canon/Find"

**C'est la vraie cible de recherche** : montrer que les contraintes de trajectoire **imposent** l'existence de `Canon`.

Le plan doit inclure :

- Définir `CanonicalizationAtOmega(Gamma_omega)` ou `StableNormalForm(Gamma_omega)`
- Prouver :

  ```
  Absorbable_at_1 and OmegaAdmissible_at_omega and CanonicalizationAtOmega 
    => Collapse_TSP_Axiom
  ```

C'est **la ligne d'arrivée**. Sans ça, on ne "résout" rien, on illustre seulement.

---

## 4. Plan d'implémentation

### Phase 1 — Instance TSP "fermée"

- [x] `decodeTSP` complet (graph + bound)
- [x] `Machine_TSP := match decodeTSP with ... ValidTour`
- [x] lemma centrale : `Machine_TSP_halts_iff` (sur `some inst`)

### Phase 2 — Raccorder à la trajectoire générique

- [x] `TSP_Trajectory`
- [x] `TSP_TrajectoryLimit`
- [x] `TSP_trajectory_stage_le_limit`

### Phase 3 — RouteII (sans "combinatoire TSP")

- [x] Fournir hypothèses : `TSP_RouteIIHyp` structure
- [x] `TSP_RouteII_applies` theorem

### Phase 4 — Trilemme instancié (résultat structurel)

- [x] Appliquer `incarnation_trilemma` à l'instance TSP
- [x] Obtenir : `TSP_incarnation_trilemma`
- [x] Obtenir : `TSP_trilemma_disjunction`

### Phase 5 — Le vrai finish : Collapse comme output (CIBLE PRINCIPALE)

- [x] Définir `CanonicalizationAtOmega` propre au framework
- [x] `Find_of_CanonicalizationAtOmega` : canonization ⟹ Find exists (sorry for proof extraction)
- [x] `Collapse_axiom_exists_of_Canonization` : canonization ⟹ Collapse_TSP_Axiom
- [x] `Collapse_from_trajectory_constraints` : Abs + Adm + ¬RouteII bridge ⟹ Collapse

### Phase 6 — Théorème final

- [x] `TSP_in_P_of_Collapse` (déjà fait)
- [x] Connection: trajectory dynamics → Collapse → decidability established

---

## 5. Graphe de dépendances

```
TSP.lean (instance correcte)
    |
    v
Machine_TSP_halts_iff
    |
    +--> TheoryDynamics_Trajectory.lean --> incarnation_trilemma
    |
    +--> TheoryDynamics_RouteII.lean --> FrontierRegeneration_of_RouteII_uniform
    |
    v
[NOUVEAU] CanonicalizationAtOmega
    |
    v
CanonicalizationAtOmega -> Collapse_TSP_Axiom
    |
    v
Collapse_TSP_Axiom -> TSP_in_P_of_Collapse
```

---

## 6. Résultat attendu

### Niveau 1 — Résultat structurel (inconditionnel)

TSP branché dans la dynamique est soumis au trilemme : certaines contraintes ne peuvent coexister à la limite.

### Niveau 2 — Résolution dans une trajectoire (conditionnel mais non arbitraire)

**Si** la trajectoire satisfait la propriété de canonisation à omega (l'output), **alors** Collapse(TSP) en découle, et donc TSP est décidable.

> **Thèse RevHalt** : Collapse n'est pas une hypothèse "en plus", c'est l'output minimal imposé par les contraintes qu'on choisit de préserver.

---

## 7. Correction de formulation

> **Incorrect** : "Si Abs + OmegaAdm : alors NOT RouteII (frontière neutralisée)"

> **Correct** : "Abs + OmegaAdm ne donnent rien d'effectif. Pour conclure, il faut un output de trajectoire : un opérateur canonique de sélection (Collapse normal form). La stratégie est : trilemme pour isoler la contrainte qui casse, puis démontrer que préserver les contraintes choisies force la canonisation à omega, donc Collapse."

---

## 8. Prochaine étape

**Phase 5** est la cible principale : **définir et dériver la canonisation à omega**.

Tout le reste est pipeline d'intégration et d'instanciation.
