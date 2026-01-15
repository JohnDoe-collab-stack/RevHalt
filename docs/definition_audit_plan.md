# Plan d'Audit Rigoureux — Définitions RevHalt

## Objectif

Vérifier que **chaque définition centrale** :

1. N'est pas vacuously true (satisfaite par tout)
2. N'est pas vacuously false (jamais satisfaite)
3. Correspond à l'intention mathématique déclarée
4. Est instanciable sur au moins un cas concret
5. Interagit correctement avec les autres définitions

---

# PHASE 1 — BASE

## 1.1 Fichier : `Base/Kit.lean`

### Définitions à auditer

| Nom | Type | Question critique |
|-----|------|-------------------|
| `RHKit` | structure | Quels champs ? Sont-ils tous nécessaires ? |
| `Rev0_K` | def/prop | Que signifie "halting certifié" ? Est-ce bien Σ₁ ? |
| `KitStabilizes` | def/prop | Capture-t-il vraiment non-halting ? |
| `DetectsUpFixed` | def/prop | Lien avec quotient `up` ? |

### Vérifications

- [ ] `Rev0_K` n'est pas toujours faux : ∃ trace t, Rev0_K K t = true
- [ ] `Rev0_K` n'est pas toujours vrai : ∃ trace t, Rev0_K K t = false
- [ ] `KitStabilizes` est le complément logique conceptuel de `Rev0_K`
- [ ] Les axiomes sur `RHKit` (si présents) sont satisfiables

### Instanciation requise

Montrer un exemple de `RHKit` concret (machines de Turing ?) où Rev0 et Stabilizes sont non-triviaux.

---

## 1.2 Fichier : `Base/Trace.lean`

### Définitions à auditer

| Nom | Type | Question critique |
|-----|------|-------------------|
| `Trace` | def | Qu'est-ce qu'une trace ? Séquence d'états ? |
| `Step` | def | Transition unitaire ? |
| `Stabilizes` | def/prop | Quand une trace "se stabilise" ? |
| `Halts` | def/prop (si présent) | Distinction avec Stabilizes ? |

### Vérifications

- [ ] `Trace` est un type non-vide
- [ ] `Stabilizes` est cohérent : si stabilise à n, reste stable pour m > n
- [ ] `Stabilizes` ⟺ existe un état final atteint ?

---

## 1.3 Fichier : `Base/QuotientUp.lean`

### Définitions à auditer

| Nom | Type | Question critique |
|-----|------|-------------------|
| `UpRel` | relation | Quelle équivalence ? |
| `UpQuot` | quotient | Quotient bien défini ? |
| `up` | fonction | Projection dans le quotient ? |

### Vérifications

- [ ] `UpRel` est réflexive, symétrique, transitive
- [ ] `up` est bien défini (indépendant du représentant)
- [ ] Lien avec `Stabilizes` : traces équivalentes ⟺ même comportement à l'infini ?

---

# PHASE 2 — THÉORIE FONDAMENTALE

## 2.1 Fichier : `Theory/Canonicity.lean`

### Définitions à auditer

| Nom | Question critique |
|-----|-------------------|
| `Canonical` | Qu'est-ce qu'un objet canonique ? Normalisation ? |
| Équivalences | Sont-elles bien des équivalences (réflexive, symétrique, transitive) ? |

### Vérifications

- [ ] `Canonical` n'est pas satisfait par tout objet
- [ ] Les propriétés canoniques sont préservées par les opérations du framework

---

## 2.2 Fichier : `Theory/Impossibility.lean`

### Définitions à auditer

| Nom | Question critique |
|-----|-------------------|
| `ImpossibleSystem` | structure | Quels axiomes ? Lesquels sont essentiels ? |
| `InternalHaltingPredicate` | structure | Qu'est-ce qui fait un prédicat "interne" ? |
| `T2_impossibility` | theorem | Hypothèses exactes ? |

### Vérifications

- [ ] `ImpossibleSystem` a au moins une instanciation (PA ? ZFC ?)
- [ ] `InternalHaltingPredicate` requiert des propriétés non-triviales
- [ ] `T2_impossibility` : lister TOUTES les hypothèses — sont-elles toutes utilisées ?
- [ ] Aucune hypothèse cachée (vérifier les `variable` en scope)

### Question critique

**T2 s'applique-t-il au cas général (toutes les machines) ou à des cas spécifiques ?**

---

## 2.3 Fichier : `Theory/Complementarity.lean`

### Définitions à auditer

| Nom | Question critique |
|-----|-------------------|
| `S1Rel` | Frontière positive (vrai ∧ non-prouvable) |
| `S2Rel` | Frontière négative ? |
| `S1Set` / `S2Set` | Versions ensemblistes |
| Anti-monotonie | `S1Rel_anti_monotone` bien formulé ? |

### Vérifications

- [ ] `S1Rel Γ` peut être non-vide (existe Γ, e tels que S1Rel Γ contient encode_halt e)
- [ ] `S1Rel Γ` peut être vide (existe Γ tel que S1Rel Γ = ∅)
- [ ] Anti-monotonie : Γ ⊆ Δ ⟹ S1Rel Δ ⊆ S1Rel Γ (formulé correctement ?)
- [ ] Lien S1Rel ↔ S1Set cohérent

---

## 2.4 Fichier : `Theory/Categorical.lean`

### Définitions à auditer

| Nom | Question critique |
|-----|-------------------|
| `ThObj` | Objets = théories ? États ? |
| `ThHom` | Morphismes = inclusions ? |
| `ThState` | Structure d'état (Cn-closed, ProvClosed) |
| Foncteurs | F bien défini sur morphismes ? |

### Vérifications

- [ ] `ThObj` forme une catégorie (identité, composition)
- [ ] `ThHom` préserve les propriétés structurelles
- [ ] Les foncteurs respectent map_id, map_comp

---

## 2.5 Fichier : `Theory/Stabilization.lean`

### Définitions à auditer

| Nom | Question critique |
|-----|-------------------|
| `Stabilizes` (si différent de Base) | Cohérent avec Base/Trace ? |
| Conditions de stabilisation | Quelles propriétés garantissent stabilisation ? |

### Vérifications

- [ ] Cohérence avec `Base/Trace.lean`
- [ ] Les théorèmes de stabilisation sont non-triviaux

---

# PHASE 3 — THEORYDYNAMICS

## 3.1 Fichier : `TheoryDynamics.lean` (CENTRAL)

### Définitions à auditer

| Nom | Question critique | Priorité |
|-----|-------------------|----------|
| `Provable` | Variable — quelle signature attendue ? | HAUTE |
| `S1Rel` | Identique à Complementarity ? | HAUTE |
| `F0` | Étape avant Cn | MOYENNE |
| `F` | F Γ = Cn(Γ ∪ S1Rel Γ) | HAUTE |
| `Absorbable` | p ∈ Γ ⟹ Provable Γ p | HAUTE |
| `ProvClosed` | Provable Γ p ⟹ p ∈ Γ | HAUTE |
| `OmegaAdmissible` | Cn-closed ∧ ProvClosed | HAUTE |
| `FrontierWitness` | Existence d'un témoin frontière | MOYENNE |
| `omega_trilemma` | Théorème central ω | HAUTE |

### Vérifications

- [ ] `Absorbable` : existe Γ absorbable (non trivial)
- [ ] `Absorbable` : existe Γ non-absorbable
- [ ] `OmegaAdmissible` : existe Γ admissible
- [ ] `OmegaAdmissible` : existe Γ non-admissible
- [ ] `omega_trilemma` : quelles sont les 3 branches exactes ?

---

## 3.2 Fichier : `TheoryDynamics_RouteII.lean`

### Définitions à auditer

| Nom | Question critique |
|-----|-------------------|
| `Soundness` | Provable Γ p ⟹ SProvable p |
| `NegativeComplete` | ¬Rev0 ⟹ S-prouvable(¬halt) |
| `RouteIIApplies` | Admissible ⟹ S1Rel ≠ ∅ |

### Vérifications

- [ ] `RouteIIApplies` dépend de T2_impossibility — le lien est-il explicite ?
- [ ] Soundness est-elle satisfiable pour PA ?
- [ ] NegativeComplete est-elle satisfiable ?

---

## 3.3 Fichier : `TheoryDynamics_Transfinite.lean` (CENTRAL)

### Définitions à auditer

| Nom | Question critique | Priorité |
|-----|-------------------|----------|
| `LimitOp` | Structure pour opérateurs limite | HAUTE |
| `LimitDecomp` | Décomposition (preuve que stages s'incluent) | HAUTE |
| `transIterL` | Itération transfinie paramétrée | HAUTE |
| `transIter` | Cas union | MOYENNE |
| `ContinuousAtL` | Continuité à la limite | HAUTE |
| `FixpointFromContinuity` | Contrat continuité → fixpoint | HAUTE |
| `LimitIncludesStages` | Γ_β ⊆ Γ_lim pour β < lim | HAUTE |
| `limit_collapse_schema_L` | Collapse générique | HAUTE |
| `structural_escape_transfinite_L` | Module A + B + C → False | HAUTE |
| `fork_law_False` / `fork_law_not_ContinuousAtL` | Fork Law | HAUTE |

### Vérifications

- [ ] `transIterL` bien fondée (Ordinal.limitRecOn) ?
- [ ] `LimitIncludesStages` prouvée pour `unionLimitOp`, `cnUnionLimitOp`, `jumpLimitOp`
- [ ] `fixpoint_implies_OmegaAdmissible` : hypothèses minimales ?
- [ ] `routeII_contradiction` : hypothèses minimales ?
- [ ] `fork_law_*` : lister les 7 hypothèses exactes, vérifier qu'aucune n'est inutilisée

---

## 3.4 Autres fichiers TheoryDynamics

| Fichier | Focus |
|---------|-------|
| `TheoryDynamics_Trajectory.lean` | `incarnation_trilemma`, cohérence avec Transfinite |
| `TheoryDynamics_Transfinite_Jump.lean` | `jumpLimitOp`, `not_JumpDiscontinuousAlong_frontier` |
| `TheoryDynamics_Transfinite_JumpFixpoint.lean` | `no_fixpoint_at_limit` |
| `TheoryDynamics_TwoSided.lean` | Extension, moins critique |

---

# PHASE 4 — VÉRIFICATION CROISÉE

## 4.1 Cohérence inter-fichiers

- [ ] `S1Rel` dans Complementarity = `S1Rel` dans TheoryDynamics ?
- [ ] `Rev0_K` (Base) utilisé correctement dans `S1Rel` (Theory) ?
- [ ] `Stabilizes` (Base) cohérent avec concepts dynamiques ?

## 4.2 Chaîne de dépendances

```
Base/Kit + Base/Trace
    ↓
Complementarity (S1Rel)
    ↓
Impossibility (T2)
    ↓
TheoryDynamics (F, Absorbable, OmegaAdmissible)
    ↓
TheoryDynamics_RouteII (RouteIIApplies)
    ↓
TheoryDynamics_Transfinite (Fork Law)
```

Vérifier que chaque flèche est justifiée par des imports et des utilisations réelles.

## 4.3 Hypothèses non-déclarées

Pour chaque théorème central, lister :

- Variables en scope (`variable` statements)
- Instances implicites
- Axiomes utilisés (#check @nom_theorem)

---

# PHASE 5 — INSTANCIATION CONCRÈTE

## 5.1 Cas test : Machines de Turing

- [ ] Définir `RHKit` pour Turing machines
- [ ] Montrer `Rev0_K` = "halte effectivement"
- [ ] Montrer `S1Rel` non-vide pour PA
- [ ] Montrer `Absorbable` atteignable (exemple trivial)

## 5.2 Cas test : Langage NP spécifique (optionnel)

- [ ] Instancier sur SAT ou équivalent
- [ ] Vérifier Route II / Collapse

---

# LIVRABLES

1. **Rapport par fichier** : pour chaque fichier, liste des définitions avec statut (OK / Suspect / À revoir)
2. **Graphe de dépendances** : visualisation des liens entre définitions
3. **Liste des hypothèses** : pour chaque théorème central, liste exhaustive
4. **Instanciation témoin** : au moins un cas concret compilant

---

# EXÉCUTION

Pour chaque fichier, je vais :

1. Lire le fichier complet
2. Extraire chaque définition avec son corps
3. Vérifier les critères listés
4. Documenter dans le rapport
