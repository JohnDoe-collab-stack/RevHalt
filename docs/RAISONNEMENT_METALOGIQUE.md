Résumé — Unicité de l’arrêt sous géométrie d’observation (principe Rev)

Nous considérons les exécutions comme des traces T : ℕ → Prop et introduisons une géométrie d’observation via un opérateur de clôture up : Trace → Trace, défini par up T n := ∃ k ≤ n, T k. Les traces canoniques (ou closes) sont les points fixes de up, et l’équivalence d’observation est donnée par UpEqv T T' := ∀ n, up T n ↔ up T' n. Un Kit K est un observateur K.Proj : Trace → Prop dont on ne requiert la correction que localement, sur les seules traces canoniques : pour toute trace close S, K.Proj S ↔ ∃ n, S n.

La contribution centrale n’est pas la clôture en elle-même, mais le principe d’unicité qu’elle induit dès qu’on impose une discipline d’observation : parmi les prédicats globaux P : Trace → Prop qui (i) sont invariants par UpEqv (ne distinguent que ce que up distingue) et (ii) coïncident avec l’existence sur les traces closes, il existe un unique candidat. Ce candidat est extensionnellement l’arrêt standard Halts. L’opérateur Rev(K, T) := K.Proj (up T) réalise alors le mécanisme canonique d’extension : à partir d’un observateur seulement spécifié sur les canoniques, Rev fabrique le seul verdict global compatible avec la géométrie d’observation. Ainsi, Rev ne décide pas l’arrêt ; il le capture en le rendant inévitable dès que l’on fixe ce que l’observation a le droit de distinguer.

# Raisonnement metalogique (clarifie, autocontenu, et reference)

Ce document synthétise le raisonnement **metalogique** et son **raccord Lean**.
Il est **autocontenu** (definitions et enchainement sont rappeles ici),
et il donne les **references exactes** dans le code Lean pour verification.

Objectif global :
Montrer que la dynamique formelle impose l'extinction d'une corne du trilemme,
puis propager cette extinction le long d'une sous-suite cofinale,
et conclure l'extinction generique sous hypotheses assemblees.

---

## Vocabulaire minimal (glossaire)

- **Absorbable(Γ)** : toute formule appartenant a Γ est provable depuis Γ.  
  (Fermeture "membre -> provable")

- **OmegaAdmissible(Γ)** : Γ est stable par Cn et ProvClosed.  
  (Fermeture deductive + "provable -> membre")

- **RouteIIAt(Γ)** : la condition "Route II" est satisfaite a Γ.

- **A(n), B(n), C(n)** : instanciations de ces trois proprietes
  sur `chainState n` et `omegaΓ` (voir section 1).

- **Cornes du trilemme** : les trois couples (A,B,C) et leurs negations.

- **Cofinalite** : une propriete P se realise "infiniment souvent"
  de facon cofinale (pour tout N, il existe un indice >= N qui satisfait P).

---

## Vue d'ensemble (chaine logique)

1) **Trilemme local** : A(n) ∧ B(n) ∧ C(n) est impossible.  
2) **Sous-suite cofinale** : on force la negation de la corne manquante
   selon le mode (BC/AC/AB) le long d'une sous-suite `times`.
3) **PA dynamique** : PA_at revient cofinalement le long des visites.
4) **Extinction generique** : PA + Bridge ⇒ C(t), mais corne AB ⇒ ¬C(t) : contradiction.
5) **Couche metalogique** : l'escape transfinite force qu'une corne tombe
   (collapse vs Route II), donc le trilemme s'active.

---

## Raisonnement detaille (pas a pas, sans sauts)

Ce bloc explicite l'enchainement **exact** des lemmes du code.

**Etape 1 — Definir les cornes A/B/C.**  
Les definitions `A`, `B`, `C` codent Absorbable, OmegaAdmissible et RouteIIAt
au pas `n` (section 1). Cela fixe le vocabulaire unique des cornes.

**Etape 2 — Trilemme local.**  
Le lemme `trilemma_not_all_at_step` interdit A(n) ∧ B(n) ∧ C(n) au meme pas.
Les trois lemmes derives donnent la negation de la corne manquante a partir
des deux autres (section 2).

**Etape 3 — Couplage par mode.**  
`Pair` (BC/AC/AB) encode exactement "deux cornes vraies".  
Donc "Pair au pas n" + trilemme local ⇒ "corne manquante fausse" au pas n.

**Etape 4 — Sous-suite `times`.**  
`times` produit une sous-suite d'indices `n = times k` telle que
`Pair (sigma k)` est vrai a `n` (via `times_spec`).  
C'est la cle qui transporte la logique du trilemme vers une suite cofinale.

**Etape 5 — Forcage de cornes.**  
`strict_subseq_horns` combine Etapes 2–4 :  
au temps `times k`, la corne manquante est niee en fonction du mode `sigma k`.

**Etape 6 — Cofinalite des negations.**  
Si chaque mode apparait cofinalement (hypothese `SigmaCofinal`),
alors les negations correspondantes apparaissent cofinalement le long de `times`
(`cofinal_hornBC/AC/AB_along_times`).

**Etape 7 — PA dynamique.**  
`PA_at` est definie sur `chainState n`.  
`PairPA` ajoute PA aux couples de cornes, et `toSimpleWitness`
permet d'utiliser la meme sous-suite `times`.  
`cofinalPA_on_mode` assure que PA revient cofinalement sur chaque mode.

**Etape 8 — Monotonie de PA.**  
Dans `GenericExtinction`, `chainState_mono` ⇒ `PA_at_mono` ⇒
`PA_Eventually_of_exists`: si PA apparait a un temps, elle persiste
a tous les temps ulterieurs.

**Etape 9 — Contradiction finale.**  
Pour un `k` tel que `sigma k = AB`, on pose `t = times k`.  
Alors :

- par Etape 8, `PA_at t`;
- par le **bridge**, `RouteIIAt` a `t`;
- par Etape 5 (mode AB), `¬ RouteIIAt` a `t`.  
Contradiction, donc **EventuallyNotAB**.

**Etape 10 — Raccord metalogique.**  
La couche transfinie (`TheoryDynamics_Transfinite.lean`) donne un
schema de **contradiction structurelle** entre :

- `Absorbable` (A),  
- `OmegaAdmissible` (B),  
- `RouteIIAt` (C).  
C'est exactement le trilemme encode par A/B/C.  
Ainsi, la couche metalogique **alimente** le trilemme local, et
la chaine Etapes 1–9 propage cette contrainte vers l'extinction generique.

---

## 1) Les cornes du trilemme (A/B/C) – definitions et sens

Dans `RevHalt/Trilemma/CofinalHornsSimple.lean`, on fixe :

- **A(n)** = `Absorbable` au pas `n+1`  
  -> `RevHalt/Trilemma/CofinalHornsSimple.lean:21`
- **B(n)** = `OmegaAdmissible` sur `omegaΓ` de `chainState n`  
  -> `RevHalt/Trilemma/CofinalHornsSimple.lean:25`
- **C(n)** = `RouteIIAt` sur le même `omegaΓ`  
  -> `RevHalt/Trilemma/CofinalHornsSimple.lean:30`

Le **couplage** par mode est donné par `Pair` (BC, AC, AB) :  
`RevHalt/Trilemma/CofinalHornsSimple.lean:48`.

---

## 2) Trilemme local (impossibilité A ∧ B ∧ C au même pas)

Le trilemme est formulé au niveau d’un pas `n` :

- `trilemma_not_all_at_step`  
  -> `RevHalt/Trilemma/Trilemma.lean:88`

Lemmes dérivés (négation d’une corne à partir des deux autres) :

- `absorbable_step_and_omegaAdmissible_omega_implies_not_routeIIAt_omega`  
  -> `RevHalt/Trilemma/Trilemma.lean:108`
- `absorbable_step_and_routeIIAt_omega_implies_not_omegaAdmissible_omega`  
  -> `RevHalt/Trilemma/Trilemma.lean:127`
- `omegaAdmissible_omega_and_routeIIAt_omega_implies_not_absorbable_step`  
  -> `RevHalt/Trilemma/Trilemma.lean:146`

---

## 3) Cofinalité des cornes (sous-suite times)

Toujours dans `CofinalHornsSimple.lean` :

- `CofinalWitness` : `RevHalt/Trilemma/CofinalHornsSimple.lean:74`
- `times` (sous-suite guidée par témoins) :  
  `RevHalt/Trilemma/CofinalHornsSimple.lean:78`

**Forçage des cornes** sur la sous-suite :

- `strict_subseq_horns`  
  -> `RevHalt/Trilemma/CofinalHornsSimple.lean:166`

**Cofinalité** des cornes forcées :

- `cofinal_hornBC_along_times`  
  -> `RevHalt/Trilemma/CofinalHornsSimple.lean:335`
- `cofinal_hornAC_along_times`  
  -> `RevHalt/Trilemma/CofinalHornsSimple.lean:400`
- `cofinal_hornAB_along_times`  
  -> `RevHalt/Trilemma/CofinalHornsSimple.lean:461`

Interpretation :

- mode **BC** ⇒ ¬A apparaît cofinalement,
- mode **AC** ⇒ ¬B apparaît cofinalement,
- mode **AB** ⇒ ¬C apparaît cofinalement.

---

## 4) PA dynamique (PA_at et sa cofinalite)

Dans `RevHalt/Trilemma/CofinalHornsPA.lean` :

- `PA_in`, `PA_at`  
  -> `RevHalt/Trilemma/CofinalHornsPA.lean:21`, `:25`
- `PairPA` : couple `Pair` + `PA_at`  
  -> `RevHalt/Trilemma/CofinalHornsPA.lean:29`
- `toSimpleWitness` : conversion PairPA -> Pair  
  -> `RevHalt/Trilemma/CofinalHornsPA.lean:38`
- `CofinalPA_on_visits`  
  -> `RevHalt/Trilemma/CofinalHornsPA.lean:67`
- `cofinalPA_on_mode`  
  -> `RevHalt/Trilemma/CofinalHornsPA.lean:88`
- `dynamic_trilemma_with_PA_Strong_final`  
  -> `RevHalt/Trilemma/CofinalHornsPA.lean:147`

Ce bloc garantit : **sur chaque mode**, `PA_at` revient cofinalement.

---

## 5) Extinction generique (logique finale)

Dans `RevHalt/Trilemma/GenericExtinction.lean` :

- `PA_implies_RouteIIAt`  
  -> `RevHalt/Trilemma/GenericExtinction.lean:25`
- `EventuallyNotAB`  
  -> `RevHalt/Trilemma/GenericExtinction.lean:46`
- `CollatzInstance` (bundle des hypothèses)  
  -> `RevHalt/Trilemma/GenericExtinction.lean:54`
- `chainState_mono`, `PA_at_mono`, `PA_Eventually_of_exists`  
  -> `RevHalt/Trilemma/GenericExtinction.lean:95`, `:110`, `:119`
- `eventuallyNotAB_of_instance`  
  -> `RevHalt/Trilemma/GenericExtinction.lean:133`

**Mecanisme formel** :

1) `PA_at` devient **persistant** (monotonie) à partir d’un `t0`.
2) `times` donne un `t` cofinal, avec `N ≤ t`.
3) Le **bridge** donne `RouteIIAt` au même `t`.
4) `strict_subseq_horns` donne `¬ RouteIIAt` au même `t` si mode AB.
5) Contradiction ⇒ `EventuallyNotAB`.

---

## 6) Escape / Collapse transfinis (couche metalogique)

Dans `RevHalt/Theory/TheoryDynamics_Transfinite.lean` :

**Brique “Collapse”** :

- `frontierInjected_of_CnExt`  
  -> `RevHalt/Theory/TheoryDynamics_Transfinite.lean:300`
- `limit_collapse_schema_L`  
  -> `RevHalt/Theory/TheoryDynamics_Transfinite.lean:322`
- `limit_collapse_schema`  
  -> `RevHalt/Theory/TheoryDynamics_Transfinite.lean:398`

**Brique “RouteII contradiction”** :

- `routeII_contradiction`  
  -> `RevHalt/Theory/TheoryDynamics_Transfinite.lean:466`

**Escape complet** :

- `structural_escape_transfinite_L`  
  -> `RevHalt/Theory/TheoryDynamics_Transfinite.lean:484`
- `structural_escape_transfinite`  
  -> `RevHalt/Theory/TheoryDynamics_Transfinite.lean:600`

Interpretation formelle :

1) **Absorption + FrontierInjected** ⇒ `S1Rel = ∅` (collapse).
2) **RouteIIApplies + OmegaAdmissible** ⇒ `S1Rel ≠ ∅`.
3) Contradiction ⇒ **escape** : on ne peut pas tout avoir simultanément.

---

## 7) Branchement “metalogique → trilemme/cornes”

Le branchement se fait **via A/B/C** :

- A = `Absorbable` (fixe l’absorption locale)
- B = `OmegaAdmissible` (admissibilité dynamique)
- C = `RouteIIAt` (Route II)

Le **trilemme local** (section 2) se relie donc directement au **collapse/escape** (section 6)
par ces mêmes objets A/B/C.  
Ensuite, la **cofinalité des cornes** (section 3) et **PA dynamique** (section 4)
alimentent l’**extinction générique** (section 5).

---

## Conclusion (structure du raisonnement)

Le raisonnement metalogique est **déjà entièrement formalisé** dans le code :

1) **Escape transfinite** force qu’une corne tombe (contradiction structurelle).
2) **Trilemme + cornes cofinales** localise cette chute le long de `times`.
3) **PA dynamique + bridge** concluent `EventuallyNotAB`.

Toutes les étapes ci-dessus sont traçables dans les fichiers Lean listés.
