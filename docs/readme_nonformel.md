---

# RevHalt

RevHalt est une architecture Lean pour **internaliser des propriétés dynamiques infinies** (stabilisation, non-atteinte d’une cible, non-arrêt) dans des **objets structuraux finitaires**. Le projet factorise explicitement trois niveaux, reliés par des morphismes/lemmes de passage :

1. **Observation finie (Splitter/Residus)** : un langage de recouvrements finis sur des états d’information, et les invariants induits (Queue).
2. **Jeux (Up2/Avoid)** : une sémantique d’évitement formulée de manière structurelle.
3. **Temps (Up1/Traces)** : propriétés temporelles sur des trajectoires infinies (Stabilizes, non-atteinte).

Le point clé n’est pas un problème particulier (Collatz peut servir de banc d’essai), mais une **compression canonique** : remplacer des obligations Π₂ sur une trajectoire infinie par la production (ou l’hypothèse) d’un invariant finitaire et d’un pont vers l’évitement de la cible.

---

## Motivation

Les problèmes de terminaison/évitement sont typiquement Π₂ : ils quantifient sur un futur potentiellement infini, souvent avec quantifications imbriquées. RevHalt impose une séparation nette :

* **Construction** (combinatoire/calcul) : produire des objets finitaires (splitters, partitions, certificats de fenêtres, etc.).
* **Vérification** (Lean) : remonter ces objets vers des conclusions temporelles **sans refaire** une analyse infinie “pas-à-pas”.

> RevHalt ne rend pas ces problèmes “faciles” : la difficulté est déplacée vers la construction de certificats finitaires (Queue, ponts). En revanche, la remontée vers des propriétés temporelles est factorisée et entièrement auditée dans Lean.

---

## Organisation du dépôt

### Modules “core”

* `RevHalt/Theory/Splitter/Core.lean`
  Définit le langage de l’observation finie :

  * `Splitter`, `compose`
  * `Cases` (profondeur), `ResEquiv` (équivalence de résidu)
  * `ObsEq` (équivalence observationnelle, version “spec”)
  * `Queue` (invariance de résidu le long d’une dynamique)
  * lemmes structurels (bornes, couverture, stabilité)

* `RevHalt/Theory/Hierarchy.lean`
  **Fichier chapeau** : point de convergence reliant
  **Observation finie → Jeux d’évitement → Traces temporelles**.
  C’est ici que se formule explicitement la thèse “statique fini → dynamique infini”.

### Modules “auxiliaires”

* `RevHalt/Theory/Splitter/Aux.lean`
  Définitions non-spec / pédagogie / expérimentation (p. ex. équivalence “depth 1”, notions dépréciées, atomicité auxiliaire).
  À utiliser uniquement lorsque l’objectif n’est pas la voie “spec”.

### Modules “certificats”

* `RevHalt/Theory/Up2Gain.lean`
  Formats de certificats locaux (fenêtres de gain) et jeu prédicatif associé, destinés à alimenter la chaîne de `Hierarchy`.

  Remarque : les diagnostics `#print axioms` peuvent refléter des choix d’encodage internes à mathlib (quotients, extensionalité propositionnelle) sans que cela change le contenu mathématique des définitions. L’architecture RevHalt (Splitter/Queue/Hierarchy) est formulée de manière prédicative ; la question “axiom-free” est donc traitée module par module et n’est pas un prérequis conceptuel pour la chaîne `Hierarchy`.

---

## Concepts (vue d’ensemble)

### Splitter : observation finie, compositionnelle

Un `Splitter` transforme un état d’information fini `Info Pos` en une liste finie de raffinements (cas), avec :

* **refinement** : chaque cas préserve la satisfaisabilité de l’information d’origine,
* **cover** : tout état compatible tombe dans au moins un cas.

La composition `compose` donne une algèbre des observations, et `Cases` donne la sémantique à profondeur `d`.

### Résidus et équivalence observationnelle

* `ResEquiv S d I0 n m` : à profondeur `d`, aucun cas accessible depuis `I0` ne distingue `n` et `m`.
* `ObsEq S T` : `S` et `T` induisent la même notion de résidu à toute profondeur.

Intuition : ce n’est pas une “partition ad hoc”, mais une **géométrie de l’observable** induite par des recouvrements finis.
> Le Splitter joue le rôle d’un **site finitaire d’observation** ; `Cases` en est la tour de raffinements, et `ResEquiv` les faisceaux invariants au niveau de profondeur donné.

### Queue : invariant de résidu sous dynamique

`Queue` exprime qu’un état initial satisfait un socle `I0` et que, le long de son orbite, il reste dans la même classe d’observation (au sens de `ResEquiv`). C’est l’objet finitaire qui “porte” l’infini : une fois la Queue établie, la fermeture orbitale est un fait structurel (via `queue_orbit_closed`), et la remontée temporelle ne ré-analyse pas la dynamique pas-à-pas.

---

## Key Theorem (Hierarchy)

Le résultat principal est :

```lean
theorem stabilization_chain_up1
    (Pos : Type)
    (S : Splitter Pos) (d : ℕ) (I0 : Info Pos)
    (emb : TemporalEmbedding Pos)
    (h_safe : ∀ p, Queue Pos emb.Next S d I0 p → emb.embed p ∉ emb.Target)
    (hQ : Queue Pos emb.Next S d I0 emb.start)
    : RevHalt.Stabilizes (TimeTrace emb)
```

### Lecture mathématique

* `Queue … emb.start` fournit un **invariant d’observation finitaire** sur l’état initial.
* `h_safe` est le **pont** : tout état dans la Queue évite la cible après interprétation temporelle.
* `Stabilizes (TimeTrace emb)` est une conclusion **temporelle infinie** sur la trace.

### Message du projet

> Une structure finitaire d’observation (Queue) + un morphisme “Queue ⇒ ¬Target”
> suffisent à obtenir une preuve de stabilisation sur la trace temporelle.

---

## Usage attendu

1. Définir une dynamique et son encodage `TemporalEmbedding`.
2. Choisir (ou construire) un `Splitter` et une profondeur `d`.
3. Établir une `Queue` sur l’état initial (ou fournir un certificat/instance).
4. Prouver (ou hypothétiser) le pont `h_safe`.
5. Déduire `Stabilizes (TimeTrace emb)` via `stabilization_chain_up1`.

---

## Portée et contribution

RevHalt ne dépend pas d’un problème particulier ; Collatz peut être un banc d’essai.
La contribution principale est une **factorisation** réutilisable et auditable pour :

* non-atteinte (safety),
* non-terminaison / non-arrêt,
* stabilisation d’orbites,
* validation de certificats finitaires.

Contributions attendues :

* nouveaux splitters (arithmétiques, symboliques),
* nouveaux formats de certificats (fenêtres, résidus, partitions),
* nouveaux ponts `Queue ⇒ ¬Target` pour des dynamiques concrètes,
* exemples end-to-end.

---

## Glossaire Technique

*   **Splitter** : Algorithme ou structure finie capable de raffiner un état d'information en une liste de cas plus précis.
*   **Queue** : Invariant de résidu. Un état qui ne "fuit" jamais de sa classe d'observation le long de sa trajectoire.
*   **ResEquiv** (Residue Equivalence) : Deux états sont ResEquiv si le Splitter ne peut pas les distinguer à une profondeur donnée.
*   **ObsEq** (Observational Equivalence) : Deux Splitters sont ObsEq s'ils génèrent exactement les mêmes distinctions résiduelles.
*   **Target** : L'ensemble des états fatals (arrêt, erreur) que l'on cherche à éviter.
*   **TemporalEmbedding / Embedding** : Structure qui (i) interprète les états du modèle dans un espace de traces/jeux, (ii) transporte la dynamique (`Next`) et (iii) relie l’évitement d’une cible abstraite à la non-atteinte d’un ensemble cible concret.

---

### Ce que RevHalt n’est pas

* Une preuve automatique de Collatz (ou d’un autre problème ouvert).
* Un oracle de terminaison.
* Une réduction miracle de Π₂ en décidable.

> C’est une **factorisation** : si l’on sait exhiber un invariant finitaire (Queue) et un pont de sûreté, alors la conclusion temporelle suit mécaniquement.

---

---

### Perspective Théorie de la Preuve (Ordinaux)

Conceptuellement, cette méthode **court-circuite une preuve par approximants transfinis** (points fixes / jeux).
L'ordinal de fermeture, potentiellement très grand (transfini) dans une preuve temporelle classique, est remplacé — lorsque `Queue` existe — par un certificat finitaire borné par la complexité du Splitter (profondeur, cardinal).
C'est un **abaissement de rang** : l'infini n'est pas "parcouru", il est "tué" par la structure.

---

## Conclusion

RevHalt défend une thèse structurale : la structure ne “prévoit” pas le temps, elle le contraint.
L’objectif n’est pas de dérouler une trajectoire infinie, mais de représenter ce qui est observable et stable sous dynamique.

Concrètement, RevHalt transforme des obligations temporelles de type Π₂ (quantifier sur un futur potentiellement infini) en obligations structurales :

exhiber un objet finitaire d’observation (une Queue, définie via un Splitter et une profondeur),

établir un morphisme de sûreté (un pont du type Queue ⇒ ¬Target),

puis déduire mécaniquement une propriété sur la trace (Stabilizes, non-atteinte, non-arrêt) via Hierarchy.

Ainsi, l’infini n’est pas “parcouru” ni “analysé pas-à-pas” : il est internalisé dans un invariant d’observation stable, et la dynamique est ramenée à une vérification locale de compatibilité avec la cible.

