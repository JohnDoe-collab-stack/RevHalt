---

## Ce que `Hierarchy.lean` établit formellement

`Hierarchy.lean` ne juxtapose pas “plusieurs lectures d’un même objet”. Il formalise une **chaîne de réductions constructives** entre trois niveaux, avec des interfaces explicitement typées et des hypothèses de compatibilité.

### Niveaux et objets

| Niveau   | Domaine (formel)                      | Objet / prédicat (dans le code)           | Sens informel                                              |
| -------- | ------------------------------------- | ----------------------------------------- | ---------------------------------------------------------- |
| Splitter | Structure de résolution paramétrique  | `Queue Pos Next S d I0 n`                 | Certificat de “couverture”/résolution d’un état            |
| Up2      | Théorie des jeux (kernel d’évitement) | `Avoid2Mem G Target (embed n)`            | Appartenance au noyau d’évitement (sécurité structurelle)  |
| Up1      | Traces / stabilisation                | `¬ T n` puis `Stabilizes (TimeTrace emb)` | Non-atteinte du target au point (puis le long de l’orbite) |

Remarque de portée : le fichier est **paramétrique** en `Pos : Type` et en `Splitter Pos`. L’interprétation “arithmétique (primes/divisions)” dépend de l’instanciation concrète de `Splitter` dans `Splitter.Core`.

---

## La chaîne Splitter → Up2 → Up1 (pointwise)

### 1) Up2 → Up1 : de l’évitement à la non-atteinte du target

Le lemme `avoid2_implies_not_target` montre que si une position est dans `Avoid2Set`, alors elle n’est pas dans `Target`. Via la spécification d’encodage

`target_spec : embed n ∈ Target ↔ T n`

on en déduit immédiatement (théorème `up2_implies_up1_pointwise`) :

> Si `embed n ∈ Avoid2Set`, alors `¬ T n`.

C’est un passage purement logique : “être dans le noyau d’évitement” exclut “être une cible”, et donc exclut la vérité du prédicat de trace correspondant.

---

### 2) Splitter → Up2 : le pont de réduction (bridge)

Le cœur “trans-domaines” est encapsulé dans le théorème importé :

`queue_splitter_subset_avoid2` (dans `RevHalt.Theory.Splitter.AvoidanceBridge`)

`Hierarchy.lean` le mobilise sous la forme `splitter_implies_avoid2`, qui requiert :

* une dynamique déterministe encodée dans le jeu :
  `h_hom : ∀ n, G.moves (embed n) = {embed (Next n)}`
* un contrôle de tour (ici, toujours `Turn.P`) :
  `h_turn : ∀ n, G.turn (embed n) = Turn.P`
* une sûreté locale sur les cas de la Queue :
  `h_safe : ∀ n, Queue … n → embed n ∉ Target`

Sous ces hypothèses, on obtient :

> `Queue … n` ⇒ `Avoid2Mem G Target (embed n)`.

C’est exactement le point où une structure de “résolution” (Queue/Splitter) est convertie en un énoncé de type “kernel d’évitement” (Up2).

---

### 3) Le théorème de chaîne : `hierarchy_chain`

Le théorème `hierarchy_chain` compose les deux étapes précédentes :

1. `Queue … n` ⇒ `Avoid2Mem … (embed n)` (bridge Splitter→Up2)
2. `Avoid2Mem … (embed n)` ⇒ `¬ T n` (Up2→Up1 via `target_spec`)

Donc, **au niveau pointwise** :

> Un certificat `Queue` entraîne la non-vérité du prédicat de trace au même index.

---

## Passage au temps : stabilisation le long de l’orbite (Up1 complet)

`Hierarchy.lean` spécialise ensuite l’énoncé à un contexte temporel via `TemporalEmbedding`, qui ajoute :

* un successeur `Next`,
* les contraintes `hom` et `turnP` (les mêmes que ci-dessus),
* un point de départ `start`.

On définit alors la trace temporelle le long de l’orbite :

`TimeTrace emb k := emb.T (iterate Next k start)`.

Avec le lemme d’invariance `queue_orbit_closed`, on transporte `Queue` de `start` à chaque itéré `iterate Next k start`, puis on applique `hierarchy_chain` point par point. Ceci donne :

* `stabilization_chain_orbit : ∀ k, ¬ emb.T (iterate Next k start)`
* donc `stabilization_chain_up1 : Stabilizes (TimeTrace emb)`.

---

## La signification mathématique exacte

Ce que prouve `Hierarchy.lean` est un **schéma de réduction** :

> (Certificat de résolution `Queue` sur un état)
>
> * (compatibilité dynamique jeu/orbite)
> * (sûreté locale des cas)
>   ⟹ (appartenance au noyau Up2)
>   ⟹ (non-atteinte pointwise)
>   ⟹ (stabilisation le long de l’orbite).

C’est donc bien une **architecture de transfert inter-couches** : une structure de niveau “résolution” se compile en une propriété de niveau “jeu” (Up2), qui se compile en une propriété temporelle Π₁ (Up1).
