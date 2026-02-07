# Primitive Holonomy (relationnelle) et le “problème LLM” : aliasing sous observation partielle

Ce document relie le cadre `PrimitiveHolonomy` (Lean) à un phénomène bien connu en ML/RL et
qui apparaît naturellement quand on traite un système comme une **boîte noire** observée
partiellement.

Références dans le repo :
- `RevHalt/Theory/PrimitiveHolonomy.lean`
- `RevHalt/Theory/PrimitiveHolonomy_PA_Fragment.lean`

## 1) Le cœur : observation partielle + dynamique = ambiguïté de micro-état

Dans `PrimitiveHolonomy`, on sépare explicitement :
- l’**observable** `obs : S → V` (ce que l’on voit),
- le **micro-état** `S` (ce qui existe “vraiment” et peut contenir du caché),
- une cible d’observation `target_obs : P → V` associée à un préfixe `h : P`,
- la **fibre** au-dessus de `h` : `Fiber obs target_obs h = {x : S | obs x = target_obs h}`.

Deux micro-états `x, x'` dans la même fibre sont **indiscernables** par `obs` (même visible),
mais peuvent diverger dans ce qu’ils permettent dans le futur.

## 2) Transport relationnel et holonomie relationnelle

Un “chemin” `p : Path h k` a une sémantique relationnelle `sem p : S → S → Prop`.
Le transport “dans la fibre” est une relation :
`Transport p : FiberPt(h) → FiberPt(k) → Prop`.

Pour une 2-cellule `α : Deformation p q`, on définit l’holonomie :

`HolonomyRel α = Transport p ∘ (Transport q)†`

Intuition : “les sorties possibles par `p` et par `q` se recollent-elles proprement ?”.

Point crucial : comme `Transport` est une **relation** (pas une fonction), l’holonomie peut
être non-triviale pour deux raisons distinctes :
1. **Aliasing interne** (perte d’information) : plusieurs sources possibles pour le même `y`.
2. **Mismatch de chemins** : `p` et `q` transportent différemment (même si chacun est déterministe).

Le fichier `PrimitiveHolonomy_PA_Fragment.lean` donne explicitement **les deux scénarios**.

## 3) Le diagnostic opérationnel : `LagEvent`

`LagEvent` formalise exactement le pattern :
- `x ≠ x'` mais `obs x = obs x'` (même fibre),
- `HolonomyRel α x x'` : la 2D relie les deux micro-états,
- il existe un futur `step` tel que :
  - `x` reste compatible avec `step`,
  - `x'` ne l’est pas.

Donc : un résumé `σ` qui factorise par `obs` (du type `σ = f ∘ obs`) **ne peut pas**
prédire correctement ce futur `step` sur ces deux états, et `PrimitiveHolonomy` produit
des **témoins** (les `x, x'`, le `step`) de cette impossibilité.

## 4) Le nom “standard” côté ML / LLM

Le phénomène “même observation, états différents, futurs différents” porte un nom standard :

- **state aliasing** (RL)
- **perceptual aliasing** (RL)
- **partial observability / POMDP** (cadre global)

Dans le vocabulaire LLM, on le rencontre typiquement sous des formes comme :
- ambiguïté latente (“même texte vu, mais plusieurs états internes plausibles”),
- non-identifiabilité du latent depuis l’I/O,
- et, en aval, échecs de prédiction/contrôle basés sur des features trop pauvres.

Le point de `PrimitiveHolonomy` n’est pas de “résoudre la boîte noire”,
mais de **certifier** quand une classe de résumés est insuffisante, et de décrire
le type d’information qu’il faut ajouter (via `Sig`, signatures de compatibilité).

## 5) Ce que le fragment PA apporte (concret)

Dans `RevHalt/Theory/PrimitiveHolonomy_PA_Fragment.lean` :
- Scénario 1 (“aliasing pur”) : `R_p = R_q` et le transport n’est pas left-unique.
  On prouve `¬ LeftUniqueRel (Transport … p …)`.
- Scénario 2 (“mismatch de chemins”) : `R_p_det ≠ R_q_det`, mais chacun est déterministe.
  On prouve `LeftUniqueRel` pour `p` et `q`, et malgré ça on obtient une holonomie tordue + `LagEvent`.

Autrement dit : même quand chaque chemin est “propre” pris isolément, la 2D peut fabriquer une
obstruction prédictive.

## 6) Et la “black box” alors ?

Oui, on peut traiter le système comme boîte noire **au niveau sémantique** :
le cadre ne demande pas d’ouvrir “l’architecture interne”, seulement de fixer :
- quels sont les observables (`obs`),
- quelles transitions on accepte comme `sem p`,
- quelles commutations on déclare admissibles (`Deformation`).

Mais non : l’holonomie ne “décompile” pas la boîte noire.
Elle fournit plutôt une **théorie des limites** (et des certificats) sur ce que peut prédire
un résumé 1D ou une famille de features, et un langage pour spécifier une réparation (`Gauge` / auto-régulation).

## 7) Prochain pas naturel (pour rendre ça “LLM-critique”)

Pour coller encore plus aux LLM :
- passer de `Prop` (qualitatif) à une version **probabiliste** (relations pondérées),
- instancier `HistoryGraph` sur des “programmes”/réécritures/concurrence réelles,
- choisir un prédicat `OK` (contraintes réalistes sur les “réparations”/interventions),
- et montrer une obstruction/non-obstruction non-triviale sous ces contraintes.

