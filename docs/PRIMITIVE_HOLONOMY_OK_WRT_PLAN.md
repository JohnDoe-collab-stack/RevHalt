# Plan de preuve : `ObstructionWrt` / `AutoRegulatedWrt` sous un `OK` non-trivial

Ce document est un plan **opérationnel** (Lean-first) pour prouver des énoncés du type :

- `ObstructionWrt sem obs target_obs OK J`
- `AutoRegulatedWrt sem obs target_obs OK J`

avec un prédicat `OK` **réaliste** (i.e. pas `OK := True`), de sorte que :

- `emptyGauge` soit exclu (sinon certaines obstructions deviennent vacuement réfutables),
- et/ou que les jauges admissibles ne puissent pas “effacer” artificiellement un témoin.

Références dans le code existant :

- Monotonie “un témoin d’holonomie survit à la correction” si `GaugeRefl` :
  `RevHalt/Theory/PrimitiveHolonomy.lean:355` (`correctedHolonomy_of_holonomy_of_gaugeRefl`).
- Obstruction singleton (version générique) :
  `RevHalt/Theory/PrimitiveHolonomy.lean:575` (`obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl`).
- Instanciation PA (avec `OK_refl_total`) :
  `RevHalt/Theory/PrimitiveHolonomy_PA_Fragment.lean:616`.
- Jauge de “repair” non réflexive (scénario 2) :
  `RevHalt/Theory/PrimitiveHolonomy_PA_Fragment.lean:670` (`repairGauge_det`).

---

## 1) Étape 0 : choisir un `OK` qui a du contenu

### 0.1 Non-vacuïté minimale (exclure `emptyGauge`)

Le point le plus simple : imposer **la totalité** du gauge sur chaque fibre cible.

- Définition : `GaugeTotal` (déjà dans `PrimitiveHolonomy`).
- Effet : `emptyGauge` est automatiquement exclu (car il n’a jamais de sortie).

Dans le PA-fragment, un `OK` minimal utile est :

- `OK_refl_total := GaugeRefl ∧ GaugeTotal`
  (`RevHalt/Theory/PrimitiveHolonomy_PA_Fragment.lean:616`).

### 0.2 Principe “anti-effacement” (faire survivre les témoins)

Si l’objectif est de prouver `ObstructionWrt`, il faut empêcher la jauge de **supprimer** un témoin.
Le choix standard, et déjà exploité par le code, est :

- `GaugeRefl` : la jauge contient la diagonale sur la fibre cible.

Conséquence clé : sous `GaugeRefl`, on a une inclusion (au sens relationnel) :
`Transport ⊆ CorrectedTransport`, donc aussi `HolonomyRel ⊆ CorrectedHolonomy`.

→ C’est exactement ce que formalise `correctedHolonomy_of_holonomy_of_gaugeRefl`.

### 0.3 Principe “réparations autorisées” (si on veut `AutoRegulatedWrt`)

Si l’objectif est au contraire d’exhiber une **réparation** (existence d’une jauge),
alors imposer `GaugeRefl` peut être *trop fort* : une jauge réflexive ne peut pas “tordre”/recoller
certains mismatchs (voir le scénario 2).

Dans ce cas, on choisit un `OK` qui :

- exclut `emptyGauge` (souvent `GaugeTotal` suffit),
- mais **n’impose pas** `GaugeRefl`,
- et impose plutôt des contraintes de “coût”/“forme” (ex: fonctionnalité, localité, bornes, etc.).

Exemple de jauge “réparatrice” non réflexive : `repairGauge_det`
(`RevHalt/Theory/PrimitiveHolonomy_PA_Fragment.lean:670`).

---

## 2) Prouver `ObstructionWrt` (schéma recommandé)

### Hypothèses typiques sur `OK`

Le schéma le plus robuste est :

1. `OK φ → GaugeRefl φ` (anti-effacement),
2. `OK φ → GaugeTotal φ` (non-vacuïté), optionnel mais très utile appliqué.

### Recette (forme “pipeline”)

**Objectif :** `ObstructionWrt sem obs target_obs OK J`.

1. Fixer un `φ` quelconque et une preuve `hOK : OK φ`.
2. Choisir une cellule `c ∈ J` pour laquelle on sait produire un témoin de `TwistedHolonomy`
   (ou directement un témoin `HolonomyRel`).
3. Extraire `x ≠ x'` et `hHol : HolonomyRel sem ... α x x'`.
4. Passer au monde “corrigé” via `GaugeRefl` :
   utiliser `correctedHolonomy_of_holonomy_of_gaugeRefl` (ou la version singleton générique)
   pour obtenir `CorrectedHolonomy sem ... φ α x x'`.
5. Conclure `ObstructionWrt`.

### Variante “singleton J” (le plus simple à industrialiser)

Si `J = {c}`, la preuve peut être compressée via :

- `obstructionWrt_singleton_of_twistedHolonomy_of_gaugeRefl`
  (`RevHalt/Theory/PrimitiveHolonomy.lean:575`).

Le PA-fragment illustre exactement ce pattern sur `J_h0 = {cell_h0}`.

---

## 3) Prouver `AutoRegulatedWrt` (schéma recommandé)

### Hypothèses typiques sur `OK`

Le pattern “existence” est :

1. définir un `OK` qui capture des contraintes réalistes (excluant `emptyGauge`),
2. exhiber explicitement une jauge `φ` telle que `OK φ`,
3. prouver la diagonalisation : pour tout `c ∈ J`, la `CorrectedHolonomy ... φ ...` est la diagonale.

Contrairement à `ObstructionWrt`, ici on ne veut **pas** forcément `GaugeRefl`
(car elle bloque certaines réparations).

### Recette (forme “construction de jauge”)

**Objectif :** `AutoRegulatedWrt sem obs target_obs OK J`.

1. Définir une jauge candidate `φ`.
   - Dans les cas fonctionnels (transports déterministes), une bonne heuristique est :
     faire en sorte que `CorrectedTransport p` et `CorrectedTransport q` “coïncident”
     (ou deviennent des bijections identiques sur la fibre cible).
2. Prouver `OK φ` (souvent : `GaugeTotal` + une contrainte de forme).
3. Pour chaque cellule `c = (h,k,p,q,α)` dans `J`, prouver :
   `∀ x x', CorrectedHolonomy ... φ α x x' ↔ x = x'`.

### Exemple guide : mismatch sans aliasing (scénario 2)

Dans `PrimitiveHolonomy_PA_Fragment.lean`, on a :

- obstruction sous `OK_refl_total` (donc avec `GaugeRefl`),
- mais une réparation explicite si on **relâche** `GaugeRefl` via `repairGauge_det`.

Ce “split” est exactement le point appliqué : *le choix de `OK` décide si la régulation est possible*.

---

## 4) Checklist de “réalisme” pour un `OK` appliqué

Selon le domaine (LLM, concurrence, normalisation de preuves, contrôle), un `OK` utile devrait typiquement :

- Exclure les jauges vides : `GaugeTotal` (ou une variante bornée/locale).
- Contrôler le pouvoir de la jauge :
  - **Localité** (dépend de `obs`, du temps, d’un voisinage, d’un budget),
  - **structure** (fonctionnelle, bijective, invariants préservés),
  - **coût** (nombre de merges autorisés, pas de “flip arbitraire”).
- Être prouvable dans l’instance :
  - des lemmes “monotones” (si on vise obstruction),
  - des lemmes “constructifs” (si on vise régulation).

---

## 5) Cas “bijections” et lien algébrique (anneaux / idéaux / congruences)

Ici on se place dans le **scénario 2** typique : chaque transport sur la fibre est une bijection
(au sens relationnel), mais `p` et `q` ne recollent pas les fibres de la même façon.

### 5.1 Holonomie = permutation (set-level) ; automorphisme seulement si la structure est préservée

Si `T_p, T_q : Fiber(h) → Fiber(k)` sont bijectifs, alors leur converse `(T_q)†` se comporte comme
un inverse relationnel, et :

- `HolonomyRel = T_p ∘ (T_q)†`

devient (intuitivement) le **graphe** de la bijection `h := T_p ∘ T_q⁻¹` sur `Fiber(h)`.

Dans ce régime, `TwistedHolonomy` signifie : `h ≠ id` (il existe `x ≠ x'` avec `h(x) = x'`).

Remarque importante : “bijectif” ici veut dire **bijection d’ensembles** (ou permutation) sur une fibre.
Pour parler littéralement “anneaux / idéaux / mod I”, il faut un verrou supplémentaire : la holonomie doit
être un **endomorphisme algébrique** (morphisme de module / morphisme d’anneau) ou au moins respecter la
congruence choisie. Sinon, la théorie pertinente est plutôt “groupe de permutations” que “idéal”.

Exemple-guide : dans le PA-fragment, le twist `Bool.not` est une bijection, mais si on interprète `Bool`
comme `𝔽₂`, `not : 0 ↦ 1` n’est pas un morphisme d’anneau (il ne préserve pas `0`) : c’est une translation affine.

### 5.2 `OK` comme “congruence admissible”

Dans beaucoup d’applications, le “hidden” d’une fibre a une structure (groupe abélien, module, anneau).
Un `OK` réaliste est alors : la jauge doit être une **congruence** compatible avec la structure
et *non arbitraire*.

Pattern :

1. Sur une fibre `B`, choisir un “objet de quotient” :
   - **module** : un sous-module `N` (ou `Submodule`),
   - **anneau** : un idéal `I` (ou `Ideal`).
2. Définir la relation de jauge par :
   - `b ~ b'  :↔  (b - b') ∈ N` (module),
   - `b ~ b'  :↔  (b - b') ∈ I` (anneau).
3. Lever `~` en une `Gauge` sur `FiberPt` (même `visible`, on ne jauge que le `hidden`).

Ce `OK` :

- exclut les jauges “magiques” (il faut être un quotient),
- est compatible avec `GaugeRefl` (car `b - b = 0 ∈ N/I`),
- permet un **axe appliqué clair** : quel quotient est autorisé (budget, localité, taille, stabilité).

### 5.3 Réguler = trivialiser l’action d’holonomie dans un quotient (quand l’action descend au quotient)

Dans le cas bijectif, les holonomies agissent comme des permutations `h` de la fibre (au sens set-level).
Si, en plus, elles préservent une structure (module/anneau), on peut les traiter comme des automorphismes/endomorphismes
dans cette catégorie.
“Diagonaliser l’holonomie corrigée” revient à rendre `h` **trivial** après passage au quotient :

- sur un module : choisir `N` tel que `h` induit l’identité sur `B/N`,
- sur un anneau : choisir `I` tel que `h` induit l’identité sur `B/I`.

Heuristique constructive utile (module) :

- prendre `N` comme le sous-module engendré par l’image de `(h - id)` :
  `N := span (range (h - id))`.

Version anneau (si `h` est un endomorphisme d’anneau, ou au moins respecte l’addition/multiplication) :

- prendre `I` comme l’idéal engendré par `{h(b) - b | b ∈ B}`.

Le point conceptuel : vous passez d’un “OK arbitraire sur relations” à un **OK de type algébrique**
où `AutoRegulatedWrt` devient un problème de *quotient admissible qui tue une action*.

### 5.4 Implication “profonde” côté anneaux : `OK` comme famille d’idéaux admissibles (après restriction)

Vu comme un cadre “anneaux”, l’apport n’est pas juste une reformulation : c’est un *filtre de réalisme*.

1. **Dans un cadre algébrique standard**, une “jauge admissible” est typiquement une congruence,
   donc (pour les anneaux) un idéal `I`. Dans **notre code**, une `Gauge` est a priori une relation arbitraire
   (et dépendante du chemin). La lecture “idéaux” devient mathématiquement exacte seulement après avoir **restreint**
   `OK` aux jauges qui proviennent de congruences/quotients (et idéalement sont indépendantes du chemin, ou ne dépendent
   que de la fibre / du type de move). Dans ce régime, `OK` spécifie une *classe d’idéaux admissibles*
   (bornés, locaux, stables, de coût contrôlé, etc.).

2. **Dans ce régime**, les deux problèmes deviennent des énoncés très nets :
   - `AutoRegulatedWrt` : `∃ I ∈ OK,  h ≡ id (mod I)` (l’action d’holonomie est tuée par le quotient).
   - `ObstructionWrt` : `∀ I ∈ OK,  h ≢ id (mod I)` (l’action survit à toutes les réductions autorisées).

   Remarque de précision : ces formes “mod I” deviennent **littérales** si la cible de régulation est formulée
   *dans le quotient* (ou via une relation `~`) plutôt qu’en égalité brute `x = x'` sur la fibre.

3. **Le PA-fragment illustre un point important** : il existe des “réparations” relationnelles non réflexives
   (ex: `repairGauge_det`, `RevHalt/Theory/PrimitiveHolonomy_PA_Fragment.lean:670`) qui peuvent corriger une holonomie,
   mais qui ne correspondent pas à un quotient/congruence (un idéal donne toujours une relation réflexive).
   Donc dès que `OK` est “anneau-compatible” (congruences/idéaux), certaines réparations disparaissent et se transforment
   en **obstructions algébriques réelles**.

4. **Lecture holonomique des anneaux : trajectoires non bijectives par nature.**
   Du point de vue “holonomie primitive”, une grande partie de l’algèbre commutative se formule déjà comme
   une géométrie de flèches **non bijectives** :
   - un quotient `R → R/I` est une application surjective mais typiquement non injective (collapse),
   - un morphisme d’anneaux transporte de l’information et peut créer des identifications via son noyau,
   - les idéaux / congruences décrivent précisément “ce qui devient indiscernable”.

   Traduction dans le cadre :
   - un `Transport` many-to-one correspond exactement à un “passage au quotient” (perte contrôlée),
   - `T ∘ T†` est la *relation noyau* (“avoir la même image”), i.e. la version holonomique de “`≡ (mod I)`”,
   - et `OK` borne **quels** collapses (quels quotients) sont autorisés.

   C’est ce déplacement qui rend le lien anneaux/holonomie non superficiel : on ne colle pas un vocabulaire,
   on reconnaît que les objets structurants (idéaux, congruences, noyaux) sont déjà des invariants de
   trajectoires non bijectives.

5. **Spécification minimale pour que la lecture “idéaux / mod I” soit littérale (verrous A/B/C/D).**

   Pour passer de “bonne intuition” à “énoncé exact”, il faut expliciter quatre contraintes sur `OK`
   (ou sur une sous-classe de `Gauge`) :

   (A) **Congruence ⇔ idéal (bilatère si non commutatif).**
   - Côté anneaux, une congruence `~` correspond à un idéal `I` via `a ~ b ↔ a - b ∈ I`.
   - En non-commutatif, il faut un idéal **bilatère** pour que `R/I` hérite d’une structure d’anneau.

   (B) **Path-blind (au moins endpoint-blind).**
   - Dans le code actuel, une `Gauge` dépend de `p : Path h k`.
   - Pour être un “quotient de la fibre au-dessus de `k`”, la jauge doit dépendre essentiellement de `k`
     (ou d’un “type de move”), pas de l’historique fin.
   - Spécification typique : il existe une relation `~k` telle que `φ p = ~k` pour tout `p : h ⟶ k`.

   (C) **Descente au quotient (compatibilité).**
   - Pour pouvoir écrire “`h ≡ id (mod I)`”, il faut que le transport (ou le transport corrigé)
     soit **bien défini sur le quotient**.
   - Schéma : si `x ~h x'` et `T_p x y` et `T_p x' y'`, alors `y ~k y'`.

   (D) **Structure-preserving (anneau / module).**
   - Pour que “congruence ⇔ idéal” s’applique et que “`≡ (mod I)`” soit un invariant algébrique,
     il faut que la relation `~` soit compatible avec les opérations, *et* que les transports/holonomies
     que l’on veut “tuer” soient des morphismes dans la même catégorie (ou au minimum respectent `~`).
   - Sans (D), on a toujours un noyau/indiscernabilité au niveau *ensembles* (`T ∘ T†`), mais pas forcément
     un idéal (ou un quotient bien typé comme module/anneau).

   Une fois (A)(B)(C)(D) posés, les deux lectures deviennent réellement des énoncés “mod I” :
   - **AutoRegulatedWrt (version quotient)** : `∃ I ∈ OK`, pour toute cellule admissible,
     l’holonomie *induite* sur `Fiber(h)/~h` est l’identité.
   - **ObstructionWrt (version quotient)** : `∀ I ∈ OK`, il existe une cellule où l’holonomie induite
     n’est pas l’identité sur le quotient.

   Et c’est précisément là que `repairGauge_det` joue son rôle : dès que `OK` impose (A)(B)(C)(D),
   les “réparations” non réflexives ou history-dependent sortent du jeu, et ce qui reste est
   une obstruction algébrique authentique.

---

## 6) Ce qu’il reste à faire (prochaines cibles Lean)

1. Formaliser (et comparer) plusieurs familles de `OK` “naturelles” :
   - `OK_refl_total` (anti-effacement + non-vacuïté),
   - `OK_total_functional` (réparations autorisées mais contrôlées),
   - `OK_obs_local` (jauge qui factorise par `obs`, ou dépend d’un résumé).
2. Montrer, dans une même instance, un **diagramme** :
   - `ObstructionWrt` sous `OK_strict`,
   - `AutoRegulatedWrt` sous `OK_relaxed`,
   et documenter ce que “relaxed” autorise concrètement.
3. Sortir du PA-fragment :
   - instancier sur un exemple de concurrence (commutations),
   - ou un exemple de “décodage LLM” (chemins = ordres de calcul / schedule de modules),
   où `OK` correspond à un vrai type de mécanisme d’intervention.
