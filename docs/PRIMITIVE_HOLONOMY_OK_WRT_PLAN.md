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

## 5) Ce qu’il reste à faire (prochaines cibles Lean)

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

