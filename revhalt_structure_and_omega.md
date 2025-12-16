# RevHalt — structure et ancrage formel (référence synthétique)

Ce document fixe une **lecture structurée** de la dynamique globale de RevHalt (5 axes) et explicite l’**ancrage formel** de l’instance **Ω (OmegaChaitin)** via ses primitives **discrètes** (bits) et **continues** (cuts rationnels), ainsi que leur **pont arithmétique**.

---

## Mini-Glossaire contextuel

*   **`OmegaModel`** : Index de temps `t` (souvent alias vers `ℕ` dans l'implémentation) utilisé comme modèle local.
*   **`OmegaApprox t`** : Approximation rationnelle calculable de $\Omega$ au temps `t` (somme partielle des poids des programmes terminant avant `t`).
*   **`OmegaSat t φ`** : Relation de satisfaction locale ; la propriété `φ` est-elle vérifiée au temps `t` par l'approximation courante ?
*   **`LR_omega`** : *Local Reading*, la trace (suite de booléens dans le temps) qui surveille l'évolution de validité d'une formule.
*   **`Kit`** : Mécanisme abstrait d'observation transformant une trace dynamique en verdict binaire limite.
*   **`pathCost`** : Coût de trajectoire dans le graphe de moves (nombre d'étapes dynamiques), et non la longueur d'une preuve logique.

---

## Partie 1 — Les 5 axes structurels de la dynamique globale

### Axe 1 — Moteur d’incomplétude (Fuel)

* **Pivot** : `fuel_from_T2`
* **Fichier** : `RevHalt/Dynamics/Core/Fuel.lean`
* **Rôle structurel** : l’incomplétude est modélisée comme une **énergie dynamique** (fuel) qui force l’extension perpétuelle du système, et non comme une simple barrière statique.

### Axe 2 — Canonicité de l’observation

* **Pivot** : `T1_traces`
* **Fichier** : `RevHalt/Theory/Canonicity.lean`
* **Rôle structurel** : l’arrêt (`Halts`) est posé comme **signature universelle** de vérité, robuste vis-à-vis des variations du mécanisme d’observation (*Kit*).
    *   *Précision* : `T1_traces` montre que, pour toute classe de kits admissibles (satisfaisant `DetectsMonotone`), le verdict-limite dépend uniquement de la propriété d’arrêt de la trace (et coïncide avec `Halts` dans le cadre considéré).

### Axe 3 — Vérité cinétique

* **Pivot** : `Master_Closure`
* **Fichier** : `RevHalt/Kinetic/MasterClosure.lean`
* **Rôle structurel** : la vérité est définie comme une **limite inductive** (*Closure*) d’un processus de stratification, plutôt qu’un ensemble statique préexistant.
    *   *Précision* : La *Closure* est le plus petit ensemble de sentences contenant la base et fermé par les règles dynamiques de RevHalt (moves / fuel-extension).

### Axe 4 — Unification Turing–Gödel

* **Pivot** : `T2_impossibility`
* **Fichier** : `RevHalt/Theory/Impossibility.lean`
* **Rôle structurel** : indécidabilité (Turing) et incomplétude (Gödel) sont formulées comme deux faces d’une **unique impossibilité structurelle** : absence d’un prédicat d’arrêt interne simultanément **total / correct / complet**.

### Axe 5 — Dualité coût / information

* **Pivot** : `cost_ge_info_gain`
* **Fichier** : `RevHalt/Dynamics/Core/Complexity.lean`
* **Rôle structurel** : toute émergence de vérité (gain d’information) admet un **coût certifiable** (`pathCost`). Le coût borne le gain d’information via un **témoin explicite** (un chemin de moves).

---

## Partie 2 — Ancrage formel OmegaChaitin (discret / continu)

**Fichier cible** : `RevHalt/Dynamics/Instances/OmegaChaitin.lean`
Objet : implémentation de la hiérarchie inversée pour Ω via `OmegaSentence`.

---

### 2.1 Primitif discret — bit de Ω

* **Concept** : coordonnée discrète (bit)
* **Lean** : `OmegaBit` / `OmegaSentence.BitIs`
* **Dépendances immédiates** : `OmegaSentence`, `OmegaReferent`

```lean
inductive OmegaSentence
| BitIs (n : ℕ) (a : ℕ) : OmegaSentence
...

def OmegaBit (n : ℕ) (a : ℕ) (_ : OmegaReferent) : OmegaSentence :=
  OmegaSentence.BitIs n a
```
*Note* : `BitIs n a` code un bit via `a % 2`.

### 2.2 Primitif continu — cut rationnel

* **Concept** : coordonnée continue rationnelle (cut)
* **Lean** : `OmegaCut` / `OmegaSentence.CutGe`
* **Dépendances immédiates** : `OmegaSentence`, `Rat` (ℚ)

```lean
inductive OmegaSentence
| CutGe (q : ℚ) : OmegaSentence
...

def OmegaCut (q : ℚ) (_ : OmegaReferent) : OmegaSentence :=
  OmegaSentence.CutGe q
```

---

### 2.3 Hiérarchie inversée (asymétrie cuts/bits)

* **Standard (classique)** : bits (base) → réel (dérivé)
* **RevHalt** : **Cuts semi-décidables** (base / primitifs) → **Bits indécidables** (reconstruits / dérivés).
* **Ancrage de semi-décidabilité** : `namespace CutComputable`

**Explicite** : Le système prend comme primitives les prédicats `CutGe q`, qui sont semi-décidables (robustes via `OmegaApprox`), et **reconstruit** les bits comme des propriétés dérivées (intersections de fenêtres).

Extrait d’intention (asymétrie) :

```lean
theorem cut_semidecidable_bit_not (n : ℕ) :
    (∀ q, Halts (LR_omega ∅ (OmegaSentence.CutGe q)) ↔ (∃ t, OmegaApprox t ≥ q)) ∧
    -- For Bits: halting only works if we guess the right bit
    ...
```

*Lecture* : `Halts (LR_omega ... (CutGe q))` caractérise `OmegaApprox ≥ q` (on peut attendre l'événement, c'est semi-décidable). Pour les bits, il n’existe pas de procédure d’arrêt uniforme garantissant de trancher le bit sans information supplémentaire (typiquement, il faut « tomber sur » le bon bit).

---

### 2.4 Lien discret / continu — équivalence “fenêtre dyadique”

* **Pivot** : `omega_bit_cut_link`
* **Fichier** : `RevHalt/Dynamics/Instances/OmegaChaitin.lean`

```lean
theorem omega_bit_cut_link : ∀ {t : OmegaModel} {n a : ℕ} {x : OmegaReferent},
    OmegaSat t (OmegaBit n a x) ↔
    ∃ (k : ℤ),
      OmegaSat t (OmegaCut ((k : ℚ) / (2 ^ n)) x) ∧
      ¬ OmegaSat t (OmegaCut (((k + 1) : ℚ) / (2 ^ n)) x) ∧
      k.toNat % 2 = a
```
*Note* : On peut lire `k` comme l’indice dyadique correspondant (typiquement proche de `⌊2^n * OmegaApprox t⌋`). Comme `OmegaApprox t ≥ 0`, `k` est un entier non-négatif, donc `k.toNat` préserve la valeur pour le test de parité.

**Portée formelle** : un bit `a` à la précision `n` est équivalent à placer la valeur continue dans une **fenêtre dyadique** : *vrai au cut inférieur*, et *non-vrai au cut supérieur* (`¬ OmegaSat …`), avec contrainte de parité. Le bit est ainsi formalisé comme une **propriété émergente** d’une topologie continue, plutôt qu’un atome isolé.
