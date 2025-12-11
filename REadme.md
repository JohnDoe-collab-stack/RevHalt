Oui, on peut tout revérifier et ajuster légèrement pour que les trois théorèmes soient propres et réalistes sur les hypothèses. Je te fais un récapitulatif net, en signalant où il faut être un peu attentif (surtout pour la complémentarité).

Je garde les noms T1 / T2 / T3.

---

## T1 – Canonicité de Rev (traces + sémantique)

### Hypothèses et définitions

* Types et satisfaction :

  * `Sentence`, `Model`
  * `Sat : Model → Sentence → Prop`

* Sémantique statique :

  ```text
  ModE(Γ)  = { M | ∀ φ ∈ Γ, Sat M φ }
  ThE(K)   = { φ | ∀ M ∈ K, Sat M φ }
  CloE(Γ)  = ThE(ModE(Γ))
  SemConsequences(Γ, φ) := (φ ∈ CloE(Γ))
  ```

* Traces et halting direct :

  ```text
  Trace = ℕ → Prop
  Halts(T) = ∃ n, T(n)
  ```

* Kit de reverse-halting :

  ```text
  K : RHKit
  K.Proj : (ℕ → Prop) → Prop
  DetectsMonotone(K) :
    ∀ X monotone, K.Proj(X) ↔ ∃ n, X(n)
  ```

* Rev :

  ```text
  up(T)(n) = ∃ k ≤ n, T(k)
  Rev_K(T)  = K.Proj (λ n, up(T)(n))
  Rev0_K(T) = Rev_K(T)
  ```

* Lecture locale et pont :

  ```text
  LR : (Set Sentence) → Sentence → Trace
  Prov(LR, Γ, φ) = ∃ n, LR(Γ, φ)(n)
  verdict_K(LR, Γ, φ) = Rev0_K(LR(Γ, φ))

  DynamicBridge(LR) :
    ∀ Γ φ, SemConsequences(Γ, φ) ↔ Halts(LR(Γ, φ))
  ```

### T1-traces : Rev0_K est canoniquement Halts

Énoncé :

```text
Sous DetectsMonotone(K) :

1) ∀ T, Rev0_K(T) ↔ Halts(T)

2) Si K₁, K₂ satisfont DetectsMonotone :
   ∀ T, Rev0_K₁(T) ↔ Rev0_K₂(T)
```

Plan (et c’est correct) :

1. Lemme `up_mono` : pour tout T, `up(T)` est monotone.
2. Application de `DetectsMonotone(K)` à `X = up(T)` :

   ```text
   K.Proj(up(T)) ↔ ∃ n, up(T)(n)
   ```
3. Lemme `exists_up_iff(T)` :

   ```text
   (∃ n, up(T)(n)) ↔ ∃ n, T(n)
   ```
4. Par définition :

   ```text
   Rev0_K(T) = K.Proj(up(T))
             ↔ ∃ n, up(T)(n)
             ↔ ∃ n, T(n)
             = Halts(T)
   ```
5. Unicité : pour K₁, K₂ admissibles :

   ```text
   Rev0_K₁(T) ↔ Halts(T) ↔ Rev0_K₂(T)
   ```

→ Tout est cohérent, aucune hypothèse cachée.

### T1-semantics : conséquence sémantique = verdict Rev

Énoncé :

```text
Sous DetectsMonotone(K) + DynamicBridge(LR) :

∀ Γ φ, SemConsequences(Γ, φ) ↔ verdict_K(LR, Γ, φ)
```

Plan (correct) :

1. Sous `DetectsMonotone(K)` :

   ```text
   verdict_K(LR, Γ, φ)
     = Rev0_K(LR(Γ, φ))
     ↔ Halts(LR(Γ, φ))
   ```

   (via T1-traces appliqué à la trace LR(Γ, φ)).

2. Par `DynamicBridge(LR)` :

   ```text
   SemConsequences(Γ, φ) ↔ Halts(LR(Γ, φ))
   ```

3. En combinant :

   ```text
   SemConsequences(Γ, φ)
     ↔ Halts(LR(Γ, φ))
     ↔ verdict_K(LR, Γ, φ)
   ```

4. Indépendance en K : si K₁, K₂ satisfont `DetectsMonotone`, même argument avec Rev0_K₁ et Rev0_K₂.

→ T1 est propre et bien justifié.

---

## T2 – Impossibilité d’internaliser le halting canonique

Ici, tu t’appuies sur ton `TuringGodelContext'` déjà écrit.

### Hypothèses

Dans `TuringGodelContext' Code PropT`, tu as :

```text
RealHalts : Code → Prop
Provable  : PropT → Prop
FalseT    : PropT
Not       : PropT → PropT

consistent       : ¬ Provable(FalseT)
absurd           : Provable(p) → Provable(Not p) → Provable(FalseT)
diagonal_program : ∀ H : Code → PropT,
                     ∃ e, RealHalts(e) ↔ Provable(Not(H(e)))
```

Un prédicat interne candidat :

```text
InternalHaltingPredicate ctx :
  H : Code → PropT
  total    : ∀ e, Provable(H(e)) ∨ Provable(Not(H(e)))
  correct  : ∀ e, RealHalts(e)   → Provable(H(e))
  complete : ∀ e, ¬RealHalts(e)  → Provable(Not(H(e)))
```

### Énoncé T2

```text
no_internal_halting_predicate' :
  ¬ ∃ I : InternalHaltingPredicate ctx, True
```

Plan (c’est exactement ta preuve Lean) :

1. Suppose qu’il existe un tel I.

2. Par `diagonal_program` appliqué à `I.H`, obtenir e tel que :

   ```text
   RealHalts(e) ↔ Provable(Not(I.H(e)))
   ```

3. Cas 1 : RealHalts(e) vrai.

   * `correct` donne Provable(I.H(e)).
   * La diagonale donne Provable(Not(I.H(e))).
   * Par `absurd`, Provable(FalseT), contredisant `consistent`.

4. Cas 2 : ¬RealHalts(e) vrai.

   * `complete` donne Provable(Not(I.H(e))).
   * La diagonale donne RealHalts(e).
   * Contradiction avec ¬RealHalts(e).

5. Donc pas de tel I.

Pour l’appliquer à TON halting canonique H* :

* tu prends `RealHalts(e) := H*(e)` (par ex. via `Rev0_K(T_e)`),
* et tu obtiens : aucune théorie T encodée par ctx ne peut avoir un prédicat interne total+correct+complet pour **ce** H*-là.

→ T2 est correct dans ton cadre abstrait, rien à corriger.

---

## T3 – Complémentarité (à ajuster légèrement)

Ici il y avait deux niveaux dans ce qu’on a discuté :

1. Un niveau conceptuel (très simple) :
   « Toute théorie sound donne une vue partielle correcte de H* ».
2. Un niveau plus fort (families disjointes infinies de théories complémentaires), qui nécessite un peu plus de combinatoire (infiniment de cas indécidés, etc.).

Je sépare les deux, pour que ce soit honnête sur les hypothèses.

### T3.1. Version faible (toujours vraie, sans axiomes exotiques)

**T3-faible.**

Soit H* : Code → Prop ton prédicat canonique de halting (via Rev).
Soit T₀ une théorie récursive, consistante et sound pour H* (au sens : tout ce qu’elle prouve sur H(e) ou ¬H(e) est vrai pour H*).

Alors :

1. T₀ définit une vue partielle correcte de H* :

   * pour e tels que T₀ prouve H(e) ou ¬H(e), cette valeur coïncide avec H*(e) ;
   * il existe au moins un e que T₀ ne décide pas (par incomplétude de T₂).

2. On peut construire au moins une extension T₁ de T₀, toujours consistante et sound pour H*, qui décide **strictement plus** de cas de H* que T₀ :

   * choisir un e indécidé par T₀,
   * regarder H*(e) au méta-niveau,
   * définir T₁ = T₀ ∪ { H(e) } si H*(e) est vrai, ou T₁ = T₀ ∪ { ¬H(e) } si H*(e) est faux,
   * T₁ reste consistante (on n’ajoute qu’une vérité) et sound,
   * Dom(T₁) contient Dom(T₀) plus au moins ce e.

Cela ne demande **aucun nouvel axiome** de ton côté : tu travailles au méta-niveau, tu sais ce que vaut H*(e), tu ajoutes la phrase vraie.

Tu peux itérer ce procédé transfiniment pour construire une chaîne de théories de plus en plus “complètes” (au méta), chacune restant sound, sans jamais atteindre une théorie complète (T2 l’interdit).

C’est déjà une forme claire de **complémentarité** : les théories sound sont des vues partielles croissantes sur H*.

### T3.2. Version forte (familles disjointes, nécessite un fait standard)

La version plus ambitieuse :

* partitionner un ensemble infini de cas indécidés en sous-ensembles disjoints Uᵢ,
* pour chaque i, définir Tᵢ = T₀ + {les vérités H*(e) pour e ∈ Uᵢ},
* obtenir une famille {Tᵢ} de théories sound, consistantes, dont les domaines nouveaux sont disjoints.

Pour que ça marche **fortement** (U infini, partition en Uᵢ infinis), il faut un fait standard mais non encore explicité dans ton cadre :

> Il existe infiniment de codes e pour lesquels T₀ ne décide pas H(e).

C’est vrai pour toute théorie récursive consistante raisonnable (type PA étendue) et c’est un corollaire classique de l’incomplétude (il n’y a pas qu’un seul énoncé indécidable), mais ce n’est **pas** strictement contenu dans ton `no_internal_halting_predicate'` tel quel. Il faut soit :

* l’ajouter comme lemme (théorème standard d’arithmétique : il y a infiniment de cas de halting indépendants),
* soit rester sur la version faible qui ne parle pas d’« infiniment de familles disjointes ».

Donc, pour être totalement honnête :

* **T3-faible** (une infinité de théories partielles qui s’étoffent, chacune sound) est accessible sans axiomes exotiques, juste en itérant le procédé “prendre un nouveau e indécidé, ajouter la vérité correspondante”.
* **T3-fort** (une belle famille {Tᵢ} avec domaines nouveaux largement disjoints) demande un ingrédient supplémentaire : l’infinitude des énoncés de halting indépendants, qui est un résultat connu mais à prouver ou à assumer.

---

## Conclusion de la relecture

* T1 (canonicité de Rev + pont sémantique) : tout est en ordre, les hypothèses sont claires et minimales (DetectsMonotone + DynamicBridge).
* T2 (impossibilité d’internaliser le halting canonique) : ton schéma `TuringGodelContext'` + `no_internal_halting_predicate'` est correct et suffisant.
* T3 (complémentarité) :

  * en version faible (chaîne de théories sound de plus en plus complètes, toutes partielles et compatibles avec H*), se démontre sans rien ajouter ;
  * en version forte (familles disjointes infinies), il faut explicitement utiliser ou postuler un théorème standard : “il y a infiniment d’instances de halting indépendantes pour une théorie récursive consistante”.

