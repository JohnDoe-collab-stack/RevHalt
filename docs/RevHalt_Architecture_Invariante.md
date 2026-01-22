# Invariant Architectural et Circuit Logique de RevHalt

Ce document formalise la "mise à plat en circuit" de la dynamique RevHalt. L'invariant central n'est pas une propriété des ordinaux ou des ensembles "en soi", mais résulte de la **politique de limite** (LimitOp) et de ce qu'elle autorise ou interdit dans un système ouvert (frontière active).

Nous présentons ici un **cœur minimal** (netlist) réutilisable pour ω, pour tout ordinal limite λ, et pour les opérateurs de saut (LimitOp "Jump").

---

## 1. Clarification Essentielle : "RouteII" et "Frontière Non-Vide"

Il est crucial de distinguer deux notions qui jouent des rôles différents dans le circuit logique :

1. **RouteIIAt(Γ)** (défini dans `TheoryDynamics.lean`) :
    * C'est *définitionnellement* : `(S1Rel Γ).Nonempty`.
    * Dans ce cas, le signal **R** (RouteII) est équivalent au signal **N** (Non-Vide). Le bloc de connexion est un fil direct.

2. **RouteIIApplies(… Γ)** (utilisé dans `structural_escape_explicit`, `Trajectory`) :
    * C'est une hypothèse "de régime" ou un signal de design : "on exige que le système reste ouvert à la limite".
    * Cela **implique** typiquement `N`, mais peut porter plus de structure. Le bloc de connexion est alors un pont non trivial (ou un axiome de design).

**Invariant du circuit** : Le bloc logique connectant RouteII à Non-Vide dépend de la version choisie, mais la conséquence `N(λ)` est toujours activée si RouteII est actif.

---

## 2. Netlist Minimale (Signaux et Sorties)

Ce circuit "plat" correspond exactement aux briques utilisées dans les preuves de *collapse*, *trilemme* et *structural escape*.

### Entrées (Signaux)

* **AbsBefore(λ)** : `∃ β < λ, Absorbable (Γ_{β+1})`
  * *Il existe une étape d'absorption avant la limite.*
* **SuccLimit(λ)** : `Order.IsSuccLimit λ`
  * *La limite est atteinte par une suite de successeurs (la bonne classe pour le schéma).*
* **LimitOp = Union** : "La limite est l'union des stades" (opérateur canonique `transIter`).
* **Inv** : Invariants structurels (paramètres des lemmes).
  * Monotonicité de Provable, injection frontière, Cn extensive/idempotente/ProvClosed, etc.
* **RouteII(λ)** : Le choix de design pour la frontière.
  * Soit `RouteIIAt(Γ_λ)` (équivalent à `S1Rel(Γ_λ).Nonempty`).
  * Soit `RouteIIApplies(Γ_λ)` (hypothèse de régime fort).
* **Cont(λ)** : Condition de continuité.
  * `ContinuousAtL(L,F,A0,λ)` pour le cas général.
  * `OmegaContinuousSet(F)` pour le cas ω.

### Sorties

* **E(λ)** : `S1Rel(Γ_λ) = ∅` (Frontière vide / Extinction).
* **N(λ)** : `(S1Rel(Γ_λ)).Nonempty` (Frontière active).
* **⊥** : Contradiction (Faux).

---

## 3. Blocs Logiques (Gates)

Ces "portes" correspondent aux théorèmes et lemmes réels du projet.

### Gate G1 — LimitCollapse

*Correspondance :* `limit_collapse_schema` (transfini) ou `S1Rel_omegaΓ_eq_empty_of_absorbable_succ` (ω).

> **(AbsBefore(λ) ∧ SuccLimit(λ) ∧ Inv ∧ LimitOp=Union) ⇒ E(λ)**

C'est la porte la plus structurante. Elle encode le fait que l'union-limite combinée à une absorption antérieure implique l'**extinction de la frontière** à la limite.

### Gate G2 — RouteII implique Non-Vide

Selon le choix de RouteII :

* Si `RouteII = RouteIIAt` : **RouteII(λ) ⇔ N(λ)** (Fil direct).
* Si `RouteII = RouteIIApplies` : **RouteII(λ) ⇒ N(λ)** (Axiome ou lemme local).

### Gate G3 — Incompatibilité

> **(E(λ) ∧ N(λ)) ⇒ ⊥**

Une frontière ne peut être à la fois vide et non-vide.

### Gate G4 — Kleene Bridge (Continuité ⇒ Point Fixe)

*Correspondance :* Schéma utilisé dans `structural_escape_explicit`.

> **Cont(λ) ∧ (Inv ∧ LimitOp=Union) ⇒ Fix(λ)**

Si l'opérateur respecte la continuité (au sens requis), alors la limite canonique est un point fixe de F.

### Gate G5 — Fixpoint ⇒ Admissible (Optionnel)

Utile si la version de RouteII exige l'admissibilité ou la fermeture.

> **Fix(λ) ∧ Inv ⇒ Adm(λ)**

*Note : Pour l'escape (¬Cont), ce gate n'est pas toujours requis, le conflit "Fix + AbsBefore ⇒ Collapse" suffit souvent.*

---

## 4. Circuits Cibles : Trilemme et Escape

### (A) Trilemme (Forme "Pure")

Si on branche `RouteIIAt` :

1. `AbsBefore(ω) ⇒ E(ω)` (Collapse via G1)
2. `RouteIIAt(ω) ⇔ N(ω)` (Définition G2)
3. `(E ∧ N) ⇒ ⊥` (Conflit G3)

**Résultat :**
> **(AbsBefore(ω) ∧ RouteIIAt(ω) ∧ Inv) ⇒ ⊥**

En version "trilemme", on ajoute souvent `OmegaAdmissible` ou une contrainte de design, mais le noyau logique contradictoire reste **E ∧ N**.

### (B) Structural Escape (¬Cont)

On ajoute le pont de Kleene (G4) :

1. `Cont ⇒ Fix`
2. `Fix` force à vivre avec l'itération canonique (donc dans le monde de G1).
3. Si on impose RouteII (donc N), on retombe sur `E ∧ N`.

**Schéma plat :**

* `(AbsBefore(λ) ∧ SuccLimit(λ) ∧ LimitOp=Union ∧ Inv) ⇒ E(λ)`
* `RouteII(λ) ⇒ N(λ)`
* `Cont(λ) ∧ Inv ∧ LimitOp=Union ⇒ Fix(λ)`
* `(E(λ) ∧ N(λ)) ⇒ ⊥`

**Résultat (Résolution) :**
> **(AbsBefore(λ) ∧ SuccLimit(λ) ∧ LimitOp=Union ∧ Inv ∧ RouteII(λ)) ⇒ ¬Cont(λ)**

C'est la lecture "architecturale" : si l'on veut un système ouvert (`RouteII`) avec absorption antérieure, la continuité (au sens de Kleene) **doit casser**. Ce n'est pas un accident, c'est une contrainte de design.

---

## 5. Le Menu Architectural ("Troisième Option")

L'impossibilité (G1 + G2 + G3) révèle les options de design disponibles.
Pour maintenir `N(λ)` (Frontière active) dans un contexte Union-Limit, il faut casser **au moins une** des conditions d'entrée de G1 :

1. **Refuser l'absorption avant λ** (`¬AbsBefore(λ)`).
2. **Modifier la LimitOp** (Passer à un Jump ou une complétion non-canonique, `LimitOp ≠ Union`).
3. **Modifier les invariants** (Changer la définition de frontière ou la discipline d'injection pour invalider `Inv`).

C'est ici que réside le choix architectural.

## 6. Verdict sur la Thèse

La proposition est **Vraie**.

Sous `LimitOp=Union` et les invariants de collapse, **l'absorption avant λ rend incompatible la persistance d'une frontière non-vide à λ**.

Pour préserver une frontière active, on doit soit empêcher l'absorption passée, soit changer la nature de la limite (Jump), soit altérer la structure même de la frontière.
