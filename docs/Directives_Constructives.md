# Directives Lean (profil constructif et calculable)

Objectif: toute nouvelle contribution doit rester **computable** (pas de `noncomputable`) et **constructive** (pas de `classical`, pas de dépendance à `Classical.choice`).

---

## 1) Interdictions (blocantes)

### 1.1 Non‑computable (interdit)

- Interdit: `noncomputable section`
- Interdit: `noncomputable def`
- Interdit: toute dépendance à une définition non‑computable importée “par commodité”.

### 1.2 Classique (interdit)

- Interdit: `open Classical`
- Interdit: `classical` (commande / tactic)
- Interdit: `by_contra`
- Interdit: `by_cases h : P` **sans** hypothèse explicite `Decidable P` (sinon Lean bascule via `Classical.propDecidable`).
- Interdit: `Classical.choice`, `Classical.decPred`, `Classical.propDecidable` **dans la liste** de `#print axioms` d’un nouveau théorème.

---

## 2) Règles de conception (obligatoires)

### 2.1 Tout ce qui est “vérification” doit être Bool

- Les checkers doivent être des fonctions en `Bool` (ex: `ChecksDerivation : ... → Bool`, `ChecksWitness : ... → Bool`).
- La couche `Prop` ne doit pas “re‑cacher” une décision par des axiomes; on passe par `decide` seulement si on a une `Decidable` explicite.

### 2.2 Toute dichotomie doit être paramétrée par la décidabilité

Au lieu de:

```lean
by_cases h : P
```

faire:

```lean
variable (decP : Decidable P)
-- puis
by_cases h : P
```

ou réécrire la preuve en évitant la dichotomie (souvent possible via un témoin `∃` / une appartenance `∈`).

### 2.3 Pas de “choix” implicite: produire les témoins

- Interdit: `choose`, `Classical.choose`, `Classical.choice`, ou toute technique “il existe donc on choisit”.
- À la place: transporter des témoins déjà présents (`rcases h with ⟨w, hw⟩`) ou définir explicitement le témoin (ex: une constante, `0`, `Nat.pair`, etc.).

### 2.4 Privilégier les formes “constructives” des énoncés

- Pour `S = ∅`, préférer `Set.eq_empty_iff_forall_notMem` (preuve directe).
- Pour `S ≠ ∅`, préférer `Set.nonempty_iff_ne_empty` **si** on a déjà `Set.Nonempty S`; sinon construire un élément explicitement.
- Pour les disjonctions “P ∨ Q”, préférer une forme “not‑all” lorsque c’est le bon contenu (ex: `¬ (P ∧ Q ∧ R)` plutôt que `¬P ∨ ¬Q ∨ ¬R` si la disjonction force du classique).

---

## 3) Check‑list “zéro classique / zéro noncomputable” (avant merge)

### 3.1 Recherche textuelle (doit être vide)

Commande:

```sh
rg -n "\\bnoncomputable\\b|\\bclassical\\b|by_contra\\b|Classical\\.(choice|decPred|propDecidable)" RevHalt
```

### 3.2 Audit d’axiomes (doit exclure `Classical.choice`)

- Ajouter le théorème dans `RevHalt/Diagnostics/AxiomsReport.lean` si c’est un point central.
- Régénérer le rapport:

```sh
lake env lean RevHalt/Diagnostics/AxiomsReport.lean
```

Critère: dans `#print axioms <theorem>`, ne pas voir `Classical.choice` / `Classical.decPred` / `Classical.propDecidable`.

### 3.3 Build minimal

```sh
lake build
```

---

## 4) Politique sur l’existant (pour éviter la dérive)

- Les fichiers déjà “classiques” peuvent exister, mais:
  - aucune nouvelle dépendance à `Classical.*` ne doit être introduite dans le noyau,
  - toute nouvelle preuve doit viser une version paramétrée (ex: `DecidablePred`, `DecidableEq`, checkers Bool) plutôt qu’une version “classical”.

