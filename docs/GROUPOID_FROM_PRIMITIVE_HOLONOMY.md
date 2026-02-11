# Groupoïde = Base réversible + Holonomie plate sur les unités

## Cadre

Soit `(P, Path, Deformation)` une 2-catégorie, `(S, sem)` une sémantique relationnelle (`sem_id`, `sem_comp`), `obs : S → V`, `target_obs : P → V`.

- **Transport** : `T_p : Relation (FiberPt h) (FiberPt k)`
- **Holonomie** : `Hol(α : p ⇒ q) = T_p ∘ T_q†`

## Conditions

### C1 — Réversibilité homotopique

> ∀ chemin `p : h → k`, ∃ `q : k → h` avec déformations `η : comp(p,q) ⇒ id_h` et `ε : comp(q,p) ⇒ id_k`.

### C2 — Platitude sur les 2-cellules d'unité

> `Hol(η) = Δ_h` et `Hol(ε) = Δ_k`.

## Théorème

> **(C1) + (C2) ⟹ groupoïde sur les fibres.**

La direction **⟸** n'est pas automatique : il faut produire des déformations η, ε dans le HistoryGraph à partir de l'égalité sémantique. Cela requiert une hypothèse de *complétude des déformations* (DeformationComplete).

### Reformulation packagée (≡ C1+C2)

La condition :

> ∀ p : h→k, ∃ (q : k→h) (η : comp(p,q) ⇒ id_h) (ε : comp(q,p) ⇒ id_k), Hol(η) = Δ_h ∧ Hol(ε) = Δ_k

est équivalente à C1+C2 (triviallement). Elle implique FibGrpd (`fwd`), mais **la réciproque FibGrpd ⟹ Packagée nécessite aussi DeformationComplete** (pour produire η, ε), car la condition mentionne des objets syntaxiques (déformations dans le HistoryGraph).

### ⟹ : (C1) + (C2) donne un groupoïde

Par `sem_comp` et `sem_id` :

- `Hol(η) = T_{comp(p,q)} ∘ T_{id}† = T_p ∘ T_q`
- `Hol(ε) = T_{comp(q,p)} ∘ T_{id}† = T_q ∘ T_p`

Donc C2 donne : `T_p ∘ T_q = Δ_h` et `T_q ∘ T_p = Δ_k`.

**Lemme.** Dans `Rel`, `R ∘ S = Δ_X` et `S ∘ R = Δ_Y` ⟹ `R` bijection et `S = R†`.

*Preuve.* Supposons `R(x, y₁)` et `R(x, y₂)` avec `y₁ ≠ y₂`. Par `R ∘ S = Δ(x,x)` : ∃ `y₀` avec `R(x, y₀) ∧ S(y₀, x)`. Alors `S(y₀, x) ∧ R(x, y₁)` donne `(S ∘ R)(y₀, y₁)`. Si `y₀ ≠ y₁`, contradiction avec `S ∘ R = Δ`. Donc `y₀ = y₁`. Même argument : `y₀ = y₂`. Donc `y₁ = y₂` — `R` est **déterministe**. Les autres propriétés (totalité, injectivité, surjectivité) suivent symétriquement. `S = R†` est alors forcé. ∎

Donc `T_p` est une bijection, `T_q = T_p†`, et avec `sem_id` + `sem_comp` : groupoïde. ∎

### ⟸ : groupoïde donne (C2), mais (C1) nécessite une hypothèse supplémentaire

Si chaque `T_p` est une bijection (groupoïde sur fibres) :

- **(C2)** : pour tout `q` avec `T_q = T_p†`, si `η : comp(p,q) ⇒ id_h` existe, alors `Hol(η) = T_{comp(p,q)} ∘ T_{id}† = T_p ∘ T_q = Δ`. ✅ Prouvé (`bwd_C2` dans le fichier Lean).
- **(C1)** : il faut produire `q`, `η`, et `ε` **dans le HistoryGraph**. On sait que `T_q = T_p†` donne `T_{comp(p,q)} = T_{id}` sémantiquement, mais **rien ne garantit l'existence d'une déformation** `comp(p,q) ⇒ id_h` dans une 2-catégorie abstraite. Cela requiert l'hypothèse de **complétude des déformations** (DeformationComplete) : si deux chemins ont le même transport, il existe une déformation entre eux. ⚠️

> **Sans DeformationComplete** : ⟸ vaut pour C2 mais pas pour C1.

## Attention : platitude universelle ≠ groupoïde

`∀ α, Hol(α) = Δ` est **strictement plus fort** qu'un groupoïde.

- `Hol(α : p ⇒ q) = T_p ∘ T_q† = Δ` force `T_p = T_q` : les chemins déformation-équivalents ont le **même** transport.
- Un groupoïde n'exige **pas** cela — deux bijections distinctes composées ne donnent pas la diagonale.

| Condition | Résultat |
|---|---|
| C1 + C2 (platitude sur unités) | **Groupoïde** |
| C1 + platitude universelle | Groupoïde **à transport indépendant du chemin** (plat) |

## Redéfinition

> **Un groupoïde émerge d'une sémantique relationnelle sur une 2-catégorie réversible dont l'holonomie est plate sur les 2-cellules d'unité.** (sens ⟹ ; le sens ⟸ nécessite DeformationComplete.)

La décomposition sépare :

| Aspect | Condition | Porte sur |
|---|---|---|
| **Topologique** | Réversibilité homotopique (C1) | HistoryGraph |
| **Géométrique** | Platitude sur les unités (C2) | Semantics |

---

## Quotient : émergence sans condition

Contrairement au groupoïde qui nécessite (C1)+(C2), le **quotient émerge toujours** de l'holonomie primitive.

### Construction

La relation `ProbeIndistinguishable` (indiscernabilité sous tous les tests holonomiques) est une équivalence par construction (réfl/sym/trans). Le quotient `FiberQuot` existe sans condition supplémentaire.

> **Le quotient canonique d'une fibre = l'espace des orbites sous l'indistinguabilité holonomique.**

### Trivialité

- **Quotient trivial** ⟺ la famille de probes est **séparante** : `∀ x ≠ y, ∃ test holonomique qui les distingue`
- **Quotient non-trivial** ⟺ ∃ `x ≠ y` indistinguables sous toutes les holonomies

### Lien avec le groupoïde

Le groupoïde (C1+C2) porte sur **une** sémantique. Le quotient (`ProbeSetoid`) porte sur une **famille** de sémantiques (`SemFamily` sur `CoeffCat`). Ce sont des niveaux différents, reliés par une **implication à sens unique** :

> **Groupoïde dans au moins un coefficient ⟹ quotient trivial.**

Car la self-holonomie `Δ` (qui existe dans tout groupoïde) est un test séparant : `Hol(α)(x,x) = True` mais `Hol(α)(y,x) = (y = x)`, donc `x ≠ y` sont distingués.

| Concept | Niveau | Condition |
|---|---|---|
| **Groupoïde** | Une sémantique | (C1) + (C2) |
| **Quotient trivial** | Famille de sémantiques | Probes séparantes |
| **Quotient non-trivial** | Famille de sémantiques | Probes non-séparantes |

---

## Correspondance avec HoTT

| Holonomie primitive | HoTT |
|---|---|
| Base `P` | Type `A : U` |
| `Path(h, k)` | Type d'identité `h =_A k` |
| `Deformation(p, q)` | Identité entre chemins `p =_{h=k} q` |
| Fibre `FiberPt(h)` | Type dépendant `B(h)` |
| Transport `T_p` (relation) | `transport^B(p) : B(h) → B(k)` (fonction) |
| Holonomie `Hol(α)` | `transport^B(p) ∘ transport^B(q)⁻¹` |

### C1 et C2 sont automatiques en HoTT

**C1** : l'inversion `p⁻¹` et les unités `p · p⁻¹ = refl` sont des théorèmes (par induction sur `refl`). Pas besoin de les postuler.

**C2** : `transport^B` respecte les 2-chemins, donc `η : p · p⁻¹ = refl` implique `transport^B(p · p⁻¹) = transport^B(refl) = id`. L'holonomie est automatiquement plate.

### Conséquence : notre cadre est strictement plus général que HoTT

HoTT **présuppose** la fonctionnalité du transport. Nos conditions (C1)+(C2) sont les hypothèses exactes que HoTT a encodées dans sa fondation (induction sur `refl` + fonctorialité du transport).

Notre cadre part de **relations** (plus général que fonctions). Quand (C1)+(C2) échouent, on accède à des situations — holonomie non-plate, base irréversible — que HoTT ne peut pas exprimer.

> **HoTT = cas particulier de notre cadre où (C1) et (C2) sont automatiques.**

Note : HoTT produit des **∞-groupoïdes** (toutes les dimensions). Notre cadre capture le niveau 1-tronqué (2-cellules, pas de 3-cellules).
