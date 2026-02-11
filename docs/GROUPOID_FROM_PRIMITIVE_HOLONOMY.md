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

> **(C1) + (C2) ⟺ groupoïde sur les fibres.**

### ⟹ : (C1) + (C2) donne un groupoïde

Par `sem_comp` et `sem_id` :

- `Hol(η) = T_{comp(p,q)} ∘ T_{id}† = T_p ∘ T_q`
- `Hol(ε) = T_{comp(q,p)} ∘ T_{id}† = T_q ∘ T_p`

Donc C2 donne : `T_p ∘ T_q = Δ_h` et `T_q ∘ T_p = Δ_k`.

**Lemme.** Dans `Rel`, `R ∘ S = Δ_X` et `S ∘ R = Δ_Y` ⟹ `R` bijection et `S = R†`.

*Preuve.* Supposons `R(x, y₁)` et `R(x, y₂)` avec `y₁ ≠ y₂`. Par `R ∘ S = Δ(x,x)` : ∃ `y₀` avec `R(x, y₀) ∧ S(y₀, x)`. Alors `S(y₀, x) ∧ R(x, y₁)` donne `(S ∘ R)(y₀, y₁)`. Si `y₀ ≠ y₁`, contradiction avec `S ∘ R = Δ`. Donc `y₀ = y₁`. Même argument : `y₀ = y₂`. Donc `y₁ = y₂` — `R` est **déterministe**. Les autres propriétés (totalité, injectivité, surjectivité) suivent symétriquement. `S = R†` est alors forcé. ∎

Donc `T_p` est une bijection, `T_q = T_p†`, et avec `sem_id` + `sem_comp` : groupoïde. ∎

### ⟸ : groupoïde donne (C1) + (C2)

Si chaque `T_p` est une bijection :

- **(C1)** : prendre `q` tel que `T_q = T_p†` (= `T_p⁻¹`). Alors `T_p ∘ T_q = Δ = T_{id}` et `T_q ∘ T_p = Δ = T_{id}`, donc par `sem_comp` les compositions ont le même transport que l'identité — poser les déformations correspondantes.
- **(C2)** : `Hol(η) = T_{comp(p,q)} ∘ T_{id}† = T_p ∘ T_q = Δ`. ∎

## Attention : platitude universelle ≠ groupoïde

`∀ α, Hol(α) = Δ` est **strictement plus fort** qu'un groupoïde.

- `Hol(α : p ⇒ q) = T_p ∘ T_q† = Δ` force `T_p = T_q` : les chemins déformation-équivalents ont le **même** transport.
- Un groupoïde n'exige **pas** cela — deux bijections distinctes composées ne donnent pas la diagonale.

| Condition | Résultat |
|---|---|
| C1 + C2 (platitude sur unités) | **Groupoïde** |
| C1 + platitude universelle | Groupoïde **à transport indépendant du chemin** (plat) |

## Redéfinition

> **Un groupoïde est une sémantique relationnelle sur une 2-catégorie réversible dont l'holonomie est plate sur les 2-cellules d'unité.**

La décomposition sépare :

| Aspect | Condition | Porte sur |
|---|---|---|
| **Topologique** | Réversibilité homotopique (C1) | HistoryGraph |
| **Géométrique** | Platitude sur les unités (C2) | Semantics |
