# Collatz Route II — Option 2 : Barrière Drift Uniforme

Document de travail — Version arithmétique (sans log, sans probabilités)

---

## 0) Motivation

L'Option 2 remplace la barrière 2-adique (V1.x) par une contrainte de **drift uniforme** formulée en arithmétique discrète.

Avantage : cette approche **voit ℕ** (via la croissance/bornitude), contrairement à l'approche 2-adique pure qui ne distingue pas ℕ de ℤ₂.

---

## 1) Cadre : orbite, valuations, sommes partielles

On travaille sur `OddNat` (impairs positifs).

### Orbite

* `n_0 = n`
* `n_{k+1} = T*(n_k)`

### Valuations

* `a_k = v2(3*n_k + 1)` (donc `a_k >= 1`)
* `n_{k+1} = (3*n_k + 1) / 2^{a_k}`

### Sommes partielles

* `A_k = a_0 + a_1 + ... + a_{k-1}` (donc `A_0 = 0`)

### Inégalité structurante

En itérant la définition :

* `n_k = (3^k * n_0 + S_k) / 2^{A_k}`

où `S_k >= 0` est un entier construit à partir des `A_i`.

Conséquence (borne drift pure) :

* `n_k >= (3^k * n_0) / 2^{A_k}`

Donc si `A_k` est "trop petit" relativement à `k`, alors `n_k` explose.

---

## 2) Contraction par blocs : la paire (p, q)

### Choix des paramètres

Choisir des entiers `p, q >= 1` tels que :

* `2^p > 3^q`

Exemple : `(p, q) = (12, 7)` car `2^12 = 4096 > 3^7 = 2187`.

### Somme de valuations sur un bloc

* `B_j = A_{j+q} - A_j = a_j + ... + a_{j+q-1}`

### Lemme L1 (BlockContraction)

Il existe une constante explicite `C(q)` telle que :

* `n_{j+q} <= (3^q / 2^{B_j}) * n_j + C(q)`

En particulier, si `B_j >= p`, alors :

* `n_{j+q} <= (3^q / 2^p) * n_j + C(q)`

et le facteur multiplicatif est strictement < 1.

Pour `(p,q) = (12,7)`, le facteur vaut `2187/4096 < 0.534`.

---

## 3) Propriété P(U) : Drift Uniforme

### Définition (BlockDrift)

Fixer une paire `(p,q)` avec `2^p > 3^q`.

P(U; p,q) : "pour toute orbite contenue dans U, il existe un rang `J` tel que pour tout `j >= J`, on a `B_j >= p`".

### Interprétation

Au-delà d'un certain temps, **chaque bloc de q étapes** a au moins `p` divisions par 2 au total.

---

## 4) Lemmes de la chaîne

### Lemme L2 (EventualBound)

Si `B_j >= p` pour tout `j >= J`, alors `sup_{k >= J} n_k` est borné explicitement.

**Preuve sketch** : Le facteur de contraction `(3^q / 2^p) < 1` fait décroître `n` par blocs jusqu'à ce qu'il soit dominé par la constante `C(q)`.

### Lemme L3 (BoundedInvariantImpliesCycle)

Si U est forward-invariant, non vide, évite 1, et toutes ses orbites sont bornées, alors il existe un cycle non trivial dans `OddNat`.

**Preuve sketch** : Orbite bornée + infinite + dans ℕ discret ⟹ cycle par pigeonhole.

---

## 5) Bifurcation complète : Cycle vs Divergence

Pour un invariant `U ⊆ OddNat`, `U ≠ ∅`, `1 ∉ U`, `T*(U) ⊆ U`, tout contre-exemple doit réaliser l'un des deux :

* **(C) Cas cycle** : orbite ultimement périodique (bornée)
* **(D) Cas divergence** : orbite avec `n_k → +∞`

### Structure Route II complète

```
Invariant U non trivial évitant 1
            ↓
    ┌───────┴───────┐
    ▼               ▼
  (C) Cycle     (D) Divergence
    ↓               ↓
  P_cyc          P_div(δ)
    ↓               ↓
  O1b-cyc        O1b-div (D2)
    ↓               ↓
    ⊥               ⊥
```

---

## 6) Bras (C) : Cycles

### Propriété forcée P_cyc

Orbite bornée + forward-invariant + évite 1 ⟹ cycle non trivial existe (L3).

### Barrière O1b-cyc : Pas de cycle non trivial

**Énoncé** : Il n'existe aucun cycle de T* dans OddNat autre que {1}.

**Contrainte diophantienne** : Un cycle de longueur L satisfait :

* `n * (2^{A_L} - 3^L) = M`

avec M > 0 très structuré. Cela force `2^{A_L} > 3^L` et des congruences fortes.

**Statut** : Vérifié computationnellement jusqu'à des bornes énormes, mais pas prouvé en général.

---

## 7) Bras (D) : Divergence

### Propriété forcée P_div(δ)

**Définition** : P_div(U; p,q,δ) = "il existe une orbite dans U et δ > 0 tels que pour tout N assez grand :

* `#{ j < N : B_j ≤ p-1 } ≥ δ N`"

Autrement dit : une **proportion uniforme** de blocs ont une somme de valuations trop faible.

### Pourquoi P_div est forcée par divergence

Si presque tous les blocs vérifiaient `B_j ≥ p`, le mécanisme de contraction (L1) empêcherait `n_k → ∞`.

Donc une orbite divergente doit **battre la contraction** via une fréquence positive de blocs expansifs.

### Barrière O1b-div (D2) : Récurrence de blocs contractants

**Objectif D2** : Prouver qu'il existe R(p,q) tel que :

> Toute orbite dans OddNat évitant 1 contient **infiniment souvent** des segments de R blocs consécutifs avec `B_j ≥ p`.

**Conséquence** : Ces épisodes de forte contraction interdisent la fuite `n_k → ∞`.

### Lemme D2 (RecurrentContraction)

Pour (p,q) = (12,7), il existe R tel que pour toute orbite (n_k) dans OddNat évitant 1, il existe infiniment de j avec les R blocs consécutifs B_j, B_{j+1}, ..., B_{j+R-1} tous ≥ p.

**Statut** : Non prouvé.

---

## 8) Résumé des deux bras

| Bras | Propriété forcée | Barrière | Statut |
|------|------------------|----------|--------|
| **(C) Cycle** | Orbite bornée → cycle | O1b-cyc : pas de cycle | Vérifié computationnellement |
| **(D) Divergence** | P_div : densité δ de blocs expansifs | O1b-div (D2) : récurrence contractante | Non prouvé |

---

## 9) Comparaison des approches

| Approche | Objet interdit | Gap principal |
|----------|----------------|---------------|
| V1.x (2-adique) | Piège universel | Ne s'applique pas aux vrais contre-exemples |
| V2 (chemins projectifs) | Chemin compatible | Existe dans ℤ₂ |
| Option 2 (bifurquée) | Cycle (C) + Divergence (D) | O1b-cyc + O1b-div (D2) |

---

## 10) Valeur de cette approche

Option 2 bifurquée :

1. **Voit ℕ** (via la croissance/bornitude)
2. **Couvre les deux cas** (cycle ET divergence)
3. Propose des formes **P_cyc** et **P_div** explicites et testables
4. Donne des lemmes **directement formalisables** (L1-L3, D2)
5. Concentre la difficulté sur des objets **arithmétiques**

C'est une **réduction complète** du problème Collatz vers :
- O1b-cyc : "Pas de cycle non trivial"
- O1b-div (D2) : "Récurrence de blocs contractants"

---

## 11) Prochaines étapes

1. Formaliser L1, L2, L3 en Lean
2. Formaliser P_div et le lemme de densité
3. Attaquer D2 (récurrence de blocs contractants)
4. Explorer les contraintes diophantiennes sur les cycles (pour O1b-cyc)
