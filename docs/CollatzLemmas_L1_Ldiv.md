# Collatz Lemmas L1 et Ldiv — Énoncés Canoniques

Document de spécification — Lean-ready (sans rationnels, arithmétique entière)

---

## Paramètres fixés

* `q = 7` (longueur de bloc)
* `p = 12` (seuil de contraction)
* Vérification : `2^12 = 4096 > 3^7 = 2187` ✓
* Constante : `C_7 = 3^7 - 1 = 2186`

---

## 1) Définitions préliminaires

### Domaine

```
OddNat = { n : Nat | n % 2 = 1 ∧ n >= 1 }
```

### Valuation 2-adique

```
v2 : Nat+ → Nat
v2(m) = max { k | 2^k divise m }
```

### Dynamique impaire

```
a : OddNat → Nat
a(n) = v2(3*n + 1)

Tstar : OddNat → OddNat
Tstar(n) = (3*n + 1) / 2^(a(n))
```

### Itérées

```
Tstar_iter : Nat → OddNat → OddNat
Tstar_iter(0, n) = n
Tstar_iter(k+1, n) = Tstar(Tstar_iter(k, n))
```

### Suite des valuations

Pour une orbite `n_k = Tstar_iter(k, n_0)` :

```
a_k = a(n_k)
```

### Somme de valuations sur un bloc

```
B : Nat → Nat
B(j) = a_j + a_{j+1} + ... + a_{j+6}   -- somme de 7 termes
```

Équivalent :

```
B(j) = sum_{i=0}^{6} a_{j+i}
```

---

## 2) Lemme L1 : BlockContraction

### Énoncé

Pour tout `n_0 ∈ OddNat`, pour tout `j ∈ Nat` :

> Si `B(j) >= 12` alors `4096 * n_{j+7} <= 2187 * n_j + 2186`

### Forme générale (paramétrique)

Pour `p, q : Nat` avec `2^p > 3^q`, et `C_q = 3^q - 1` :

> Si `B(j) >= p` alors `2^p * n_{j+q} <= 3^q * n_j + C_q`

### Preuve (sketch)

1. Dérouler q étapes de Tstar
2. À chaque étape : `n_{k+1} = (3*n_k + 1) / 2^{a_k}`
3. En majorant (ignorer les divisions intermédiaires) :
   * `n_{j+q} <= (3^q * n_j + S) / 2^{B(j)}`
   * où `S <= 3^q - 1`
4. Si `B(j) >= p`, alors `2^{B(j)} >= 2^p`
5. Donc `2^p * n_{j+q} <= 3^q * n_j + (3^q - 1)`

---

## 3) Lemme Ldiv-0 : ExpansiveBlocksNecessary

### Définition : Divergence

Une orbite `(n_k)` **diverge** si :

```
∀ M : Nat, ∃ k : Nat, n_k >= M
```

### Énoncé

Pour toute orbite `(n_k)` dans OddNat évitant 1 :

> Si `(n_k)` diverge, alors `∀ J : Nat, ∃ j >= J, B(j) <= 11`

### Interprétation

Une orbite divergente a **infiniment de blocs expansifs** (blocs de 7 étapes avec moins de 12 divisions totales par 2).

### Preuve (sketch, par contraposée)

1. Supposer le contraire : `∃ J, ∀ j >= J, B(j) >= 12`
2. Par L1 : à partir du rang J, chaque bloc de 7 étapes contracte
3. Donc `n_{J+7k}` est ultimement borné (décroissance affine avec facteur < 1)
4. Contradiction avec divergence

---

## 4) Résumé

| Lemme | Énoncé |
|-------|--------|
| **L1** | `B(j) >= 12 ⟹ 4096 * n_{j+7} <= 2187 * n_j + 2186` |
| **Ldiv-0** | `divergence ⟹ infiniment de j avec B(j) <= 11` |

---

## 5) Statut

| Lemme | Difficulté | Statut |
|-------|------------|--------|
| L1 | Mécanique (inégalités Nat) | À formaliser |
| Ldiv-0 | Logique (contraposée de L1) | À formaliser |

---

## 6) Prochaines étapes

1. Formaliser L1 en Lean
2. Formaliser Ldiv-0 en Lean
3. Intégrer dans le framework Option 2 (bifurcation cycle/divergence)
