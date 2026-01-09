# Collatz (version impaire) — Objectifs de recherche Route II

Document de travail — Research Objectives (sans LaTeX)

---

## 0) Cadre : dynamique impaire T*

On travaille sur les entiers impairs positifs.

* Domaine : `OddNat = { n ∈ N : n est impair et n >= 1 }`.

* Définition de la valuation 2-adique :
  * `v2(m)` est le plus grand `a >= 0` tel que `2^a` divise `m`.

* Définition de la dynamique impaire :
  * Pour `n` impair, `T*(n) = (3n + 1) / 2^{v2(3n + 1)}`.
  * Alors `T*(n)` est impair.

* Ensemble absorbant :
  * `B = {1}` (cycle trivial dans T*).

* Itérées :
  * `T*^0(n) = n`
  * `T*^{k+1}(n) = T*(T*^k(n))`.

---

## 1) Deux chaînes : monotone et anti-monotone

### 1.1) Chaîne monotone (absorption en temps <= k)

Définir :

* `X_k = { n ∈ OddNat : ∃ i <= k, T*^i(n) = 1 }`.

Donc `X_k ⊆ X_{k+1}` (monotone croissante).

Définir aussi le temps d'entrée minimal (partiel) :

* `hit(n) = min { i : T*^i(n) = 1 }` si un tel `i` existe.

Alors `n ∈ X_k` équivaut à `hit(n)` défini et `hit(n) <= k`.

### 1.2) Chaîne anti-monotone (complément)

Définir :

* `U_k = OddNat \ X_k`.

Donc `U_{k+1} ⊆ U_k` (anti-monotone décroissante).

Interprétation :

* `U_k` est l'ensemble des impairs qui n'ont pas atteint 1 en `k` étapes.

Le "palier" conceptuel (non terminal) est :

* `U_k = U_{k+1} != ∅`.

C'est exactement un point fixe non vide de la dynamique "ne pas atteindre 1 en temps fini".

---

## 2) Hauteur de vol

Définir la hauteur maximale avant absorption (partielle) :

* Si `hit(n)` existe, alors
  * `H(n) = max { T*^i(n) : 0 <= i <= hit(n) }`.

Sinon `H(n)` est indéfinie (ou `= +∞` selon convention, mais on évite ici).

---

# Objectif O1 : Anti-palier global

## Énoncé O1 (forme directe)

Montrer qu'il n'existe aucun ensemble `U ⊆ OddNat` tel que :

1. `U` est non vide
2. `1 ∉ U`
3. `U` est forward-invariant sous `T*` : pour tout `n ∈ U`, `T*(n) ∈ U`

Autrement dit : aucun sous-système invariant non trivial ne peut éviter `{1}`.

## Conséquence logique de O1

Si O1 est vrai, alors il n'existe aucun palier non terminal de la chaîne `U_k`.

En particulier :

* Pour tout `n ∈ OddNat`, il existe `k` tel que `n ∈ X_k` (absorption en temps fini).
* Donc la conjecture Collatz impaire est vraie.

## Variante "palier" (forme Route II)

Montrer que :

* Pour tout `k`, si `U_k = U_{k+1}` alors `U_k = ∅`.

C'est équivalent à O1 via `U = U_k` (car `U_k = U_{k+1}` implique la forward-invariance de `U_k`).

---

# Objectif O2 : Profondeur -> Hauteur

## Énoncé O2 (forme opérationnelle)

Trouver une fonction explicite `F : N × N -> N` telle que :

* Pour tout `n ∈ OddNat` et tout `k ∈ N`,
  * si `n ∈ X_k` alors `H(n) <= F(n, k)`.

Interprétation : si on sait que `n` atteint 1 en <= k étapes de `T*`, alors la hauteur maximale de l'orbite avant absorption est contrôlée par une borne universelle calculable à partir de `(n, k)`.

## Pourquoi O2 est une vraie difficulté

* O2 demande une contrainte "archimédienne" (contrôle de tailles réelles/logarithmiques), pas seulement une compatibilité 2-adique.
* C'est le lieu naturel où interviennent les arguments de drift, mais sous une forme uniformisée (et sans hypothèse probabiliste).

## Variantes d'intensité

* **O2a (faible)** : existe `F(n,k)` quelconque, même très grande, mais explicitement définie.
* **O2b (structurelle)** : `H(n) <= n * G(k)` pour un `G : N -> N`.
* **O2c (forte)** : `H(n) <= R(k)` indépendante de `n` (probablement trop forte).

---

# Relation logique entre O1 et O2

* **O1 seul** => Collatz impaire (temps fini pour tous n), sans borne quantitative.
* **O2 seul** ne prouve pas l'absorption, mais donne un contrôle sur les excursions conditionnellement à l'absorption.
* **O1 + O2** => Collatz impaire + bornes explicites de "hauteur de vol".

---

# Statut (honnête)

| Objectif | Difficulté | Barrière requise |
|----------|------------|------------------|
| O1 | Fondamental | Ne peut pas être purement 2-adique (ℤ₂ admet des points fixes) |
| O2 | Archimédien | Requiert contrôle d'orbites exceptionnelles |

## Conclusion

O1 et O2 sont des formulations propres et uniformes, mais chacune encode une partie de la difficulté centrale de Collatz. Ce document sert d'interface de recherche : ce sont les deux briques minimales à attaquer pour "faire mordre" Route II sur ℕ.

---

# Lien avec les autres documents

* `CollatzRouteII_v1.2.md` : Framework famille B (barrière 2-adique) — documenté comme exploration, pas comme solution.
* Ce document : Objectifs de recherche formels, indépendants du framework V1.x.
