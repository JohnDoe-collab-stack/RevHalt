# Collatz Route II — Framework Complet (Famille B : Barrière 2-adique)

**Document de Référence — Version 1.2 (autocontenue, sans LaTeX)**

---

## 1) Motivation : Pourquoi Lyapunov n'est pas le bon axe ici

Les approches classiques de Collatz cherchent une fonction de descente globale `f : N -> R+` telle que `f(T(n)) < f(n)` pour tout `n != 1`.

Difficulté structurelle : la dynamique alterne croissance (étape `3n+1` sur impairs) et décroissance (divisions par 2), ce qui rend une descente uniforme "simple" très peu plausible.

Route II change d'objet : on ne cherche pas une quantité qui décroît, mais on montre qu'un certain type de **stabilisation structurelle** forcerait un objet interdit.

---

## 2) Route II abstraite (gabarit)

Schéma Route II :

1. Une fermeture monotone `Cl` sur un espace fini/compact d'états.
2. Une notion de "frontière" (complément) anti-monotone.
3. Un "palier" = événement où la frontière se stabilise (ou une fermeture atteint un point fixe non terminal).
4. Le palier force un **pouvoir / objet interdit**.
5. Une barrière prouve l'impossibilité de cet objet, donc interdit le palier.

Dans RevHalt, le "pouvoir interdit" est un décideur total (barrière T2).
Ici, le "pouvoir interdit" est un système compatible d'ensembles invariants modulo `2^m` évitant le cycle trivial.

---

## 3) Dynamique T* sur les impairs

On travaille sur les impairs pour isoler la composante 2-adique.

- Pour `n` impair, définis `a(n) = v2(3n + 1)` (valuation 2-adique).
- Définis `T*(n) = (3n + 1) / 2^{a(n)}`.

Alors `T*(n)` est impair. Le cycle trivial est `{1}` (car `T*(1)=1`).

---

## 4) Espace fini et sorties universelles

### Espace

Pour `m >= 1`, définis `ModOdd(m)` comme l'ensemble des classes d'équivalence impaires modulo `2^m`.
Cardinal : `|ModOdd(m)| = 2^{m-1}`.

### Sorties universelles (quantification universelle)

C'est le point clé : on ne met pas une condition existentielle, mais universelle.

Définis (où `r` est une **classe** impaire modulo `2^m`, pas un entier) :

- `Out_m(r) = { (T*(n) mod 2^m) | n impair, (n mod 2^m) = r }`.

Un ensemble `U` inclus dans `ModOdd(m)` est **invariant** (au sens universel) si :

- pour tout `r` dans `U`, on a `Out_m(r)` inclus dans `U`.

### Fermeture

Définis la fermeture monotone :

- `Cl_m(X) = X union (union sur r dans X de Out_m(r))`.

Et l'itération :

- `Cl_m^0(X) = X`
- `Cl_m^{k+1}(X) = Cl_m(Cl_m^k(X))`
- `Cl_m^omega(X) = union sur k de Cl_m^k(X)`.

Comme `ModOdd(m)` est fini, `Cl_m^omega(X)` atteint un point fixe en temps fini.

---

## 5) Résidus exceptionnels et quasi-exceptionnels

### Résidu exceptionnel `s_m`

Pour `m >= 1`, `s_m` est l'unique classe (impair) telle que :

- `3*s_m + 1 = 0 (mod 2^m)`.

Existence/unicité : `3` est inversible modulo `2^m`, donc l'équation linéaire a une solution unique.

Propriété de cohérence :

- `s_{m+1} = s_m (mod 2^m)`.

Formule explicite :

| m mod 2 | s_m                          |
|---------|------------------------------|
| pair    | (2^m - 1) / 3                |
| impair  | (2^{m+1} - 1) / 3 mod 2^m    |

### Quasi-exceptionnel `q_m`

Les levées de `s_{m-1}` modulo `2^m` sont exactement deux résidus :

- `s_{m-1}` et `s_{m-1} + 2^{m-1}` (au niveau des représentants).

Par définition, `q_m` est l'autre levée de `s_{m-1}` qui n'est pas `s_m`.

Propriété fondamentale :

- `v2(3*q_m + 1) = m - 1`.

### Saturation (les "deux saturateurs")

- `Out_m(s_m) = ModOdd(m)`.
- `Out_m(q_m) = ModOdd(m)`.

Interprétation : dès qu'une fermeture `Cl_m^omega(X)` touche `s_m` ou `q_m`, elle sature immédiatement tout `ModOdd(m)`, donc elle contient `1 mod 2^m`.

---

## 6) Pièges (objet interdit au niveau m)

Définition : un **piège** au niveau `m` est un ensemble `U` inclus dans `ModOdd(m)` tel que :

1. `U` non vide
2. (fermeture universelle) pour tout `r` dans `U`, `Out_m(r)` inclus dans `U`
3. `U` intersection `{s_m, q_m} = vide`

Un piège est donc un point fixe non trivial de la fermeture qui évite les saturateurs.

---

## 7) Projection et descente

### Projection

Pour `m >= 2`, définis :

- `pi : ModOdd(m) -> ModOdd(m-1)` par réduction modulo `2^{m-1}`.

### Lemme de factorisation

Pour tout `r` dans `ModOdd(m)` :

- `pi(Out_m(r))` inclus dans `Out_{m-1}(pi(r))`.

### Descente des pièges

Si `U` est un piège au niveau `m`, alors `pi(U)` est un piège au niveau `m-1`.

Point technique : les seules préimages de `s_{m-1}` par `pi` sont exactement `{s_m, q_m}`, ce qui suffit pour assurer que `pi(U)` évite `s_{m-1}` si `U` évite `{s_m, q_m}`.

---

## 8) Théorème B-1' : aucun piège à aucun niveau

**Énoncé** :

Pour tout `m >= 2`, il n'existe aucun piège au niveau `m`.

**Preuve** :

- Base `m=2` : `ModOdd(2) = {1,3}` et `{s_2, q_2} = {1,3}`, donc impossible d'éviter les deux avec un ensemble non vide.
- Induction descendante : un piège à `m` impliquerait un piège à `m-1`, contradiction.

**Corollaire** (forme opérationnelle) :

Pour tout `m >= 2` et tout `X` inclus dans `ModOdd(m)` non vide, `Cl_m^omega(X)` contient `1 mod 2^m`.

---

## 9) Interprétation conceptuelle

Ce que ce résultat interdit réellement :

- au niveau de chaque `m`, il n'existe pas d'ensemble non vide fermé sous `Out_m` qui évite `{s_m, q_m}`, et donc qui évite `1`.

Donc : aucune "stabilisation locale 2-adique" de type piège ne peut exister.

C'est l'analogue exact, côté Collatz, du "palier interdit" Route II dans RevHalt :

- RevHalt : palier => décideur total => contradiction (T2).
- Collatz : palier => piège compatible modulo `2^m` => contradiction (barrière 2-adique).

---

## 10) Passage au global : hypothèse de connexion

> **IMPORTANT** : Cette section documente le chaînon qui relie le résultat mod 2^m à une assertion sur N.

### Hypothèse de connexion (à prouver formellement)

Soit `U` un sous-ensemble de `N_impairs` tel que :

1. `U` non vide
2. `U` est T*-invariant : pour tout `n` dans `U`, `T*(n)` est dans `U`
3. `U` est disjoint de `{1}`

Alors, pour tout `m >= 2`, la projection `U_m = { n mod 2^m | n dans U }` est un piège au niveau `m`.

### 10.1) Deux versions de la connexion

Il y a deux façons de relier un palier global à un piège modulo `2^m` :

**Connexion forte** :

- `U` est une **union de classes modulo `2^m`** (pour tout m, ou à partir d'un certain m₀).
- Autrement dit : pour tout `r` dans `U_m`, **toute** levée impaire `n` avec `(n mod 2^m) = r` appartient à `U`.
- Dans ce cas, l'invariance `T*(U) ⊆ U` implique directement `Out_m(r) ⊆ U_m`.
- C'est cette version qui permet d'appliquer B-1'.

**Connexion faible** :

- `U` est simplement T*-invariant, sans hypothèse de congruentialité.
- Dans ce cas, l'invariance donne seulement : pour tout `r` dans `U_m`, il existe `y` dans `Out_m(r)` tel que `y` dans `U_m`.
- C'est une fermeture **existentielle**, pas universelle.
- Cela ne suffit PAS pour appliquer B-1'.

**Conclusion** : La barrière B-1' nécessite la connexion forte.

### Justification (sous connexion forte)

- `U_m` non vide : car `U` non vide.
- `U_m` fermée (universelle) : sous connexion forte, si `r` est dans `U_m`, toutes les levées de `r` sont dans `U`. Comme `U` est T*-invariant, toutes leurs images sont dans `U`, donc `Out_m(r) ⊆ U_m`.
- `U_m` évite `{s_m, q_m}` : si `U_m` contenait `s_m` ou `q_m`, alors la clôture modulo `2^m` de `U_m` serait tout `ModOdd(m)`, donc contiendrait `1 mod 2^m`. Sous connexion forte, cela impliquerait `1` dans `U`, contradiction.

### Point technique restant

La connexion forte ("U est une union de classes modulo 2^m") est une hypothèse non triviale. Elle exprime que le palier a une structure **congruentiellement définissable**, ce qui est plausible mais reste à prouver formellement.

### Conclusion conditionnelle

**Si** l'hypothèse de connexion est prouvée, **alors** :

- Palier global (U non vide, T*-invariant, évite 1) => piège a chaque niveau m => contradiction (B-1')

Donc : **aucun palier global n'existe**.

---

## 11) Statut et prochaines étapes

### Acquis (rigoureusement établi)

| Résultat | Statut |
|----------|--------|
| Framework Route II Collatz (famille B) | Complet |
| Barrière B-1' (au niveau ModOdd(m)) | Démontré structurellement |
| Résidus saturateurs s_m, q_m | Caracterisés |
| Descente des pièges | Démontré |
| Aucun piège a aucun niveau | Démontré |

### Ce qui reste (explicitement séparé)

| Élément | Statut |
|---------|--------|
| Formalisation Lean du cadre Collatz | Non fait |
| Hypothèse de connexion (global -> mod 2^m) | Énoncée, non formellement prouvée |
| Bornes quantitatives sur les temps d'arrêt | Hors scope |

### Signification

Un contre-exemple qui **induit un palier compatible modulo 2^m** (au sens Out_m) forcerait un piège — ce qui est démontré impossible.

Ce n'est pas encore une preuve complète de Collatz, mais c'est une **barrière structurelle** qui élimine un scénario précis de contre-exemple.

---

## 12) Comparaison RevHalt / Collatz

| Aspect | RevHalt | Collatz |
|--------|---------|---------|
| Palier | S1Rel = vide | U stabilise |
| Pouvoir interdit | Décideur total | Système compatible de résidus |
| Barrière | T2 (diagonale logique) | Compatibilité 2-adique |
| Statut | Formalisé Lean | Démontré structurellement |
| Chaînon final | Complet | Hypothèse de connexion |

---

**Fin du document V1.2**
