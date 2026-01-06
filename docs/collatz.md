# Note RevHalt : Smodp, “premiers” RevHalt, et composition de splitters (autocontenu, sans latex)

Cette note fixe une spécification **RevHalt-native** pour :

1. un splitter “congruence-like” `Smod p` (qui sépare réellement les classes modulo p),
2. une notion **opérationnelle** de “premier” (pas ontologique) via l’atomicité / non-factorisation de splitters,
3. une notion propre de **composition** de splitters et les obligations associées (refinement, cover, associativité).

Tout est formulé au niveau `Splitter`, `Info`, `Sat`, `Cases`, `ResEquiv`.

---

## 0) Rappel des objets (ce que l’implémentation impose)

* `Info Pos := List (Pos → Prop)` (liste finie de contraintes)

* `Sat Pos I n := ∀ c ∈ I, c n` (n satisfait toutes les contraintes)

* `Splitter Pos` :

  * `split : Info Pos → List (Info Pos)`
  * `refinement : ∀ I J, J ∈ split I → (∀ n, Sat J n → Sat I n)`
  * `cover : ∀ I n, Sat I n → ∃ J ∈ split I, Sat J n`

* `Cases S d I0` : déroulé de split jusqu’à profondeur d (flatMap itératif)

* `ResEquiv S d I0 n m` : indistinguabilité par tous les cas de profondeur d

---

## 1) Pourquoi `Split_div p` n’est pas `Smod p`

`Split_div p` construit deux branches :

* “p divise n”
* “p ne divise pas n”

Donc il sépare en 2 classes : résidu 0 contre “non 0”, pas en p classes.

Conclusion : `Split_div p` est un splitter de **divisibilité**, pas un splitter de **congruence**.

C’est utile (Collatz, facteurs, v2), mais ce n’est pas l’outil qui isole finement les classes modulo p.

---

## 2) Spécification RevHalt de `Smod p`

### 2.1 Les contraintes élémentaires

On travaille sur `Pos := Nat`.

Définir une famille de contraintes :

* `Congr(p, r) : Nat → Prop := fun n => n % p = r`

Hypothèse de base requise :

* `p > 0` (pour que `% p` soit défini et les classes couvrent)

### 2.2 Définition de `Smod p` comme Splitter

Intention : pour une info `I`, `split I` renvoie p cas :

* `I ++ [Congr(p, 0)]`
* `I ++ [Congr(p, 1)]`
* ...
* `I ++ [Congr(p, p-1)]`

Donc :

* `split(I)` est une liste de longueur p
* chaque branche ajoute **une** contrainte “résidu = r”

### 2.3 Obligations de preuve (refinement / cover)

**Refinement** (facile) :
si `J = I ++ [Congr(p,r)]` alors `Sat(J,n) -> Sat(I,n)` parce que `Sat` est monotone par retrait de contraintes.

**Cover** (le cœur) :
si `Sat(I,n)` alors prendre `r := n % p` et montrer :

* `Sat(I ++ [Congr(p,r)], n)`

Cela demande seulement :

* `n % p = n % p` (réflexivité)
* et `Sat(I,n)` déjà acquis

Il n’y a pas de choix non-constructif : `r` est calculable.

### 2.4 Propriété attendue sur la relation de résidu (sanity check)

Avec `I0 := []` et `d := 1` :

* `ResEquiv(Smod p, 1, [], n, m)` doit être équivalent à :

  * `(n % p = m % p)`

Pourquoi :

* `Cases(1,[])` liste exactement les p infos `[Congr(p,r)]`
* `Sat([Congr(p,r)], n)` équivaut à `n%p=r`
* donc l’indistinguabilité par toutes ces contraintes est exactement l’égalité des résidus

Ceci est le **lemme de correspondance** “RevHalt residue = congruence modulo p” pour `Smod p`.

---

## 3) Composition de splitters (le produit opérationnel)

### 3.1 Définition canonique

Pour deux splitters `A` et `B` sur le même `Pos`, définir la composition `A ⊗ B` par :

* `split_{A⊗B}(I) := (A.split I).flatMap B.split`

Interprétation :

* on split d’abord par A, puis chaque branche est raffinée par B
* cela encode exactement une “résolution à deux étages”

### 3.2 Obligations : refinement et cover pour la composition

**Refinement** :

* si `K ∈ split_{A⊗B}(I)`, alors `K` provient d’un `J ∈ A.split(I)` et `K ∈ B.split(J)`
* on a `Sat(K,n) -> Sat(J,n)` par refinement de B
* puis `Sat(J,n) -> Sat(I,n)` par refinement de A
* donc `Sat(K,n) -> Sat(I,n)`

**Cover** :

* si `Sat(I,n)`, alors par cover de A il existe `J ∈ A.split(I)` avec `Sat(J,n)`
* puis par cover de B il existe `K ∈ B.split(J)` avec `Sat(K,n)`
* donc `K ∈ split_{A⊗B}(I)` et `Sat(K,n)`

Conclusion : `A ⊗ B` est un Splitter sans axiomes supplémentaires.

### 3.3 Associativité (à vérifier et à formaliser)

On veut : `(A ⊗ B) ⊗ C` et `A ⊗ (B ⊗ C)` produisent les mêmes cas “à permutation près”.

Point clé RevHalt :

* `split` renvoie une `List`, donc l’égalité stricte est fragile (ordre).
* la propriété pertinente est l’**équivalence d’ensemble** des cas, ou l’équivalence de `ResEquiv` induite.

Forme recommandée :

* prouver que `ResEquiv` induit par `(A⊗B)⊗C` est équivalent à celui induit par `A⊗(B⊗C)` (même observabilité à profondeur 1), plutôt qu’une égalité de listes.

---

## 4) “Premiers” dans RevHalt : définition opérationnelle

### 4.1 Principe (ce qu’on veut capturer)

Dans RevHalt, un “premier” ne doit pas être :

* “p est premier” comme propriété ontologique dans Nat,

mais :

* “le splitter associé à p est atomique / irréductible” dans la grammaire de résolution finitaire.

Autrement dit : p est premier si **sa résolution** ne se décompose pas en résolutions plus petites sans perte.

### 4.2 Notion 1 : atomicité de résolution (factorisation de splitters)

Fixer une famille de splitters `Smod p`.

Définir :

* `Factorizes(p, a, b)` si `Smod p` est équivalent (au niveau `ResEquiv` à profondeur 1, ou au niveau `Cases`) à `Smod a ⊗ Smod b`.

Alors définir un “prime_RH” :

* `Prime_RH(p)` : “il n’existe pas de factorisation non triviale p = a*b avec 1<a<p, 1<b<p telle que `Smod p` équivaille à `Smod a ⊗ Smod b`”

C’est une définition **dynamique/observatoire** :

* elle parle de la capacité de résolution, pas de la nature de p.

### 4.3 Relation attendue avec les premiers classiques

Objectif de théorème (pas un axiome) :

* si p est premier au sens classique, alors `Prime_RH(p)` pour la famille `Smod`.
* si p est composé, alors `Smod p` “factorise” selon la structure de la congruence (via CRT ou via propriétés de `%`), donc `¬Prime_RH(p)`.

Vous n’êtes pas obligé de prouver CRT globalement pour obtenir un résultat utile :

* vous pouvez viser un résultat plus faible mais exploitable :

  * “si p = a*b, alors l’observabilité de `Smod a ⊗ Smod b` raffine celle de `Smod p`” (inclusion de `ResEquiv`), ce qui suffit déjà pour une hiérarchie.

---

## 5) Pourquoi c’est plus général que “modulo premier”

Point clef : **RevHalt ne fige pas l’arithmétique en congruence**.
`ResEquiv` est défini à partir de `Cases` et `Sat`, donc :

* modulo classique est une instanciation (`Smod p`)
* divisibilité est une autre instanciation (`Split_div p`)
* valuation v2, tags, contraintes affines, etc., sont des instanciations du même format

Ce qui change par rapport au classique :

* l’objet fondamental n’est pas “Z/pZ”
* c’est “la capacité de distinguer des classes finies par contraintes”
* et cette capacité se compose mécaniquement (`⊗`) et se transporte vers Up2/Avoid2/Temporal

C’est exactement la “couverture finitaire par contrainte”.

---

## 6) Lien direct avec l’attaque Collatz (sans refaire Collatz ici)

Même sans parler de Collatz, la conséquence opérationnelle est :

* vous pouvez choisir une base d’observabilité mixte :

  * `S := Split_v2(k) ⊗ Split_affine(p, a, b) ⊗ Smod q ⊗ ...`
* puis la notion de “résidu RevHalt” devient :

  * “indistinguabilité par toutes les contraintes générées par ce pipeline”
* et `Queue` devient :

  * “la dynamique ne sort jamais de son résidu (au sens de cette observabilité)”

Ce cadre permet d’exprimer “modulo” de façon plus générale que la congruence :

* modulo comme “résolution finitaire”,
* pas comme quotient a priori.

---

## 7) Deliverables concrets (ce qu’il faut coder/prover)

1. Implémenter `Smod p` (split en p branches Congr(p,r))
2. Lemme : `ResEquiv(Smod p, 1, [], n, m) <-> (n%p = m%p)`
3. Implémenter `⊗` et prouver que c’est un Splitter (refinement/cover)
4. Lemme d’associativité “à ResEquiv près”
5. Définir `Prime_RH` via non-factorisation observatoire
6. Prover des implications de hiérarchie : si p factorise, alors observabilité se factorise (au moins un sens)

---


