# Énoncé blindé : ce que démontre TSP dans RevHalt

## 1) Objet : "résoudre TSP" dans RevHalt

Dans ce cadre, "résoudre TSP" ne signifie pas exhiber un nouvel algorithme combinatoire.

Cela signifie : réduire la question TSP à une question de **trajectoire** (dynamique d'enrichissement Γ₀ → Γ₁ → … → Γ_ω) et montrer que, sous certaines contraintes structurelles, la trajectoire force une forme de canonisation qui produit un procédé effectif (décision et, si possible, extraction d'un tour).

Le résultat est donc : **TSP devient décidable / recherchable relativement à une trajectoire et à ses contraintes**, pas "en absolu".

## 2) Formalisation de TSP comme instance de halting

On formalise :

- une instance TSP comme un code naturel (encodage constructif),
- une machine `Machine_TSP` qui énumère les tours et vérifie la validité,
- le fait central : **`Machine_TSP code` halte si et seulement si l'instance codée admet un tour valide**.

Conséquence : TSP (décision) est aligné avec un énoncé de type "halting" mais sur une machine monotone et transparente.

## 3) Frontière (S1Rel) : la couche de provabilité

On définit une frontière relative à un état de théorie Γ :

```
S1Rel_TSP(Γ) = ensemble des codes TSP tels que
  - l'instance est satisfaisable (la machine halte),
  - mais sa proposition "halte" n'est pas prouvable dans Γ.
```

C'est la **couche manquante** des approches standards : on suit la résistance du problème non seulement par complexité, mais par **absorbabilité dans une trajectoire de preuves**.

## 4) Trajectoire canonique et trilemme

On instancie la dynamique RevHalt :

- Γ₀ donné,
- Γₙ₊₁ = enrichissement canonique (absorption des témoins / fermeture),
- Γ_ω = limite oméga.

On applique le **théorème structurel** :

> Il est impossible de conserver simultanément :
>
> - **Absorbable** (la théorie absorbe correctement les témoins),
> - **OmegaAdmissible** (cohérence/continuité de trajectoire à la limite),
> - **RouteIIAt** (frontière non vide à ω).

Donc : à ω, **au moins une de ces propriétés doit casser**.

C'est le **verrou structurel** qui remplace "chercher un algo".

## 5) Le shift : l'axiome n'est pas un choix arbitraire, c'est l'information sémantique manquante

Le point décisif du programme est :

- On ne suppose pas "TSP est en P".
- On **identifie quelle information manque à la sémantique** pour rendre la trajectoire stable.
- Cette information manquante apparaît sous la forme d'un paquet **"canonisation effective"**.

Autrement dit : le bon axiome est **l'output minimal compatible avec les contraintes structurelles** que l'on choisit de préserver.

## 6) Version vraiment "constructive" (preuve-carrying)

Pour que "Collapse est output" soit inattaquable, on doit faire passer la provabilité de `Prop` vers de la **donnée vérifiable**.

**Hypothèse structurelle "preuve-carrying" :**

Au lieu de `Provable Γ p : Prop`, on travaille avec un schéma effectif :

```
Provable Γ p := ∃ d, ChecksDerivation Γ p d
```

où `d` est un code de dérivation, et `ChecksDerivation` est décidable.

Alors on peut extraire des programmes depuis les preuves, sans magie.

## 7) Théorème de sortie : Collapse comme conséquence d'une canonisation effective

**Définition (donnée, pas axiome) :**

`EffectiveCanonizationAtOmega` fournit :

- `Decide : code → Bool`,
- `extract : code → List Nat` (un tour),
- et les garanties :
  - si `Decide code = true` alors il existe un tour valide,
  - si l'instance a un tour valide alors `Decide code = true`,
  - et `extract` fournit un tour valide quand `Decide` dit oui.

**Théorème :**

À partir de `EffectiveCanonizationAtOmega`, on construit une fonction

```
Find code : Option (List Nat)
```

qui retourne `some tour` si `Decide code` est vrai, sinon `none`,
et on obtient un objet de type `Collapse_TSP_Axiom` (version "search").

Donc :

- **Collapse (Find) n'est pas posé comme axiome isolé**,
- il est **dérivé d'une canonisation effective à ω**.

## 8) Ce que RevHalt "démontre" sur TSP (formulation finale)

Le fichier TSP dans RevHalt démontre :

1. **TSP est représentable** comme une propriété de halting d'une machine explicite et monotone.

2. **La frontière S1Rel_TSP mesure**, le long d'une trajectoire Γ₀ → … → Γ_ω, les instances vraies mais non absorbées.

3. **Le trilemme impose une contrainte** : on ne peut pas garder simultanément Absorbable + OmegaAdmissible + RouteIIAt.

4. **Si l'on choisit** une trajectoire qui préserve Absorbable et OmegaAdmissible et que l'on obtient une canonisation effective à ω, **alors on produit** un schéma de recherche de certificat (Collapse) pour TSP, donc une procédure de décision et une extraction de tour dans ce cadre.

**Ce n'est pas "P = NP".**

C'est : **TSP devient un problème de trajectoire** : trouver (ou caractériser) les trajectoires où la canonisation effective existe, et donc où Collapse est un output contraint.

## 9) Phrase courte utilisable publiquement

> "Dans RevHalt, TSP n'est pas 'résolu' par un nouvel algorithme, mais par une dynamique : on formalise TSP comme halting, on suit sa frontière de non-absorption le long d'une trajectoire de théorie, et on montre qu'une canonisation effective à la limite produit un Collapse (Find) comme sortie. Le gap find/verify devient un phénomène dépendant de trajectoire et de l'information sémantique manquante."
