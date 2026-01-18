# Definition minimale de la spirale P-Q-R (sans latex)

Ce document fixe une definition de la spirale a partir du trilemme, avec
trois types de theorie, une transition explicite et des formules en ASCII.

---

## 1) Les trois lettres (couche trilemme)

Objets fixes:

- Gamma_1 : theorie au rang 1
- omegaGamma : theorie a la limite omega

Predicats:

- P := Absorbable(Gamma_1)
- Q := OmegaAdmissible(omegaGamma)
- R := RouteIIAt(omegaGamma)  (frontiere non vide)

Trilemme:

```
not (P and Q and R)
```

Renforcement (utilisable si on adopte l'axe structurel omega_trilemma):

```
R -> not P
```

---

## 2) Trois types de theorie (regimes definis)

On definira trois types, chacun conserve deux proprietes et abandonne la
troisieme. Ce sont des regimes de travail, pas une disjonction logique.

```
Type_PQ := P and Q and not R
Type_PR := P and R and not Q
Type_QR := Q and R and not P
```

Le trilemme interdit P and Q and R, donc aucun regime ne peut porter les trois
proprietes en meme temps.

---

## 3) Ce que Complementarity ajoute (une seule operation)

Complementarity donne un schema d'extension a partir d'un temoin de frontiere.

Forme minimale (ajout d'un temoin):

```
Ext(Gamma) := Gamma union {s}
```

ou s est "frontiere": certifie vrai et non prouvable dans Gamma.

Notation: Ext est le pas singleton. Quand on sature, on ecrit:

```
Ext_sat(Gamma) := Gamma union S1Rel(Gamma)
```

Rappel: S1Rel(Gamma) est le predicat "frontiere" et S1Set(Gamma) son ensemble.

Forme canonique (dans Complementarity):

```
S3 = S2 union S1Set
```

Si R(omegaGamma) est vrai, il existe s in S1Rel(omegaGamma), et on peut definir:

```
omegaGamma_plus := omegaGamma union {s}
```

C'est le pas de progres minimal (un seul axiome ajoute).

---

## 4) La spirale: iteration du pas de frontiere

Une spirale est l'iteration de Ext tant qu'il existe une frontiere.

Definition:

```
Gamma^(0) := omegaGamma
Gamma^(n+1) := Gamma^(n) union {s_n}
avec s_n in S1Rel(Gamma^(n)) si un tel s_n existe
```

Donc:

```
Gamma^(0) subsetneq Gamma^(1) subsetneq Gamma^(2) subsetneq ...
```

On repete le mecanisme "frontiere -> ajout" sans revenir au meme etat.
Cette stricte croissance suppose que chaque s_n est bien hors de Gamma^(n).
Convention: on note omegaGamma^(n) := Gamma^(n) (iteration au niveau omega).

---

## 5) Regle de cout issue du trilemme

A chaque niveau n, on peut mesurer:

```
P_n := Absorbable((Gamma^(n))_1)
Q_n := OmegaAdmissible(omegaGamma^(n))
R_n := RouteIIAt(omegaGamma^(n))
```

Le trilemme impose:

```
not (P_n and Q_n and R_n)
```

Et, si on adopte l'axe structurel (optionnel):

```
R_n -> not P_n
```

Lecture simple: tant que la spirale a du carburant (R_n vrai), l'absorption
forte P_n est impossible. Garder R force a perdre P et/ou Q.

---

## 6) Condition "ne pas s'arreter"

Avec seulement cette couche, on ne peut pas prouver que la spirale est infinie.
Pour qu'elle ne s'arrete jamais, il faut une hypothese minimale de regeneration:

```
forall n, R_n
```

C'est le role des fichiers de dynamique (RouteII applique, trajectoires, etc.):
deriver cette regeneration sous soundness, negative completeness, semidec
et barriere T2.

Sans regeneration, la spirale peut s'arreter si R_n devient faux.

---

## 7) Resume minimal en une ligne

```
Gamma^(n+1) = Gamma^(n) union {s_n in S1Rel(Gamma^(n))}
and R_n -> not P_n
```

---

## 8) Deux objectifs distincts (a ne pas melanger)

Objectif A — Existence d'une spirale infinie:

```
exists (Gamma^(n))_n, strictly increasing, with
Gamma^(n+1) = Gamma^(n) union {s_n} and s_n in S1Rel(Gamma^(n))
```

Objectif B — Spirale constructive (iterable par regle locale):

```
Next/Ext fabrique Gamma^(n+1) a partir de Gamma^(n)
et garantit la persistance de la frontiere
```

Les alternatives ci-dessous sont des moyens possibles de realiser ces objectifs.

## 9) Alternatives classees par force logique

1) Regeneration non constructive (existence locale):

```
forall Gamma, R(Gamma) -> exists s in S1Rel(Gamma) and R(Gamma union {s})
```

Donne une reparabilite locale. Ne produit pas automatiquement une suite infinie
sans choix dependant.

2) Existence d'une suite globale (sans fonction Next):

```
exists (s_n), s_n in S1Rel(Gamma^(n)) and Gamma^(n+1) = Gamma^(n) union {s_n}
```

Cible directe de l'objectif A. En general incomparable avec (1) sans choix.

3) Choix classique / Skolem non calculable:

```
Next(Gamma) in S1Rel(Gamma) when R(Gamma)
```

Equivalent a (1) + choix uniforme. Donne une regle locale non calculable.

4) Extension par toute la frontiere:

```
Ext_sat(Gamma) := Gamma union S1Rel(Gamma)
```

Evite le choix d'un temoin, mais requiert en plus:

```
R(Gamma) -> R(Ext_sat(Gamma))
```

Cette persistance est une hypothese forte.

5) Oracle/kit (Next externe):

```
Next_O(Gamma) fourni par un oracle, avec
Next_O(Gamma) in S1Rel(Gamma) and R(Gamma union {Next_O(Gamma)})
```

Regle locale definissable, pas forcement calculable. Proche de (3), mais
explicitement externalisee.

## 10) Choix de principe cible (recommande)

Si l'objectif est A (existence seule):

```
exists (Gamma^(n)) strictly increasing with frontier additions
```

Si l'objectif est B (regle locale sans calculabilite):

```
exists Next_O with R(Gamma) -> Next_O(Gamma) in S1Rel(Gamma)
and R(Gamma union {Next_O(Gamma)})
```

---

## 11) Intérêt du systeme (formalise)

Le systeme sert a transformer le trilemme en dynamique demonstrable, pas en
simple narration.

Points structurants:

- Separation nette entre regimes (P/Q/R) et etats (Gamma) pour eviter
  "cycle des regimes = pas de progres".
- Cout explicite a chaque etape: garder R force a perdre P et/ou Q.
- Localisation des hypotheses manquantes: regeneration/Next est isolee
  comme principe cible, pas comme consequence cachee.
- Progres prouvable: inclusion stricte ou rang ordinal comme mesure.
- Formule courte: "le trilemme induit un automate fini de regimes, et toute
  non-trivialite (spirale) exige une variable de progres orthogonale, sinon
  on retombe en cycle".

## 12) Apport de Trajectory (couche dynamique)

Le fichier Trajectory ajoute une couche "dynamique effective" a la spirale.

Points clefs:

- Trajectoire canonique: une suite unique Γ_n = F0^n(Γ0), pas un schema ambigu.
- Unicite: toute trajectoire F0-compatible est egale a la canonique.
- Dependence initiale: la trajectoire est entierement determinee par Γ0 (temps 0).
- Croissance stricte conditionnelle: regeneration + PostSplitter -> progression stricte.
- Point de rupture formalise: "incarnation trilemma" et "escape via continuity"
  isolent la variable libre (continuité ω).

Lecture simple: Spirale = schema; Trajectory = schema + objet effectif + verrou logique.

---

## 13) Application a Collatz (Verification conditionnelle)

La question "Le cycle 4-2-1 correspond-il au regime Type_PQ ?" est verifiable
(conditionnelle), et decidable si P/Q/R le sont.

- **Condition 1 (Instanciation)** : Il faut definir explicitement un objet D
  associe a Collatz et des predicats P(D), Q(D), R(D).
- **Condition 2 (Hypothese Frontiere)** : Il faut poser (ou prouver) que
  l'etat "cycle 4-2-1" implique "frontiere vide" (R est faux).

**Formulation Canonique** :

> Fixer l'interpretation Collatz (-> D) et les definitions de (P,Q,R).
> Ajouter (ou prouver) non-R au puits.
> Alors "puits = Type_PQ" est une consequence immediate (definitionnelle).

L'unique point non mecanique est la clause "frontiere vide au puits", qui est
soit un axiome d'instanciation, soit un lemme a prouver. Elle ne se deduit pas
du trilemme seul. Une fois posee, l'assignation est une verification definie
(et mecanique si P,Q,R sont decidables).

Note de rigueur:

- "Collatz se deduit du trilemme" = faux (theoreme)
- "Collatz est une instanciation reconnaissable sous canonisation + puits" = vrai (interpretation)

Sous une instanciation Collatz->D et l’hypothèse (ou preuve) ¬R au puits, le cycle 4-2-1 se reconnaît comme un représentant arithmétique du régime Type_PQ (stabilisation). Dans cette lecture, “s’arrêter” correspond à l’extinction de la frontière (plus de témoin S1 à ajouter), et l’absence de variable orthogonale observable au niveau des régimes rend compatible le fait qu’on retombe sur un cycle.

---

## 14) Verrou de preuve (le seul point non mecanique)

### 14.1 Deux directions exclusives (ne pas confondre)

**(A) Canonisation / arret (puits, type PQ)**
Objectif : montrer que la spirale s'eteint en temps fini.

Hypothese (stabilite PQ):

```
forall n (ou a partir d'un rang), P_n and Q_n
```

Formes equivalentes sous stabilite(P,Q) :

1. **Extinction finie de la frontiere**

```
exists n, not R_n
```

1. **Fixpoint d'extension (canonisation)**

```
exists n, Ext_sat(Gamma^(n)) = Gamma^(n)
```

(avec la lecture : "plus rien a ajouter")

1. **Stabilisation en Type_PQ a partir d'un rang**

```
exists n0, forall n >= n0, Type_PQ_n
```

**(B) Spirale infinie (regeneration)**
Objectif : montrer que la spirale ne s'arrete jamais.

Formes equivalentes :

1. **Regeneration globale**

```
forall n, R_n
```

1. **Regle locale Next (version constructive)**

```
forall n, R_n -> exists s_n in S1Rel(Gamma^(n)) and R(Gamma^(n) union {s_n})
```

### 13.2 Ou la preuve doit tomber

Le framework sert a isoler ce verrou. Tout le reste est mecanique une fois
(A) ou (B) etabli.

---

## 15) Canonisation arithmetique (contrainte implicite)

Principe de canonisation (arithmetique) :
Sous la contrainte arithmetique, l'extension saturee par frontiere atteint un fixpoint
(donc la frontiere s'eteint).

```
ArithmeticConstraint -> exists n, Ext_sat(Gamma^(n)) = Gamma^(n)
```

Definition directe du Fixpoint :

```
Fixpoint(Gamma) := S1Rel(Gamma) = emptyset
```

Comme R(Gamma) := S1Rel(Gamma) != emptyset, on a :

```
Fixpoint(Gamma) <-> not R(Gamma)
```

La canonisation arithmetique force ce Fixpoint.

---

## 16) Collatz : statut du puits

Dans l'instanciation Collatz->D, le puits 4-2-1 est suppose (ou montre) etre
un fixpoint pour Ext_sat, donc non-R.

```
Puits_421 -> Ext_sat(omegaGamma_puits) = omegaGamma_puits -> not R_puits
```

Ceci relie la "canonisation" a la Condition 2, confirmant que le lien est
mecanique une fois le puits atteint.
