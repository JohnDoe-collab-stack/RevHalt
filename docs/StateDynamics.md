# La Dynamique comme Système d'États (Machine Auxiliaire)

Si l'on veut formaliser la dynamique comme un objet auxiliaire, séparé du cœur (S1/S2/S3), la méthode mathématiquement propre est de construire un **système d'état** (une "machine" de réécriture) et de montrer ensuite comment (S1, S2, S3) se lisent comme projections.

Voici la version la plus nette, en dehors du cœur.

---

## 1) L'objet "à part" : l'état dynamique

Un **état** est un couple

    X := (S, F)

où :

* S (inclus dans PropT) est la **partie internalisée** (post-splitter, "ce que la théorie tient"),
* F (inclus dans PropT) est la **frontière disponible** (ce qui est détecté comme vrai mais pas absorbé).

Ce n'est pas "du code", c'est juste la structure minimale qui encode l'interdépendance.

---

## 2) L'évolution : un seul opérateur dynamique

Définis l'opérateur de transition (une étape) :

    Delta(S, F) := (S', F')

avec

    S' := Cn(S UNION F),
    F' := Frontier(S').

Et Frontier c'est exactement ta définition RevHalt (one-sided) :

    Frontier(S) := { encode_halt(e) | Rev0_K(Machine(e)) ET NON Prov_S(encode_halt(e)) }.

**Point crucial** : F' dépend de S', donc la frontière n'est pas un "ensemble fixe" ; elle est recalculée à chaque étape. C'est là que ta dynamique est formalisée, sans ambiguïté.

---

## 3) La chaîne (la seule chose qui compte)

À partir d'un état initial X0 = (S0, F0), on définit :

    X_(n+1) := Delta(X_n).

Et on peut regarder les projections :

* S_n := pi_S(X_n) = post-splitter au pas n,
* F_n := pi_F(X_n) = frontière au pas n.

C'est **exactement** "la chaîne complète" sous forme dynamique, interdépendante.

---

## 4) Comment (S1, S2, S3) se récupèrent "en lecture"

À chaque étape n :

* S2_n := S_n     (post-splitter à l'étape n),
* S1_n := F_n     (frontière à l'étape n),
* S3_n := S_n UNION F_n (extension "complémentaire" à l'étape n).

Donc tu as bien ton schéma (S3 = S2 UNION S1), mais cette fois **avec S1 et S2 co-évoluant**.

---

## 5) Pourquoi c'est "strictement" dynamique

La dépendance croisée est explicite :

* S_(n+1) = Cn(S_n UNION F_n) : la frontière pousse l'internalisation,
* F_(n+1) = Frontier(S_(n+1)) : l'internalisation réécrit la frontière.

C'est un **couplage** (feedback loop), pas une simple monotonie statique.
