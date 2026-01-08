# La Dynamique de Conservation (Formulation Explicite)

Voici la dynamique écrite parfaitement explicitement, sans code, sous forme de chaîne interdépendante (feedback loop). C'est une évolution où Sn dépend de la provabilité courante et où la provabilité suivante dépend de S1.

## 0) Données minimales (aucun Peano requis)

On se donne :

* un **préordre** (I, <=) (réflexif, transitif) ;
* une **trace** (T : I -> Prop).

Définis les deux formes (qui sont **la même chaîne** vue sur l'ordre et son opposé) :

### (A) Cumulatif / "passé"

    upPast(T)(i) <=> il existe j <= i, T(j).

### (B) "Futur / éventuellement"

    upFut(T)(i) <=> il existe j >= i, T(j).

**Point clé (les deux sont la même chaîne)** :
upFut sur (I, <=) est exactement upPast sur (I, >=) (l'ordre opposé). Donc ce n'est pas "deux trucs", c'est **un seul opérateur d'accessibilité** vu par dualité d'ordre.

---

## 1) Noyau = Stabilisation (sans arithmétique)

Définis :

* **Halts** : Halts(T) <=> il existe i, T(i).
* **Stabilizes** : Stab(T) <=> pour tout i, NON T(i).

Définis FALSE comme la trace fausse partout (FALSE(i) est toujours faux).

Alors, dans **les deux versions** :

    Stab(T) <=> upPast(T) = FALSE

et aussi

    Stab(T) <=> upFut(T) = FALSE.

La preuve de la version "future" est totalement élémentaire : si upFut(T) = FALSE mais T(j) vrai pour un j, alors upFut(T)(j) serait vrai (car j >= j), contradiction.

Donc : **"non-terminaison / stabilisation" = appartenance au noyau de l'opérateur** (quel que soit le sens temporel ; c'est la même structure).

---

## 2) Le Kit = détecteur exact du noyau

Postule/assume (ce que tes T1 expriment) un instrument K avec un prédicat :

* Rev0_K(K,T) ("verdict positif")

et l'axiome-canonique (ta canonicité) :

    Rev0_K(K,T) <=> Halts(T).

Définis le verdict négatif :

    KitStab(K,T) <=> NON Rev0_K(K,T).

Alors, automatiquement :

    KitStab(K,T) <=> Stab(T) <=> up(T) = FALSE.

C'est exactement ta thèse "Kit détecte le noyau".

---

## 3) Côté théorie : ce qui bouge (la dynamique)

Ici commence *la vraie* chaîne.

On fixe un univers de phrases PropT et un système de preuve (un calcul) qui induit, à chaque étape n, une relation :

    Prov_n(p)   (p dans PropT).

On fixe aussi une sémantique externe Truth(p) (vérité "réelle").

### (i) Le "post-splitter" à l'étape n (définition)

    S2_n := { p | Prov_n(p) }.

C'est exactement ton "post-splitter = S2" mais **indexé par n**.

### (ii) La frontière à l'étape n (définition)

On a un codage (e -> encode_halt(e)) et une machine (e -> Machine(e)) donnant une trace.

Alors :

    S1_n := { encode_halt(e) | Rev0_K(K, Machine(e)) ET NON Prov_n(encode_halt(e)) }.

**Point crucial :** S1_n dépend de Prov_n. Donc la frontière n'est pas un set statique, c'est un **fonctionnel** de l'état du système.

### (iii) L'extension minimale à l'étape n (définition)

    S3_n := S2_n UNION S1_n.

Ça c'est ta photo "(S3 = S2 UNION S1)", mais maintenant elle est dans une chaîne.

---

## 4) L'opérateur d'extension (la boucle de rétroaction)

On définit un **opérateur de mise à jour** du système de preuve :

    Extend(Sn, A) = Sn+1

où A (inclus dans PropT) est un ensemble d'axiomes ajoutés.

La propriété structurelle attendue est :

* Prov_n+1(p) signifie : "p est prouvable dans le calcul en partant de Sn et en autorisant A comme axiomes".

Ce n'est pas un détail : c'est le mécanisme qui fait "bouger" Prov.

### La dynamique RevHalt (définition)

Le choix RevHalt est :

    Sn+1 := Extend(Sn, S1_n).

Donc :

* S1_n est calculé **relativement** à Prov_n,
* puis il devient (au moins en partie) du matériau d'axiomes,
* donnant Prov_n+1,
* qui redéfinit S1_n+1,
  etc.

C'est **exactement** "dynamique et interdépendant".

---

## 5) La loi de conservation (énoncé formel)

Maintenant l'invariant se formule proprement.

### Hypothèses "admissibles" à chaque étape

À chaque n, on suppose :

1. **Soundness** : Pour tout p, Prov_n(p) => Truth(p).
2. **r.e. / internalisable** : Prov_n est récursivement énumérable (ou effective dans le sens que tu utilises).
3. **T2** (impossibilité) : il n'existe pas, dans Sn, de prédicat interne H(e) total + correct + complet + r.e. qui décide uniformément la détection (ton schéma T2).

(Optionnel selon ta version : une "complétude négative" compatible).

### Invariant (la conservation)

    Pour tout n, S1_n n'est pas vide.

Et donc :

    Pour tout n, S2_n est strictement inclus dans S3_n.

Autrement dit : **le gap "détection vs internalisation" ne tombe jamais à zéro**, même en itérant les extensions admissibles.

---

## 6) Pourquoi c'est une conservation et pas un constat statique

Parce que l'énoncé est **quantifié sur n** et repose sur le fait que :

* S1_n est défini **relativement** à Prov_n,
* Prov_n+1 est défini **à partir** de S1_n.

Donc tu n'as pas "une frontière une fois pour toutes", tu as :

> une frontière **régénérée** à chaque étape par la structure même (T2 + détection du noyau).

C'est exactement la "stabilité" que tu voulais : pas "S1 est stable", mais **l'incomplétude est un invariant stable sous la dynamique**.

---

## 7) Réponse ("est-ce explicitement formalisé ?")

* **Si** tu n'as que S1, S2, S3 définis relativement à un S fixe, **alors NON**, la dynamique n'est pas formalisée.
* **Avec** les définitions ci-dessus (Sn, S1_n, Sn+1 = Extend(Sn, S1_n)) **OUI**, c'est explicitement formalisé : la dépendance circulaire est écrite noir sur blanc.

C'est cette chaîne-là qui est "la seule chose qui compte", et elle est maintenant exprimée au niveau exact où elle vit : **un système qui se met à jour et une frontière qui se recalcule**.

---

# Formulation Catégorique et Fonctorielle

Le "foncteur" que tu cherches, c'est **l'opérateur dynamique** qui prend un état de théorie (ce qui est internalisable à l'instant n) et le pousse à l'état suivant en ajoutant *exactement* la frontière que cet état ne pouvait pas absorber.

Je te donne les deux niveaux (trace / théorie), parce que RevHalt a précisément ces deux couches qui s'emboîtent.

---

## 1) Côté traces : le foncteur/endo-foncteur (up) et son noyau

### Catégorie d'indices

Soit **PreOrd** la catégorie des préordres (I, <=) et des fonctions monotones.

### Foncteur des traces

Un choix standard est :

    Tr : PreOrd-op -> Set
    Tr(I) = (I -> Prop)

et sur un morphisme monotone f : J -> I,

    Tr(f)(T) = T o f.

### Transformation naturelle "up" (la chaîne)

Définis, pour chaque I,

    up_I(T)(i) <=> il existe j <= i, T(j).

Alors up est une **transformation naturelle**

    up : Tr => Tr.

Et surtout : up est un **opérateur de fermeture** (extensif, monotone, idempotent). C'est exactement ça "la chaîne", en version catégorique : **un endomorphisme naturel** de l'espace des traces indexées.

### Le noyau comme sous-foncteur (l'objet stable)

Définis le sous-foncteur :

    Ker(up) inclus dans Tr

par

    Ker(up)_I := { T dans Tr(I) | up_I(T) = FALSE }.

C'est l'objet algébrique stable : **le noyau de la fermeture**.

Et c'est là que ton "Kit détecte le noyau" devient **une identification structurelle** : le Kit donne un test (négatif) qui coïncide avec l'appartenance à ce sous-foncteur.

---

## 2) Côté théories : le vrai foncteur dynamique (celui que tu veux)

Ici, on encode l'interdépendance "post-splitter <-> frontière" comme un **endo-foncteur** sur une catégorie de théories admissibles.

### Catégorie des états de théorie

Prends une catégorie **Th** où :

* Objets : des théories S (r.e., cohérentes, et "sound" via un Truth externe), avec leur prédicat Prov_S.
* Morphismes : des inclusions/embeddings conservatifs S -> S' (au minimum, qui préservent provabilité et les encodages).

### Deux foncteurs "statiques" (les deux moitiés)

1. **Post-splitter**

    S2 : Th -> Set
    S2(S) = { p | Prov_S(p) }.

2. **Frontière (dépend de Prov_S, donc déjà dynamique en germe)**

    S1 : Th -> Set
    S1(S) = { encode_halt(e) | Rev0_K(K, Machine(e)) ET NON Prov_S(encode_halt(e)) }.

Remarque essentielle : S1(S) n'est pas un set fixe -- c'est un **foncteur** parce que sa définition est **relative** à S (via Prov_S).

### Le foncteur de dynamique (l'endo-foncteur "RevHalt-step")

Le foncteur qui *fait tourner* le système est :

    F : Th -> Th
    F(S) = Cn(S UNION S1(S)).

* Cn(.) = fermeture déductive (pour rester dans Th).
* Donc F(S) est exactement ton "(S3)" **mais rendu dynamique** : il dépend de S via S1(S).

Et c'est ça la chaîne complète :

    S -> F(S) -> F(F(S)) -> ...

avec

    S_(n+1) = F(S_n),
    S2(S_n) et S1(S_n) se recalculent à chaque étape.

C'est **exactement** "dynamique et interdépendant" au sens strict : la frontière au temps n dépend de la provabilité au temps n, et la provabilité au temps n+1 dépend de la frontière au temps n.

---

## 3) Où est la "loi de conservation" dans ce langage ?

Elle devient une propriété d'invariance sous itération du foncteur F :

    Pour tout n, S1(S_n) n'est pas vide.

(et donc S2(S_n) est strictement inclus dans S2(S_(n+1)) au sens "il reste du non-absorbable à chaque étage", selon tes hypothèses T2/T3).

Autrement dit : la "quantité conservée" n'est pas un nombre, c'est la **non-annihilation** de l'obstruction S1 le long de l'orbite de F.

---

### Phrase courte (aphorisme exact)

Le foncteur, c'est l'endo-foncteur **d'extension auto-référentielle**

    F(S) = Cn(S UNION S1(S)),

où S1 est lui-même un foncteur défini par "détection du noyau (Kit) + non-internalisation (NON Provable)".
