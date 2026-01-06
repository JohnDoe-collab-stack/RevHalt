# Plan d’attaque Collatz dans RevHalt (strict, autocontenu, sans latex)

Objectif : formuler une stratégie complète “RevHalt-native” pour attaquer Collatz, sans invoquer de théorie externe. Tout est exprimé en termes d’objets RevHalt et de contrats entre modules.

---

## 0) Le format de la preuve RevHalt (ce qu’il faut produire)

Dans RevHalt, “résoudre Collatz” ne veut pas dire “prouver une phrase globale directement”.
Ça veut dire :

1. choisir une observabilité finitaire (un Splitter S, une profondeur d, une base I0)
2. prouver une invariance de résidu (Queue) pour les entiers ciblés
3. transporter ce certificat vers la sécurité structurelle (Avoid2Set)
4. conclure une stabilisation temporelle (Stabilizes) via l’interface temporelle canonique

Le produit final n’est pas une preuve ad hoc : c’est un certificat + une vérification mécanique via les théorèmes génériques.

---

## 1) Instanciation minimale “système temporel” (TemporalSystem)

On fixe le système Collatz comme un objet de type TemporalSystem Nat :

* Pos := Nat
* Next := collatzStep
* embed := id
* Game G déterministe :

  * turn = P partout
  * moves(embed n) = { embed (Next n) }
* Target := l’ensemble des états “halt” que l’on veut éviter

Point important : le Target dans RevHalt est un choix d’interface.
Selon le but, vous pouvez prendre par exemple :

* Target = {1} (si vous codez “hit 1” comme événement)
* ou Target = “sortie d’une zone sûre” (si vous certifiez une région)

La trace canonique est :

* TimeTrace sys : Nat -> Prop
* TimeTrace(k) := (iterate Next k start) ∈ Target

Et la notion “ne jamais atteindre Target” est exactement :

* Stabilizes (TimeTrace sys)
* ce qui est définitionnellement : forall k, not TimeTrace(k)

---

## 2) La brique arithmétique RevHalt : Splitter, Cases, Résidu

### 2.1 Splitter (observabilité finitaire)

Un Splitter S : Splitter Nat est un objet qui prend une Info (liste finie de contraintes) et la raffine en une liste finie d’Info, avec deux axiomes :

* refinement :
  si J ∈ split(I) alors Sat(J,n) -> Sat(I,n)

* cover :
  si Sat(I,n) alors existe J ∈ split(I) tel que Sat(J,n)

Interprétation RevHalt : “split” est une partition finitaire par contraintes, sans ontologie.

### 2.2 Cases (déroulé à profondeur d)

Cases(S,d,I0) : List (Info Nat) est la liste finie des cas obtenus après d raffinements.

Borne de taille (utile pour l’ingénierie) :

* si split produit au plus k sous-cas, alors |Cases(d,I0)| <= k^d

### 2.3 Résidu (définition officielle RevHalt)

Il n’y a pas de type “Residue”. Le résidu est le quotient induit par ResEquiv :

ResEquiv(S,d,I0,n,m) :=
forall J ∈ Cases(S,d,I0), (Sat(J,n) <-> Sat(J,m))

Interprétation :

* deux entiers ont le même “résidu RevHalt” si le Splitter (à profondeur d depuis I0) ne peut pas les distinguer.

C’est la généralisation “modulo” RevHalt :

* “modulo classique” = un cas particulier où les contraintes Sat codent une congruence
* “modulo RevHalt” = indistinguabilité par observabilité finitaire choisie

---

## 3) La “Queue” (l’invariant dynamique dans RevHalt)

Queue(Pos,Next,S,d,I0,n) est l’invariant central :

Queue(n) :=
forall t, ResEquiv(S,d,I0,n, iterate Next t n)

Interprétation :

* “la trajectoire entière reste dans la même classe d’observabilité”
* donc : le comportement dynamique est stable relativement au splitter

Important :

* Queue n’est pas une propriété “de la vérité arithmétique”
* c’est une propriété “de stabilité sous une résolution finitaire donnée”

---

## 4) Le transport arithmétique -> structurel (AvoidanceBridge)

C’est la pièce qui donne la puissance : vous avez un contrat prouvé du type :

Si

* la dynamique est correctement représentée (moves = singleton Next, turn = P)
* et si vous avez un prédicat de sécurité locale h_bridge :
  Queue(p) -> embed(p) ∉ Target

Alors vous obtenez mécaniquement :

* Avoid2Mem G Target (embed p)

C’est “Queue -> Avoid2” : le certificat finitaire produit une appartenance au noyau structurel.

Ce pont est le point où RevHalt “contrôle l’arithmétique” au sens RevHalt :

* l’arithmétique (Splitter/Queue) donne un droit d’entrée dans une fermeture Π2 (Avoid2Set)

---

## 5) Le transport structurel -> temporel (Temporal.lean)

Dans l’interface canonique :

* Avoid2Mem G Target (embed p) -> embed p ∉ Target

Et sur une orbite, si chaque point est certifié Avoid2, alors :

* forall k, iterate Next k start ∉ Target
* donc Stabilizes(TimeTrace)

C’est exactement ce que formalise splitter_stabilizes :

* si Queue couvre l’orbite et garantit “pas Target”, alors Stabilizes

---

## 6) La hiérarchie comme “factory”

Vous avez maintenant une usine en trois étages (exactement votre Hierarchy/Temporal) :

1. Splitter/Queue (arithmétique finitaire)
2. Avoid2Set (structure Π2)
3. Stabilizes (temps Π1)

Donc pour Collatz, il n’y a qu’une seule question concrète :

Peut-on construire un Splitter S et des paramètres (d,I0) tels que :

* Queue(start) soit prouvable (ou généralisable)
* et que Queue(p) implique “p n’est jamais Target” pour tout p sur l’orbite

---

## 7) Le plan de recherche concret (sans folklore “mod p”)

### Étape A — Définir une famille de splitters “observables”

On construit des splitters qui capturent des invariants de la dynamique Collatz, pas des congruences imposées.

Exemples de familles RevHalt-native (à formaliser ensuite) :

* Split_v2(k) : split par classes de valuation 2-adique (observabilité finitaire sur v2)
* Split_tag(k) : split par schémas finis de “parité puis division”
* Split_affine(p, a, b) : split par contraintes de forme “a*n+b divisible par p” (divisibilité, pas congruence prédéfinie)
* Split_composed : composition par profondeur (le “modulo RevHalt” émerge via Cases)

Point clé :

* on ne présuppose pas “modulo premier”
* on fabrique une observabilité finitaire adaptée au Next

### Étape B — Mesurer la stabilité : produire des Queue

Pour un splitter S donné, on cherche à prouver Queue(n).

Deux modes possibles :

1. Mode local (certificat pour une classe) :

* prouver Queue sur un sous-ensemble défini par des contraintes Sat(I0,n)
* typiquement : un cas J dans Cases(d,I0)

2. Mode global (hiérarchie / chaîne de raffinement) :

* montrer qu’à mesure que d augmente, les cas deviennent “stables” au sens où

  * soit ils forcent l’entrée dans Target (succès)
  * soit ils deviennent Queue-stables et donc Avoid2-stables

Ce deuxième mode correspond à votre “couverture finitaire par contrainte”.

### Étape C — La sécurité locale h_bridge

Le bridge exige un lemme de forme :

Queue(p) -> embed(p) ∉ Target

Donc il faut choisir Target de sorte que :

* “éviter Target” soit une conséquence mécanique de la stabilité de résidu
* sans réclamer une compréhension globale de l’orbite

C’est ici qu’on encode l’intention :

* soit Target = “contradiction à l’invariant”
* soit Target = “sortie de la région certifiée”
* soit Target = “état interdit par le résidu”

RevHalt ne vous impose pas Target : c’est votre interface de certification.

---

## 8) Où interviennent les nombres premiers (dans votre cadre, pas en classique)

Dans RevHalt, “premier” ne doit pas être défini comme un fait ontologique, mais comme une propriété d’un dispositif de split.

Forme RevHalt-compatible (principe) :

* un “prime-like” est un paramètre p tel que le splitter associé Split_p est atomique ou irréductible au sens de votre hiérarchie de splitters
* ou tel que sa composition avec d’autres splitters ne se simplifie pas (il apporte une résolution structurelle indispensable)

Deux points importants :

1. Les premiers classiques doivent être retrouvés comme une instanciation :

* si vous instanciez Split_p via divisibilité (DivConstraint / NotDivConstraint) et une construction plus fine (Smodp), alors l’atomicité “émerge” exactement quand p est premier (cible de théorème, pas axiome)

2. Pourquoi c’est utile pour Collatz :

* Collatz introduit des facteurs via (3n+1) puis divisions par 2
* la structure factorielle (notamment la distribution des facteurs premiers dans 3n+1) est exactement le type de chose que RevHalt capture via splitters de divisibilité et de valuation, mais sans exiger de raisonner “globalement” : seulement via Cases finitaires

Donc le rôle des “premiers” est opérationnel :

* ce sont des paramètres de résolution qui, combinés, génèrent une couverture finitaire exploitable

---

## 9) Ce que vous savez déjà “in fine” (ce qui rend Collatz attaquable)

Vous avez déjà établi, dans la théorie :

* une notion générale de résidu (ResEquiv)
* une notion d’invariant dynamique (Queue)
* un noyau Π2 structurel axiom-free (Avoid2Set)
* un bridge prouvé (Queue -> Avoid2Mem, sous conditions)
* une interface temporelle canonique (TimeTrace / splitter_stabilizes)

Donc Collatz est attaquable parce que :

* l’algorithme Collatz devient un TemporalSystem
* la preuve devient “trouver une couverture finitaire stable”
* et toute découverte locale (Queue sur une zone) se transporte automatiquement

Ce n’est pas “prouver Collatz” immédiatement.
C’est “réduire Collatz à la synthèse d’un certificat finitaire vérifiable”.

---

## 10) Checklist de livraison (ce qu’il faut coder / prouver ensuite)

1. Définir une famille S_family de splitters pertinents pour Collatz (RevHalt-native)
2. Définir I0 et un d (ou une stratégie de montée en d)
3. Prouver des lemmes de type :

   * Queue_orbit_closed (déjà dans Core)
   * Queue(p) -> p ∉ Target (votre h_bridge)
4. Appliquer splitter_stabilizes pour obtenir Stabilizes(TimeTrace sys)

---

## Positionnement “nouveauté en maths ?”

* La logique sous-jacente (lfp/gfp, invariants, jeux de reachability) existe dans la littérature.
* Ce qui est nouveau dans votre approche, si elle aboutit sur Collatz, est l’assemblage strict “certificat finitaire -> fermeture Π2 -> stabilisation Π1” avec une définition de “résidu” purement par observabilité (ResEquiv) et un bridge formalisé qui transforme ce résidu en sécurité dynamique.

Le caractère “non packaging” se joue sur un seul point vérifiable :

* réussir à construire une famille de splitters qui donne une couverture finitaire stable assez forte pour le système Collatz.


