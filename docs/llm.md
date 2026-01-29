# Dynamique minimale d'un LLM comme catégorie d'histoires (avec commutations, cofinalité interne et complétion)

Ce document propose un modèle **purement dynamique** (au sens : "l'objet premier est une dynamique d'événements, d'histoires et de commutations"), conçu pour capturer ce que les LLM rendent immédiatement tangible : **l'ordre des sauts compte**, certaines opérations **commutent parfois**, d'autres **ne commutent pas**, et aucun "horizon fini" ne clôt naturellement la dynamique.

Point central : le "transfini ZFC pertinent" (quand on en parle) **n'est pas un index externe** qu'on plaque sur le système. Il **réapparaît uniquement comme effet de scheduling** : il dépend strictement de la géométrie interne des histoires (la catégorie des préfixes et ses cofinalités).

---

## 0. Intuition générale

* Un LLM en situation (conversation + outils + contraintes + observations externes + changements de mode + mises à jour éventuelles) ne se comporte pas comme une simple itération sur une chaîne de temps.
* La bonne primitive n'est pas "un état" mais une **histoire** : un objet avec

  * une grammaire d'événements,
  * une structure de causalité (ordre partiel),
  * des commutations (indépendances) et des non-commutations (dépendances),
  * des changements de régime (modes/policies/budgets),
  * et parfois une méta-dynamique (train/update).

Le modèle qui suit formalise cela via une **catégorie (ou 2-catégorie) d'histoires**, puis une sémantique en **diagrammes** (foncteurs) au lieu de chaînes.

---

## 1) Alphabet d'événements : le "milieu" dynamique

On fixe un ensemble d'événements typés. L'idée : "le milieu" d'un LLM est une **grammaire d'événements** (pas une loss).

### 1.1 Ensemble des événements

On pose un ensemble disjoint d'événements :

* E_tok : événements "token" / production interne (ex. émission d'un token, d'un segment, d'un acte de raisonnement observable, etc.)
* E_tool : événements "outil" (appel d'outil + retour d'outil)
* E_obs : événements "observation" / feedback externe (résultat, erreur, mesure, vérification, signal utilisateur, etc.)
* E_mode : événements "changement de mode" (policy, règles, budget, prompt système, routage, garde-fous, paramètres d'échantillonnage, etc.)
* E_train : événements "mise à jour" (saut gradient, update de paramètres, changement de modèle, reconfiguration durable)

On écrit :

E = E_tok ⊔ E_tool ⊔ E_obs ⊔ E_mode ⊔ E_train

### 1.2 Remarque sur la granularité

* Rien n'impose que E_tok soit "token par token". On peut regrouper (phrase, chunk, acte, etc.).
* E_train peut être absent (cas "inference only") ou présent (systèmes continuellement ajustés, personnalisation persistante, etc.).
* E_mode est crucial : beaucoup de phénomènes LLM viennent de "la règle d'évolution qui change".

---

## 2) Géométrie de commutation : l'indépendance

On veut formaliser quand deux événements peuvent être permutés sans "changer" l'histoire pertinente.

### 2.1 Indépendance statique (version simple)

On pose une relation d'indépendance :

I ⊆ E × E

Intuition : (e1, e2) ∈ I signifie "e1 et e2 peuvent commuter" (concurrence).

Exemples typiques :

* deux lectures RAG indépendantes,
* log/trace vs action,
* certaines observations vs actions internes,
* actions dont les effets sont disjoints.

### 2.2 Indépendance contextuelle (version réaliste pour LLM)

Dans les LLM, l'indépendance dépend souvent du préfixe : un événement peut rendre un autre dépendant (ex. un appel outil produit les arguments du second).

On peut donc raffiner en :

I_h ⊆ E × E, pour chaque préfixe h

Interprétation : "à l'histoire h, e1 et e2 commutent".

Cette version est généralement la plus fidèle.

---

## 3) Catégorie (ou 2-catégorie) des histoires : H

On formalise l'espace des "histoires" comme structure combinatoire avec extensions, causalité, conflits et commutations.

Deux constructions standard (équivalentes en esprit) sont utiles.

---

### 3.A Option A : poset d'événements (event structure / pomsets)

Un objet (une histoire finie) est une structure :

* un ensemble fini d'événements présents, noté Ev(h) ⊆ E
* une relation de causalité (ordre partiel) <=_h sur Ev(h)
* une relation de conflit (incompatibilité), notée #_h

Contraintes usuelles (schématiquement) :

* la causalité est un ordre partiel,
* le conflit est symétrique et héritable (si un événement est en conflit, ses extensions le restent, etc. selon la variante).

Une flèche h -> h' est une **extension** :

* Ev(h) ⊆ Ev(h')
* les relations (causalité, conflit) sont préservées par restriction

Dans ce point de vue, H est souvent un **poset** (ou une catégorie mince) : au plus une flèche entre deux objets.

---

### 3.B Option B : catégorie de préfixes avec 2-cellules (commutations explicites)

Ici on veut rendre les commutations visibles (utile pour les LLM).

* Objets : préfixes finitisés (histoires finies)
* 1-flèches : "ajout d'un événement" (extension élémentaire)

  * h --e--> h1 signifie "on étend h en ajoutant l'événement e"
* 2-cellules : carrés de commutation, lorsque deux ajouts sont indépendants (souvent via I_h)

Schéma typique :

* h --e1--> h1 --e2--> h12
* h --e2--> h2 --e1--> h21

et une 2-cellule identifiant ces deux chemins lorsque e1 et e2 commutent dans le contexte :

(h --e1--> h1 --e2--> h12)  ≅  (h --e2--> h2 --e1--> h21)

Cette structure capture exactement l'intuition :

* "parfois l'ordre commute"
* "parfois non"
* et la commutation peut dépendre du contexte.

---

### 3.C Quoi faire des 2-cellules : quotient ou structure

Deux attitudes :

1. Quotienter (traces/pomsets)

* on identifie effectivement les ordres commutants,
* l'histoire devient une trace concurrente.

1. Garder la 2-structure

* on conserve la "géométrie des commutations",
* utile si la sensibilité au chemin de commutation est elle-même un phénomène (fréquent avec les LLM : format, style, injection, budgets, etc.).

Dans ce document, on privilégie souvent (2), car l'objectif est de ne pas écraser la dynamique réelle.

---

## 4) Exécution = diagramme (pas chaîne)

Le cœur du modèle : une exécution n'est pas une suite indexée par N, mais un **diagramme** sur H.

### 4.1 Espace d'états / cible X

On fixe une catégorie X qui représente ce qu'on considère comme "état" :

* état externe (monde, fichiers, DB, outils),
* mémoire accessible (context window, mémoire persistante, RAG),
* contraintes/policies,
* paramètres/poids (si on modélise E_train),
* ressources (budget de tokens, temps, quotas),
* etc.

Selon le niveau de réalisme, X peut être :

* déterministe (fonctionnel),
* relationnelle (nondéterminisme),
* probabiliste (kernels / distributions),
* informationnelle (états partiellement observables).

### 4.2 Exécution comme foncteur

Une exécution est un foncteur :

S : H -> X

Interprétation :

* à chaque histoire h, S(h) est l'état "réalisé/induit" après h,
* à chaque extension (flèche) h -> h', S associe une transition d'état.

### 4.3 Version probabiliste (souvent la plus fidèle aux LLM)

Pour un LLM, même à "température 0", il existe souvent :

* observation partielle,
* nondéterminisme effectif (outils, réseaux, latences),
* changements de mode.

On peut donc prendre X comme une catégorie de transformations probabilistes (ou relations). Alors S capture une **sémantique de trajectoires possibles** plutôt qu'un unique chemin.

---

## 5) Observables et clôture de préfixe ("up")

On veut formaliser le "vu jusqu'ici" de manière intrinsèque aux histoires.

### 5.1 Prédicat d'observation

On fixe un prédicat (ou une famille de prédicats) sur les histoires :

O(h) : "succès", "violation", "atteinte d'un état", "preuve trouvée", etc.

O peut dépendre de S(h) (via la sémantique) ou être défini directement sur h (via les événements observés).

### 5.2 Clôture de préfixe

On définit l'opérateur "up" :

up(O)(h) est vrai ssi il existe un préfixe h' de h tel que O(h') soit vrai.

Autrement dit : "O a déjà été observé quelque part dans le passé de h".

Cet opérateur formalise un résumé cumulatif minimal ("apparu au moins une fois").

---

## 6) Cofinalité interne : horizons sans ordinal plaqué

Le slogan "aucun horizon fini ne clôt" doit vivre dans H, pas dans un temps externe.

### 6.1 Ensembles dirigés

Un sous-ensemble D de H est dirigé si pour tout couple (h1, h2) dans D, il existe h3 dans D tel que :

* h1 -> h3 et h2 -> h3 (h3 est une extension commune)

Intuition : D représente un "avenir ouvert" où tout couple de préfixes peut être prolongé de manière compatible.

### 6.2 Cofinalité

Un sous-ensemble C de H est cofinal si pour tout h dans H, il existe c dans C tel que :

* h -> c

Intuition : C "atteint" arbitrairement loin : aucun préfixe ne l'exclut définitivement.

### 6.3 Formulation interne de "aucun horizon fini ne clôt"

Une formulation typique (adaptable) :

* Pour tout préfixe h, il existe une extension h' telle que l'événement/régime visé devienne réalisable/atteint.

Important : la propriété est formulée **dans H** (extensions, commutations, conflits), pas dans N, ni dans "Ord".

---

## 7) La limite correcte : complétion par idéaux (Scott)

L'idée : au lieu de prendre une "limite le long d'une chaîne", on complète H en ajoutant des points-limites qui représentent des exécutions potentiellement infinies sous forme d'idéaux.

### 7.1 Idéaux

Un idéal J dans H est un ensemble de préfixes qui est :

* inférieur-clos : si h est dans J et h' -> h, alors h' est dans J
* dirigé : pour tout h1, h2 dans J, il existe h3 dans J qui les prolonge (extension commune)

Intuition : un idéal est une "exécution partielle cohérente", vue comme l'ensemble de tous ses préfixes finitisés.

### 7.2 Complétion Idl(H)

On note Idl(H) l'ensemble (ou la catégorie) des idéaux de H, ordonné par inclusion (et muni de la structure de domaines usuelle).

Interprétation :

* H décrit les histoires finies,
* Idl(H) ajoute des "points limites" correspondant à des comportements prolongés.

### 7.3 Extension de la sémantique

Sous des conditions standard (selon X), une exécution S : H -> X s'étend en :

S_hat : Idl(H) -> X

Interprétation :

* une exécution prolongée est évaluée sur un idéal (un "avenir dirigé"), pas sur une étape "numérotée".

C'est ici que se voit la différence avec union→continuité→point fixe :

* la "limite" est un objet construit à partir de la géométrie dirigée de H,
* pas un passage à l'infini imposé par une indexation ordinale.

---

## 8) Où Ord réapparaît (seulement comme scheduling)

On récupère des ordinaux uniquement si l'on décide de "linéariser" la dynamique, c'est-à-dire choisir un scheduling.

### 8.1 Chaînes cofinales

Une chaîne cofinale est un morphisme (ou une application monotone) :

c : A -> H

où A est une chaîne (souvent un ordinal, ou N), et l'image de c est cofinale dans H.

Intuition : c choisit une exécution linéarisée qui "va arbitrairement loin".

### 8.2 "Transfini ZFC pertinent" = types d'ordre réalisables

Les ordinaux qui apparaissent alors ne sont pas "posés" :

* ils sont exactement les types d'ordre des chaînes cofinales que H admet.

Donc :

* changer la dynamique (donc H) change les cofinalités possibles,
* et change donc quels ordinaux peuvent apparaître comme horizons de scheduling.

C'est le sens précis de :

* "le transfini (au sens des ordinaux effectivement pertinents) dépend strictement de la dynamique".

---

## 9) Pourquoi union → continuité → point fixe décrit un faux objet

Le triptyque "standard" fabrique typiquement un objet stable qui correspond à une projection cumulée, pas à la dynamique réelle.

### 9.1 Ce que fait le triptyque (en dynamique d'histoires)

1. Imposer une linéarisation

* on choisit une chaîne (souvent N ou un ordinal) qui traverse H.

1. Projeter l'histoire sur un résumé cumulatif

* par exemple "apparu au moins une fois" (union/up) ou un autre forgetful map :

  * on écrase l'ordre, les commutations, et souvent les conflits fins.

1. Exiger une continuité qui force la commutation "résumé puis évoluer" = "évoluer puis résumer"

* ce qui est précisément ce que les LLM violent empiriquement :

  * résumer/reformuler/réordonner modifie la suite.

1. Conclure à un point fixe

* le point fixe est alors un invariant de la projection (le résumé cumulatif),
* pas un invariant de la dynamique sur H.

### 9.2 Critère de validité (quand le triptyque serait légitime)

Le schéma "résumé stable" n'est fidèle que si la sémantique factorise à travers le quotient/projection :

* si toutes les permutations déclarées commutantes sont effectivement neutres pour la sémantique,
* si la projection ne détruit pas d'information causalement pertinente.

Pour des LLM "in the wild" (modes, outils, budgets, formats, guardrails), cette factorisation échoue souvent.

---

## 10) Comment les LLM rendent ce cadre "évident"

Les LLM fournissent un laboratoire interactif de phénomènes que ce cadre formalise directement :

* Sensibilité à l'ordre :

  * deux historiques "équivalents en contenu" mais ordonnés différemment divergent.
* Commutations partielles :

  * certains ajouts (ex. deux lectures indépendantes) commutent parfois,
  * mais deviennent dépendants si le contexte change.
* Méta-dynamique :

  * changement de mode/policy/budget modifie la règle.
* Troncature et non-clôture :

  * aucune fenêtre finie ne capture "tout ce qui peut compter" si le système a des sources externes, des politiques, ou des routes alternatives.

Le cadre H + commutations + idéaux explique pourquoi la "stabilisation" obtenue par union/continuité est souvent une stabilisation de **projection**, pas de **milieu**.

---

## 11) Mini-exemples (sans math lourde)

### 11.1 Deux lectures RAG indépendantes (commutation locale)

* e1 = "lecture doc A"
* e2 = "lecture doc B"
* si e1 et e2 sont indépendants dans le préfixe h (I_h), alors les deux chemins :

  * ajouter e1 puis e2
  * ajouter e2 puis e1
    sont reliés par une 2-cellule de commutation.

Mais si la lecture A sert à construire la requête de la lecture B, alors au préfixe h :

* e1 et e2 ne commutent pas (pas de 2-cellule).

### 11.2 Changement de mode (non-commutation structurelle)

* e_mode = "appliquer une policy stricte"
* e_tok = "écrire une réponse détaillée"

Ordre 1 : policy puis rédaction

* la rédaction est contrainte dès le départ.

Ordre 2 : rédaction puis policy

* la policy peut tronquer, réécrire, ou refuser.

Même si on "résume" après coup, les trajectoires ne se réconcilient pas : non-commutation effective.

### 11.3 Idéal comme "exécution infinie possible"

Un idéal J est l'ensemble de tous les préfixes compatibles d'une exécution prolongée.
Ce n'est pas une suite numérotée :

* c'est un "futur dirigé" dans lequel toute paire de préfixes a une extension commune.

---

## 12) Checklist : ce qui rend le modèle "minimal mais complet"

* [x] Alphabet typé d'événements E (milieu)
* [x] Indépendance I (idéalement contextuelle I_h)
* [x] Catégorie/2-catégorie des histoires H (préfixes + extensions + commutations)
* [x] Exécution comme diagramme S : H -> X (et X peut être probabiliste)
* [x] Observables O et clôture up(O)
* [x] Cofinalité interne (dirigés, cofinal)
* [x] Limite correcte via Idl(H) (idéaux) et extension S_hat
* [x] Ordinaux seulement via scheduling (chaînes cofinales)
* [x] Critique structurelle du triptyque union→continuité→point fixe

---

## 13) Une phrase portable (version courte)

La blackbox structurelle des LLM vient du fait que l'objet réel est un diagramme sur une catégorie d'histoires avec commutations ; les ordinaux ne sont que des linéarisations (schedulings), et union + continuité fabrique un point fixe de la projection cumulative, pas de la dynamique.

---

## 14) Glossaire rapide

* Événement : primitive dynamique (token, outil, observation, mode, train…).
* Préfixe / histoire finie : configuration d'événements avec causalité et conflits.
* Commutation (2-cellule) : permutation légitime de deux extensions indépendantes.
* Dirigé : ensemble de préfixes où toute paire admet une extension commune.
* Cofinal : sous-ensemble qui "atteint" arbitrairement loin (tout préfixe s'y prolonge).
* Idéal : dirigé + inférieur-clos ; représente un comportement prolongé via tous ses préfixes.
* Idl(H) : complétion par idéaux ; remplace "limite d'une chaîne".
* Scheduling : choix d'une chaîne cofinale ; seul endroit où un ordinal intervient.

---

### Proposition (critère de "pas de blackbox")

Soit $\mathcal H$ la (2-)catégorie des histoires et $S:\mathcal H\to\mathcal X$ la sémantique (exécution comme diagramme).
Soit $q:\mathcal H\to Q$ une projection/résumé (quotient par commutations, "déjà-vu", compression, etc.).

On dit que **le résumé est fidèle** si et seulement s'il existe $\widetilde S:Q\to\mathcal X$ tel que
$$
S \cong \widetilde S\circ q
$$
(isomorphisme naturel : la sémantique ne dépend que du résumé).

**Alors :**

* Si $S$ factorise par $q$, il n'y a **pas** de blackbox structurelle relativement à ce résumé : deux histoires $h_1, h_2$ avec $q(h_1)=q(h_2)$ induisent le même comportement (même $S(h)$ à isomorphisme près).
* Si $S$ **ne** factorise pas par $q$, la blackbox est **structurelle** : il existe $h_1, h_2$ tels que $q(h_1)=q(h_2)$ mais $S(h_1)\not\cong S(h_2)$. Autrement dit, le comportement dépend du **chemin** dans $\mathcal H$, pas seulement du résumé.

---

### Corollaire (pour "union → continuité → point fixe")

Prends $q=\mathrm{Occ}$ ou $q=\mathrm{up}$ (projection cumulative : "apparu au moins une fois").
Si la dynamique réelle ne factorise pas par ce $q$ (cas typique des LLM à modes/sauts), alors toute stabilisation obtenue par "continuité + point fixe" concerne **$\widetilde S$ sur le résumé** (la projection cumulative), et non la dynamique $S$ sur $\mathcal H$.
Donc "union → continuité → fixpoint" produit une **stabilité de projection**, pas une stabilité du milieu.

---

---

## Encadré : Poids comme observable de la sémantique

On suppose que l'espace d'états cible $\mathcal X$ **contient** une composante "poids" $\mathcal W$ (et éventuellement d'autres composantes : mémoire, mode, ressources, état d'optimizer, etc.). On fixe une projection
$$
\pi_W:\mathcal X\to \mathcal W.
$$
Pour une exécution $S:\mathcal H\to \mathcal X$, on définit l'**observable poids**
$$
W := \pi_W\circ S:\mathcal H\to \mathcal W.
$$
Ainsi, "les poids" ne sont pas un *dedans* mystérieux : ce sont un **output** (une observable) de l'histoire.

Les événements $E_{\text{train}}$ sont alors précisément ceux dont l'action sur $\mathcal X$ modifie la composante $\mathcal W$.

---

## Corollaire : "les poids suffisent" est une propriété de factorisation (et se falsifie)

Dire que "les poids suffisent à expliquer le comportement" (relativement à une famille d'observables $O$) signifie :

> il existe $\widetilde S_W:\mathcal W\to\mathcal X$ (ou plus faiblement $\widetilde O_W:\mathcal W\to \text{Obs}$) tel que
> $$
> S \cong \widetilde S_W\circ W
> \quad\text{(ou)}\quad
> O\circ S \cong \widetilde O_W\circ W.
> $$

**Test falsifiable :** s'il existe $h_1, h_2$ tels que
$$
W(h_1)=W(h_2)
\quad\text{mais}\quad
O(S(h_1))\neq O(S(h_2)),
$$
alors les poids **ne suffisent pas** : il existe une dépendance à une autre composante de l'état (mode/policy, mémoire, ressources, RNG, état d'optimizer, etc.) ou au **chemin** dans $\mathcal H$ que $W$ n'encode pas.

---

## Quotient "anti–boîte noire" canonique (relatif à des observables)

Fixe une famille d'observables $\mathcal O=\{O_i:\mathcal X\to \text{Obs}_i\}$. Définis une relation sur les histoires :
$$
h \sim_{\mathcal O} h'
\quad\Longleftrightarrow\quad
\forall i,\; O_i(S(h)) \cong O_i(S(h')).
$$
Alors le quotient $q_{\mathcal O}:\mathcal H\to \mathcal H/_{\sim_{\mathcal O}}$ est, par construction, un **résumé maximalement compressif** qui élimine la boîte noire **pour $\mathcal O$** : on a automatiquement une factorisation
$$
(O_i\circ S) \cong \widetilde O_i \circ q_{\mathcal O}
\quad\text{pour tout }i.
$$
La "boîte noire" devient donc exactement : *avoir choisi un résumé $q$ plus grossier que $q_{\mathcal O}$* (ou avoir demandé des observables trop fines).

---

## Lien avec "Ord = scheduling" quand les poids sont outputs

Si $E_{\text{train}}$ est présent, alors différents schedulings (chaînes cofinales dans $\mathcal H$) peuvent produire des trajectoires de poids différentes. Les ordinaux pertinents ne sont toujours pas posés : ils réapparaissent comme **types d'ordre de linéarisations cofinales** admissibles par la dynamique d'updates (et par les contraintes de commutation/conflit).

---

### Ce que cet encadré clarifie, net

* **Oui**, dans ce cadre, les poids ne sont pas la boîte noire : ce sont un output $W(h)$.
* La question "boîte noire" devient : *peut-on remplacer l'histoire par un résumé petit $q$ (idéalement bien plus petit que $W$) sans perdre la sémantique pertinente ?*
* Et ça se formule **exactement** en factorisation.

---

## Hypothèses techniques (verrouillage)

Pour que le cadre ci-dessus soit un **théorème** (et non seulement un programme sémantique), on fixe les conventions suivantes :

### 1. Deux niveaux : analyse 2D / complétion Scott

On distingue deux niveaux :

* **(i) Analyse 2D** : on garde la 2-structure (carrés de commutation) pour étudier la sensibilité au chemin.
* **(ii) Complétion** : `Idl(H)` s'applique au **poset quotient** $\mathcal H / \sim$ obtenu en identifiant les chemins reliés par 2-cellules (commutations neutres).

### 2. Équivalence sur les observables

L'isomorphisme $\cong$ dans $\mathcal X$ est défini **relativement à une famille d'observables $\mathcal O$** :
$$
S(h_1) \cong S(h_2) \quad\Longleftrightarrow\quad \forall i,\; O_i(S(h_1)) \stackrel{\text{loi}}{=} O_i(S(h_2)).
$$
Par défaut, « même loi sur les observables fixées ».

### 3. Extension $\widehat S$ sur Idl(H)

On suppose :

* $\mathcal X$ admet les **colimites dirigées** (diagrammes indexés par des ensembles dirigés),
* $S$ les préserve.

L'extension est alors définie par :
$$
\widehat S(J) := \mathrm{colim}_{h \in J}\, S(h) \quad (J\ \text{idéal dirigé}).
$$

### 4. Cohérence de l'indépendance $I_h$ : diamants locaux

On n'impose **pas** la monotonicité de $I_h$. La condition de cohérence est :

> **Diamants locaux.** Si à un préfixe $h$ les extensions $h \xrightarrow{e_1} h_1$ et $h \xrightarrow{e_2} h_2$ existent, alors :
>
> * **(i)** soit il existe $h_{12}$ tel que $h_1 \xrightarrow{e_2} h_{12}$ et $h_2 \xrightarrow{e_1} h_{12}$, et on déclare une 2-cellule (commutation),
> * **(ii)** soit les deux prolongements existent mais il n'y a pas d'état commun $h_{12}$ rendant le carré commutatif (non-commutation effective : l'ordre importe).

Intuition : l'indépendance peut se **perdre** en avançant (ex. lecture A produit la requête de B), ou se **gagner** (contrainte levée). Elle n'est pas monotone.

### 5. Poids élargis

L'observable $W$ inclut l'**état d'apprentissage complet** :
$$
W := (\theta, \text{optimizer\_state}, \text{buffers}, \text{rng})
$$
et non $\theta$ seul. Sans cela, le test de factorisation échoue trivialement (état d'optimizer différent).

---

> **Sous (1–5)**, la construction $\widehat S$ est bien définie (à iso près) et le critère de factorisation $S \simeq \widetilde S \circ q$ est invariant par passage aux idéaux.
