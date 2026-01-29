# Dynamique minimale d'un agent : catégorie d'histoires, commutations, cofinalité interne, complétion

## LLM "en situation" comme cas-laboratoire

---

# Partie I — Théorie fondationnelle (agent en milieu)

## 0. Idée directrice

L'objet premier n'est pas une suite d'états indexée par $\mathbb{N}$ (ni par un ordinal), mais une **dynamique d'événements** organisée en histoires, où :

* l'ordre des sauts compte ;
* certaines opérations commutent localement, d'autres pas ;
* la dynamique n'a pas d'horizon fini naturel ;
* les "ordinaux pertinents" n'apparaissent qu'après coup, comme types d'ordre de schedulings possibles.

> **Principe** : on ne part pas d'un temps externe, on part d'une géométrie interne d'histoires.

---

## 1. Données primitives (le milieu)

On fixe un alphabet typé d'événements (la typologie est utile mais non obligatoire) :

| Type | Description |
|------|-------------|
| $E_{\text{tok}}$ | Production interne (token, chunk, acte de rédaction, acte de calcul) |
| $E_{\text{tool}}$ | Actions d'outil (appel / retour) |
| $E_{\text{obs}}$ | Observations externes (résultats, erreurs, mesures, feedback) |
| $E_{\text{mode}}$ | Changements de régime (policy, garde-fous, budget, routage, paramètres) |
| $E_{\text{train}}$ | Mises à jour durables (update de paramètres, reconfiguration persistante) |

On note $E$ la somme disjointe de ces familles :
$$
E = E_{\text{tok}} \sqcup E_{\text{tool}} \sqcup E_{\text{obs}} \sqcup E_{\text{mode}} \sqcup E_{\text{train}}
$$

### 1.1. Extensions admissibles

Une histoire n'est pas une liste brute : c'est un objet qui supporte des **extensions légales**.

On se donne une règle d'extension :

> À chaque préfixe $h$, on associe $\text{Enabled}(h) \subseteq E$, les événements activables après $h$.

$\text{Enabled}(h)$ encode :

* permissions, disponibilité d'outils, budget restant ;
* dépendances de données (un événement produit une donnée requise par un autre) ;
* contraintes de sécurité/policy.

**Point clé** : $\text{Enabled}(h)$ appartient au milieu, pas à une horloge externe.

### 1.2. Commutation locale (indépendance contextuelle)

On ne postule pas d'indépendance globale. On se donne une **commutation locale**, relative à un préfixe :

> Pour chaque préfixe $h$, une relation $I_h \subseteq \text{Enabled}(h) \times \text{Enabled}(h)$.

**Lecture** : $(e_1, e_2) \in I_h$ signifie "à ce stade $h$, on peut permuter $e_1$ et $e_2$ sans changer ce qui est pertinent".

$I_h$ peut varier avec $h$ : la commutation est un phénomène local attesté, pas un axiome global.

---

## 2. Constructeur canonique : la 2-géométrie des histoires (niveau analyse 2D)

On construit l'objet fondationnel "géométrie des histoires" : on ne postule pas $\mathcal{H}$, on le **génère**.

### 2.1. $\mathcal{H}_2$ : structure libre engendrée par extensions + commutations locales

| Niveau | Structure |
|--------|-----------|
| **Objets** | Préfixes (histoires finies) |
| **1-flèches** | Extensions élémentaires : si $e \in \text{Enabled}(h)$, alors $h \xrightarrow{e} h \cdot e$ |
| **2-cellules** | Carrés de commutation lorsque la commutation est attestée localement |

#### Diamants locaux (cohérence minimale)

Si depuis un même préfixe $h$, on peut faire $h \xrightarrow{e_1} h_1$ et $h \xrightarrow{e_2} h_2$, alors il y a trois situations :

1. **Commutation** : on peut prolonger des deux côtés et recoller dans une histoire commune $h_{12}$, et on atteste une 2-cellule (les deux ordres sont équivalents).
2. **Non-commutation** : les deux ordres existent mais ne se recollent pas (pas de 2-cellule). L'ordre est un fait structurel.
3. **Dépendance dure** : l'un des ordres bloque (une extension n'existe pas). L'ordre est contraint.

Cette 2-géométrie encode "parfois ça commute, parfois non" sans écraser les différences de chemin.

---

## 3. Constructeur canonique : base posetale pour les limites (niveau complétion)

La complétion par idéaux est naturellement posetale. Pour rester fondationnel sans alourdir en théorie des présheaves, on passe par une base canonique.

### 3.1. $\mathcal{H}$ : quotient posetal des commutations déclarées neutres

On forme le poset $\mathcal{H}$ ainsi :

1. On part des objets de $\mathcal{H}_2$ ;
2. On identifie les préfixes reliés par une chaîne de 2-cellules (commutations déclarées neutres) ;
3. On ordonne par extension : $[h] \leq [h']$ si $h'$ est atteignable depuis $h$ par une suite d'extensions.

**Lecture** :

* $\mathcal{H}_2$ sert à analyser la **sensibilité au chemin** (niveau 2D) ;
* $\mathcal{H}$ sert à construire les **points-limites** (idéaux) de façon canonique.

---

## 4. Cofinalité interne et futur ouvert

Sur le poset $\mathcal{H}$ :

| Concept | Définition |
|---------|------------|
| **Ensemble dirigé** | Toute paire de préfixes y admet un prolongement commun |
| **Ensemble cofinal** | Tout préfixe de $\mathcal{H}$ se prolonge dans cet ensemble |

**Interprétation** :

* "pas d'horizon fini" est une propriété interne : pour tout préfixe, il existe des extensions non bloquées ;
* On ne met pas d'ordinal ici : on parle d'extensions, de dirigés, de cofinalité.

---

## 5. Constructeur canonique : complétion par idéaux

### 5.1. Idéaux

Un idéal $J$ de $\mathcal{H}$ est un ensemble de préfixes qui est :

* **Inférieur-clos** : si $h \in J$ et $h' \leq h$, alors $h' \in J$ ;
* **Dirigé** : toute paire dans $J$ admet un prolongement commun dans $J$.

Un idéal représente une exécution prolongée comme "tous ses préfixes compatibles".

### 5.2. $\text{Idl}(\mathcal{H})$

$\text{Idl}(\mathcal{H})$ est l'ensemble des idéaux, ordonné par inclusion.

**Lecture fondationnelle** :

* $\text{Idl}(\mathcal{H})$ ajoute exactement les "points-limites" nécessaires pour représenter des futurs dirigés.
* On n'ajoute pas "l'infini" par un index ; on le construit depuis la compatibilité interne.

---

## 6. Sémantique : exécution comme diagramme

### 6.1. Cible $\mathcal{X}$

On fixe $\mathcal{X}$, qui représente l'état pertinent :

* monde externe (outils, fichiers, DB),
* mémoire (fenêtre de contexte, mémoire persistante, RAG),
* modes/policies,
* ressources (budget, quotas),
* paramètres, si présents.

$\mathcal{X}$ peut être déterministe, relationnelle, ou probabiliste.

### 6.2. Exécution

Une exécution est un diagramme :
$$
S : \mathcal{H}_2 \to \mathcal{X} \quad\text{(niveau 2D)}
\qquad\text{ou}\qquad
S : \mathcal{H} \to \mathcal{X} \quad\text{(niveau quotient)}
$$

**Lecture** :

* à chaque préfixe, un état ;
* à chaque extension, une transition ;
* les 2-cellules (si gardées) représentent les commutations sémantiques acceptées comme neutres.

---

## 7. Observables et "boîte noire" comme défaut de factorisation

### 7.1. Observables

On fixe une famille d'observables $\mathcal{O} = \{O_i\}$ :

* succès / violation,
* exactitude, coût, format,
* etc.

Chaque $O_i$ prend un état de $\mathcal{X}$ et renvoie une valeur observable (ou une loi, si probabiliste).

### 7.2. Équivalence pertinente

Deux états sont équivalents relativement à $\mathcal{O}$ si toutes les observables coïncident (ou ont même loi).

> "Comprendre" est toujours relatif à ce qu'on exige de préserver.

### 7.3. Résumé fidèle

Un résumé est une application $q : \mathcal{H} \to Q$ (compression, quotient, "déjà-vu", etc.).

$q$ est **fidèle** pour $\mathcal{O}$ si les observables après exécution ne dépendent que de $q(h)$.

**Conséquence** :

* si $q$ est fidèle : pas de boîte noire structurelle relativement à $q$ ;
* sinon : boîte noire structurelle, dépendance au chemin.

### 7.4. Quotient canonique anti–boîte noire (relatif aux observables)

On définit l'indiscernabilité sur $\mathcal{H}$ :
$$
h \sim_{\mathcal{O}} h' \quad\Longleftrightarrow\quad \forall i,\; O_i(S(h)) = O_i(S(h')).
$$

On obtient $Q_{\mathcal{O}} = \mathcal{H} / {\sim_{\mathcal{O}}}$, et la projection $q_{\mathcal{O}} : \mathcal{H} \to Q_{\mathcal{O}}$.

**Propriété fondationnelle** :

* $q_{\mathcal{O}}$ est le résumé maximalement compressif qui élimine la boîte noire pour $\mathcal{O}$ ;
* tout résumé fidèle factorise par $q_{\mathcal{O}}$ (c'est la "bonne abstraction minimale" relative à $\mathcal{O}$).

---

## 8. Paramètres/poids comme outputs (si $E_{\text{train}}$ est présent)

Si la mise à jour existe, les poids sont une **composante observable** de l'état, pas un "dedans" métaphysique.

On fixe une projection "poids" $\pi_W : \mathcal{X} \to \mathcal{W}$, où $\mathcal{W}$ inclut l'état d'apprentissage complet :

* paramètres $\theta$,
* état d'optimizer,
* buffers,
* RNG/seed si pertinent.

On définit l'observable poids :
$$
W(h) := \pi_W(S(h)).
$$

Dire "les poids suffisent" devient une propriété :
> Toutes les observables factorisent via $W$.

---

## 9. Extension aux idéaux

Pour interpréter des exécutions prolongées, on demande à $\mathcal{X}$ d'admettre les colimites correspondant aux futurs dirigés, et à $S$ de les préserver.

On définit alors $\widehat{S}$ sur $\text{Idl}(\mathcal{H})$ :
$$
\widehat{S}(J) := \mathrm{colim}_{h \in J}\, S(h) \quad (J\ \text{idéal dirigé}).
$$

Une exécution prolongée est évaluée sur un idéal (un futur dirigé), pas sur une étape numérotée.

---

## 10. Où Ord réapparaît : uniquement comme scheduling

Un **scheduling** est une linéarisation :

* une chaîne $A$ et une application monotone $c : A \to \mathcal{H}$ dont l'image est cofinale.

Les ordinaux n'interviennent qu'**après coup** :

* comme types d'ordre possibles de schedulings cofinaux admissibles.

> Changer la géométrie de $\mathcal{H}$ change les schedulings admissibles, donc change le "transfini pertinent".

---

## 11. Critique structurelle : itération + continuité + point fixe

Le schéma standard :

1. Impose une linéarisation,
2. Projette vers un résumé cumulatif qui oublie l'ordre et les non-commutations,
3. Conclut à un point fixe sur ce résumé.

Dans ce cadre :

* on voit que le point fixe obtenu est un invariant de la **projection**,
* pas un invariant de la **dynamique d'histoires**.

> **Critère de légitimité** : ce schéma n'est fidèle que si la sémantique observée factorise réellement par le résumé.

---

## 12. Phrase fondationnelle

> Ce cadre n'est pas une reformulation : il **inverse la hiérarchie standard** "temps ordinal → dynamique". Ici, la dynamique est première (géométrie interne des histoires) et l'ordinal n'apparaît qu'après coup, comme type d'ordre de schedulings admissibles. En particulier, les preuves fondées sur itération, continuité et point fixe portent souvent sur une abstraction imposée, pas sur l'objet dynamique.

---

# Partie II — Lien avec les LLM (instanciation, diagnostics, phénomènes)

## A. Pourquoi les LLM rendent la théorie visible

Les LLM "en situation" exhibent naturellement :

* **Non-commutations massives** : ordre des instructions, ordre des preuves, ordre des filtrages ;
* **Commutations locales** : requêtes RAG indépendantes, logs, certaines vérifications ;
* **Événements de mode** : policies, garde-fous, budgets, routage, outils ;
* **Observations externes** : retours d'outils, erreurs réseau, latences, confirmations.

> Ils ne fondent pas la théorie : ils fournissent un **laboratoire** où ses primitives sont immédiatement observables.

---

## B. Correspondance concrète des primitives

| Primitive | Instanciation LLM |
|-----------|-------------------|
| $E_{\text{tok}}$ | Segments produits (raisonnement visible, plan, réponse, reformulation) |
| $E_{\text{tool}}$ | Appel outil + retour outil |
| $E_{\text{obs}}$ | Erreur d'API, "document introuvable", résultat de recherche, feedback utilisateur |
| $E_{\text{mode}}$ | Changement de policy, activation d'un filtre, baisse de budget, changement de modèle |
| $E_{\text{train}}$ | Adaptation persistante (fine-tuning, RLHF en ligne), ou absent en "inference only" |
| $\text{Enabled}(h)$ | "Outil autorisé / non autorisé", "assez de budget", "prompt a fourni les arguments" |
| $I_h$ | Deux lectures RAG indépendantes (tant qu'aucune ne paramètre l'autre) |

---

## C. Deux mini-scènes qui illustrent la structure

### 1. RAG parallèle

Deux lectures de documents indépendants commutent souvent.
Mais si la première lecture sert à construire la requête de la seconde, la commutation **disparaît** à ce préfixe.

### 2. Mode/policy

"Appliquer policy stricte puis rédiger" ≠ "rédiger puis appliquer policy".
Les deux chemins existent, mais ne se recollent pas : **non-commutation structurelle**.

---

## D. Ce que le cadre apporte en pratique sur un LLM

| Application | Diagnostic |
|-------------|------------|
| **Non-reproductibilité** | Localiser la divergence comme non-commutation (souvent mode/budget/outils) |
| **Parallélisation sûre** | Identifier où $I_h$ est attesté, et où il ne l'est pas |
| **Compression/mémoire** | Tester si un résumé $q$ est fidèle pour des observables $\mathcal{O}$ |
| **Gouvernance** | Exprimer des contraintes structurelles comme contraintes sur $\text{Enabled}(h)$ |

---

## E. Définition claire de "boîte noire" sur un LLM

> La boîte noire n'est pas "les poids".
> C'est le fait que le résumé choisi (log, mémoire compressée, "déjà-vu") ne suffit pas à reconstruire les observables, donc que le comportement dépend du chemin.

Autrement dit : la boîte noire devient un **défaut d'abstraction**, testable par non-factorisation.

---

# Partie III — Observable, fibres, et monodromie : la dépendance au chemin comme holonomie

## 13.0. Idée directrice

Dans ce cadre, "faire un quotient" (résumé $q$) n'est pas l'objet ultime. Le point plus fondamental est :

* Une observable ne se contente pas d'écraser de l'information ;
* Elle définit, au-dessus de chaque histoire, une **fibre d'ambiguïté** (les micro-états compatibles avec la même observation) ;
* La dépendance au chemin apparaît alors comme une **monodromie** : les boucles (chemins fermés admissibles) agissent sur ces fibres.

> **Moralement** : la non-canonicité n'est pas seulement une perte d'information, c'est un **tressage** (holonomie) induit par la dynamique.

---

## 13.1. Données minimales (rappel autocontenu)

On suppose données :

| Donnée | Description |
|--------|-------------|
| $\mathcal{H}_2$ | 2-géométrie d'histoires (objets = préfixes, 1-flèches = extensions, 2-cellules = commutations) |
| $S : \mathcal{H}_2 \to \mathcal{X}$ | Sémantique (exécution) |
| $O : \mathcal{X} \to V$ | Observable (ou famille d'observables) |

On pose la composition :
$$
F := O \circ S : \mathcal{H}_2 \to V
$$

$F$ est "ce que le système montre" quand on ne regarde que via $O$.

> **Convention.** Dans ce texte, une observable lit l'état attaché à un préfixe (objet). Les observables de type coût/latence/trace sont modélisées en les intégrant dans l'état ($\mathcal{X}$ contient compteurs, logs, budgets, etc.).

> **Lien $\mathcal{O}$ vs $O$.** Dans la Partie III on fixe une observable particulière $O$ (ou un produit d'observables) extraite de la famille $\mathcal{O}$. En pratique on peut prendre $O = \prod_i O_i$.

---

## 13.2. Fibres : ce que l'observable ne voit pas (version robuste)

On fixe une observable (ou une famille d'observables) $O : \mathcal{X} \to V$.
Ici $V$ peut être :

* un ensemble de valeurs (déterministe),
* un espace de lois / distributions (probabiliste),
* ou un produit de plusieurs cibles si $O$ regroupe plusieurs critères (format, coût, sécurité, etc.).

Pour un préfixe $h$, on note :

* $x_h := S(h)$ l'état dans $\mathcal{X}$,
* $v_h := O(x_h)$ sa valeur observable.

**Définition (fibre d'ambiguïté au-dessus d'une observation).**

La fibre au-dessus de $v$ est l'ensemble (ou classe) des états observablement indiscernables :
$$
\mathrm{Fibre}(v) := \{ x \in \mathrm{Obj}(\mathcal{X}) \mid O(x) = v \}.
$$

Et la fibre "au-dessus de l'histoire" $h$ est :
$$
\mathrm{Fibre}(h) := \mathrm{Fibre}(v_h).
$$

**Lecture.**
$\mathrm{Fibre}(h)$ est l'espace des micro-états compatibles avec ce que l'observable voit à l'étape $h$. C'est la "part cachée" relative à $O$.

---

## 13.3. Transport : comment une extension agit sur les fibres

Soit une 1-flèche (extension) $a : h \to h'$ dans $\mathcal{H}_2$.
La sémantique donne une transition $S(a)$ dans $\mathcal{X}$.

Pour obtenir une notion opérationnelle de "transport sur la fibre", on distingue deux cas.

### Cas (A) : sémantique fonctionnelle (dynamique déterministe)

On suppose que chaque extension $a$ induit une fonction sur les états :
$$
f_a : \mathrm{Obj}(\mathcal{X}) \to \mathrm{Obj}(\mathcal{X}),
$$
et que $S(h') = f_a(S(h))$.

Alors on obtient un transport :
$$
T_a : \mathrm{Fibre}(h) \to \mathrm{Fibre}(h'),
$$
défini par $T_a(x) := f_a(x)$, **là où cela a un sens** (i.e. on applique la même transition au micro-état).

### Cas (B) : sémantique relationnelle/probabiliste (dynamique non déterministe)

Si la transition n'est pas une fonction mais une relation, un noyau probabiliste, ou une API avec effets de bord, alors le "transport" n'est plus une fonction mais une **correspondance** :
$$
T_a \subseteq \mathrm{Fibre}(h) \times \mathrm{Fibre}(h'),
$$
où $(x, y) \in T_a$ signifie "le micro-état $x$ peut évoluer en $y$ via $a$".

> **Point clé.** Dans les systèmes agentiques (LLM + outils + budgets + IO), le cas (B) est souvent le bon modèle minimal.

---

## 13.4. Carrés de commutation et holonomie : la dépendance au chemin là où l'observable est aveugle

Le phénomène essentiel n'est pas seulement "deux chemins donnent des observations différentes". C'est :

> **Même quand l'observable ne distingue pas deux chemins, le transport sur la partie cachée peut différer.**

Le bon objet de base n'est donc pas une "boucle" au sens naïf, mais un **carré de commutation** (une 2-cellule) dans $\mathcal{H}_2$.

> **Convention (transport le long d'un chemin).** Pour un chemin $p = a_1 ; \ldots ; a_m$, on note $T_p$ la composition des transports élémentaires : composition de fonctions en cas (A), composition relationnelle en cas (B).

### Définition (carré observable)

On considère une 2-cellule (un diamant de commutation) :

* deux chemins $p$ et $q$ de $h$ vers un même but $k$,
* et une 2-cellule attestant qu'ils sont "équivalents au niveau $\mathcal{H}_2$" :

$$
p : h \to k, \quad q : h \to k, \quad p \Rightarrow q.
$$

Ici, l'observation finale est la même (même objet $k$), donc ce n'est **pas** là que se loge l'intérêt.

### Définition (défaut d'holonomie / monodromie relative à O)

On compare les transports induits sur la fibre de départ :

| Cas | Structure du transport |
|-----|------------------------|
| **(A) Fonctionnel** | $T_p, T_q : \mathrm{Fibre}(h) \to \mathrm{Fibre}(k)$ (applications) |
| **(B) Relationnel** | $T_p, T_q \subseteq \mathrm{Fibre}(h) \times \mathrm{Fibre}(k)$ (correspondances) |

On définit alors le **défaut d'holonomie** comme la relation sur la fibre de départ :
$$
\mathrm{Hol}(p, q) \subseteq \mathrm{Fibre}(h) \times \mathrm{Fibre}(h),
$$
donnée par :

* $(x, x') \in \mathrm{Hol}(p, q)$ ssi $T_p(x)$ et $T_q(x')$ "coïncident" au but.

Concrètement :

| Cas | Condition pour $(x, x') \in \mathrm{Hol}(p, q)$ |
|-----|------------------------------------------------|
| **(A)** | $T_p(x) = T_q(x')$ dans $\mathrm{Fibre}(k)$ |
| **(B)** | $\exists y \in \mathrm{Fibre}(k)$ tel que $(x, y) \in T_p$ et $(x', y) \in T_q$ |

**Interprétation (terminologie précise).**

* **Holonomie faible** : la diagonale est incluse dans $\mathrm{Hol}(p, q)$, i.e. $\forall x,\, (x, x) \in \mathrm{Hol}(p, q)$ (recollage possible sans twist).
* **Holonomie forte (strictement triviale)** : $\mathrm{Hol}(p, q)$ est exactement la diagonale, i.e. $(x, x') \in \mathrm{Hol}(p, q) \Rightarrow x' = x$.
* **Holonomie tordue** : il existe $x \neq x'$ tels que $(x, x') \in \mathrm{Hol}(p, q)$. L'ordre "ne compte pas observablement", mais il **tord** la partie cachée.

---

## 13.5. Quand on obtient une vraie "monodromie" au sens groupe (cas inversible)

Si, dans un régime particulier (rare mais parfois pertinent), les transports sont **bijectifs** sur les fibres (cas (A) avec bijections, ou micro-dynamique réversible), alors :

* $T_p$ et $T_q$ sont des bijections $\mathrm{Fibre}(h) \to \mathrm{Fibre}(k)$,
* et on peut définir un automorphisme de fibre (une vraie monodromie) :

$$
\mathrm{Mono}(p, q) := T_q^{-1} \circ T_p \in \mathrm{Aut}(\mathrm{Fibre}(h)).
$$

**Lecture.**
Dans ce cas spécial, les carrés engendrent une action (représentation) du "groupoïde des déformations de scheduling" sur les fibres.

> **Définition (groupoïde des déformations).** On considère le groupoïde $\mathcal{G}_W$ engendré par les chemins de $\mathcal{H}_2$ en **inversant formellement** les 2-cellules de $W$ (déformations admissibles de scheduling). L'action sur les fibres est la représentation de monodromie.

> **Dans le cas général (non-inversible)**, la bonne notion est la **correspondance d'holonomie** $\mathrm{Hol}(p, q)$ ci-dessus.

---

## 13.5bis. Pourquoi c'est plus fondamental (synthèse)

| Niveau | Ce qu'il capture |
|--------|------------------|
| Quotient $q_{\mathcal{O}}$ (Partie I) | Ce que l'observable **voit** |
| Fibre $\mathrm{Fibre}(h)$ | Ce que l'observable **ne voit pas** |
| Holonomie $\mathrm{Hol}(p, q)$ | Comment l'**ordre** agit sur ce que l'observable ne voit pas |

On ne fait pas que diagnostiquer une perte d'info ; on identifie l'**obstruction structurelle** à la canonicité : la dynamique peut être "plate" (holonomie triviale) ou "tordue" (holonomie non triviale) relativement à $O$.

> **Lien explicite $q_{\mathcal{O}}$ vs $\mathrm{Hol}$.** Le quotient $q_{\mathcal{O}}$ (Partie I) élimine la non-canonicité au niveau des **objets** (préfixes) relativement à $O$. L'holonomie mesure la non-canonicité résiduelle au niveau des **chemins**, i.e. l'action des déformations admissibles sur la partie cachée (fibres) que $q_{\mathcal{O}}$ ne capture pas.

---

La cyclotomie fournit un modèle canonique où tout cela est visible :

| Cyclotomie | Cadre des histoires |
|------------|---------------------|
| $\widehat{\mu}$ (ou $\widehat{\mathbb{Z}}(1)$, racines de l'unité pro-finies) | Objet "limite" $\widehat{\mathcal{H}}$ |
| "Niveau $n$" (réduction mod $\mu_n$) | Observable $O$ (troncature vers quotient fini) |
| Fibre au niveau $n$ | "Choix d'un générateur / racine primitive" ($\varphi(n)$ choix) |
| $\widehat{\mathbb{Z}}^\times \to (\mathbb{Z}/n\mathbb{Z})^\times$ | Groupe de monodromie agissant sur la fibre |

**Exemple canonique aligné avec Partie I** : prendre $\mathcal{H} = (\mathbb{N}_{\geq 1}, \mid)$ (divisibilité), dont les idéaux sont les "niveaux de compatibilité".

**Interprétation** :

* $\varphi(n)$ = **taille de la fibre** au niveau $n$ (nombre de choix de générateur).
* $(\mathbb{Z}/n\mathbb{Z})^\times$ n'est pas "un quotient externe arbitraire" : c'est le **groupe de monodromie** / symétries agissant sur cette fibre.

Le vrai objet fondamental est donc :
> "fibre + action" (un **torseur** sous le groupe de monodromie), plutôt que le seul comptage $\varphi(n)$.

Ainsi, le "plus fondamental" que $\varphi(n)$, c'est l'existence d'une structure :

* un espace de choix (fibre),
* et une action canonique (monodromie),
dont $\varphi(n)$ est seulement la cardinalité finitaire.

---

## 13.7. Conséquence méthodologique (diagnostic universel)

Ce cadre donne un **principe d'audit universel** :

1. **Fixer** les observables $\mathcal{O}$ (ce que tu veux préserver).
2. **Construire** les fibres $\text{Fibre}(h)$ (ce que $\mathcal{O}$ ne voit pas).
3. **Identifier** les boucles admissibles (variantes de scheduling, commutations, modes).
4. **Mesurer** la monodromie : les boucles agissent-elles trivialement sur les fibres ?

| Résultat | Interprétation |
|----------|----------------|
| Monodromie **triviale** | Dépendance au chemin = artefact (au moins relativement à $\mathcal{O}$) |
| Monodromie **non triviale** | Non-canonicité structurelle relative à $\mathcal{O}$, localisable |

---

## 13.8. Phrase de clôture (résumé portable)

> Une observable ne définit pas seulement un quotient ; elle définit un **faisceau de fibres d'ambiguïté** sur l'espace des histoires. La dépendance au chemin est la **monodromie** de ce faisceau. Les invariants finitaires (comme $\varphi(n)$) sont des tailles de fibres ; l'objet fondamental est la **représentation de monodromie** induite par l'interaction entre dynamique et observable.

---

# Partie IV — "mod n" comme observable de résolution : aliasing et holonomie résiduelle

## 14.0. Idée directrice

Dans ce cadre, "mod $n$" n'est pas une opération primitive. C'est un cas particulier de :

* choix d'une observable $O$ (résolution),
* quotient canonique $q_{\mathcal{O}}$ (ce qui est visible),
* fibres (ce qui est perdu),
* holonomie (comment l'ordre agit sur ce qui est perdu).

> **Ainsi, "mod $n$" devient une théorie de la compression** : elle explique quand le quotient est fidèle et ce que cache l'aliasing.

> **Cadrage.** La Partie I quotient les préfixes (objets). La Partie III mesure l'obstruction qui subsiste au niveau des chemins (2D), donc au niveau des schedulings. La Partie IV réinterprète "mod $n$" dans ce cadre.

---

## 14.1. Observable de résolution et quotient induit

On appelle **observable de résolution** toute observable $O$ qui oublie de l'information de manière contrôlée (troncature, quantification, compression, projection).

Dans les situations "mod $n$", on a typiquement :

* une tour (ou un pro-état) canonique à haute résolution,
* et une projection vers un niveau fini de résolution.

Dans le langage de la Partie I, le quotient pertinent est toujours :
$$
q_{\mathcal{O}} : \mathcal{H} \to Q_{\mathcal{O}}
$$
où $Q_{\mathcal{O}}$ est obtenu par indiscernabilité observable (§7.4).

> **"mod $n$"** = le quotient canonique associé à l'observable "résolution $n$".

**Structure de tour (cofiltrée).** Une famille $(O_n)_{n \geq 1}$ est une **tour d'observables** si pour tout $m \mid n$ il existe une application $\pi_{n \to m}$ telle que $O_m = \pi_{n \to m} \circ O_n$.

On lit alors "résolution plus fine" : $n$ plus grand (ou divisible par plus de choses) donne une observation plus riche, et $m \mid n$ est une perte d'information contrôlée. Cela fait le pont avec le poset $(\mathbb{N}_{\geq 1}, \mid)$ et l'idée "pro-niveau canonique → ombres finies".

---

## 14.2. Aliasing : non-injectivité et perte de canonicité

Une observable de résolution $O$ induit en général des fibres non triviales :

* $\mathrm{Fibre}(h)$ large = beaucoup de micro-états deviennent indistinguables.

Cette non-injectivité produit un phénomène structurel :

> **Aliasing** : plusieurs histoires / micro-états distincts donnent la même observation.

Dans ce cadre, l'aliasing n'est pas "une erreur" ; c'est un **effet géométrique** contrôlé par :

* la taille/structure des fibres,
* et les contraintes de commutation ($\mathcal{H}_2$).

---

## 14.3. Critère de fidélité du quotient (quand "mod n" est légitime)

Le quotient "mod $n$" (ou plus généralement $q_{\mathcal{O}}$) est **légitime** relativement à une famille d'observables cibles $\mathcal{O}'$ si :

> Les observables cibles factorisent par $q_{\mathcal{O}}$.

**Forme pratique** :

* si $h$ et $h'$ ont la même classe $q_{\mathcal{O}}(h) = q_{\mathcal{O}}(h')$,
* alors toutes les observables $\mathcal{O}'$ coïncident après exécution.

Sinon, "mod $n$" crée une **boîte noire** : la compression détruit de l'information requise.

---

## 14.4. Ce que mesure l'holonomie : path-dependence invisible au quotient

Même si le quotient $q_{\mathcal{O}}$ est fidèle sur les objets (préfixes), il peut subsister une **non-canonicité sur les chemins**.

C'est exactement ce que mesure :
$$
\mathrm{Hol}(p, q) \quad\text{(Partie III)}
$$
pour des carrés $p \Rightarrow q$ qui sont indistinguables au niveau de l'observable, mais dont le transport sur la fibre diffère.

| Niveau | Ce qu'il supprime |
|--------|-------------------|
| $q_{\mathcal{O}}$ | Non-canonicité au niveau des **états observés** |
| $\mathrm{Hol}$ | Non-canonicité résiduelle au niveau de **ce qui reste caché** |

> **Donc $\mathrm{Hol}$ est l'obstruction intrinsèque à une description totalement canonique à résolution fixée.**

---

## 14.5. Lecture cyclotomique (ancrage rapide)

Dans la cyclotomie :

| Concept | Instanciation |
|---------|---------------|
| "mod $n$" | Observable de résolution |
| Fibres | Choix de générateurs (racines primitives) |
| Monodromie | Action des symétries sur ces choix |
| $\varphi(n)$ | Taille de la fibre |

Ce que le cadre ajoute n'est pas une nouvelle arithmétique, mais une **lecture structurelle** :

* $\varphi(n)$ n'est pas "le fondamental" ;
* le fondamental est "fibre + action" ;
* et le quotient de résolution produit automatiquement ce couple.

---

## 14.6. Lecture LLM (ancrage rapide)

Dans un agent/LLM, "mod $n$" apparaît sous forme de :

| Compression | Exemple |
|-------------|---------|
| Mémoire | Truncation de contexte, sliding window |
| Logs | Résumés de traces, agrégation |
| Scores | Quantification, seuils |
| Budgets | Compteurs agrégés, limites discrètes |

**Protocole opérationnel** :

1. Choisir l'observable $O$ (le résumé effectif).
2. Construire $q_{\mathcal{O}}$ (le meilleur quotient fidèle).
3. Estimer les fibres (aliasing).
4. Mesurer $\mathrm{Hol}$ (dépendance au chemin invisible au résumé).

> **Résultat** : tu distingues "non-reproductibilité due au chemin" de "non-reproductibilité due à la compression", et tu peux **localiser l'obstruction**.

---

## 14.6bis. Micro-exemple : même observation, holonomie non triviale (cache / mode)

On modélise $\mathcal{X}$ avec deux composantes :

* une composante visible $y$ (réponse textuelle),
* une composante cachée $b \in \{0, 1\}$ (bit interne : "cache chaud/froid" ou "mode strict on/off").

On prend l'observable :
$$
O(y, b) := y \quad\text{(on ne voit pas $b$)}.
$$

À un préfixe $h$, deux événements sont activables et "commutent" au niveau $\mathcal{H}_2$ (2-cellule attestée) :

* $e_1$ : "précharger/cache" (met $b := 1$),
* $e_2$ : "répondre" (produit un texte $y$ qui, à ce stade, ne dépend pas de $b$).

Deux chemins vers le même but $k$ :
$$
p = e_1 ; e_2, \qquad q = e_2 ; e_1,
$$
et une 2-cellule $p \Rightarrow q$ dans $\mathcal{H}_2$.

**Alors** :

* $O(S(p)) = O(S(q))$ (même texte $y$),
* mais la fibre n'est pas recollée fortement : depuis un même micro-état $(y_0, b_0)$, on obtient $b = 1$ après $p$ et $b = b_0$ après $q$.

Donc $\mathrm{Hol}(p, q)$ contient des paires $(x, x')$ avec $x \neq x'$ (différence sur $b$), bien que l'observable soit identique.

> **Interprétation** : le résumé "mod $n$" (ici : projection sur $y$) est fidèle sur l'output immédiat, mais laisse une **holonomie sur l'état caché** qui peut affecter les étapes suivantes (coût, latence, comportement ultérieur).

---

## 14.7. Phrase de clôture

> **"mod $n$" est un cas-limite de "résolution d'observation".** Le contenu structurel n'est pas le quotient lui-même, mais la géométrie qu'il induit : fibres d'ambiguïté et holonomie des chemins. C'est cette interaction (observable × dépendance au chemin) qui explique à la fois les invariants finitaires (tailles de fibres) et les résidus non canoniques (holonomie).
