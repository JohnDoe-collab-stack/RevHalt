## Formulation Physique de RevHalt (Bulk, Bord)

Ce document donne une formulation **physique et opérationnelle** de l’idée RevHalt “(Bulk, Bord)”, en excluant les cas nuls (**RouteII : J ≠ 0**) et en remplaçant toute égalité statique du type “énergie totale = somme” par ce que la physique sait effectivement **définir, calculer et mesurer** : des **bilans de flux**.

---

### 1) Principe physique (système ouvert : Bulk + Bord)

En pratique (GR, QFT sur fond courbe, thermo), un système gravitationnel pertinent (trou noir, AdS, horizon, etc.) ne se réduit pas à “un bulk”. Il est décrit par un couple :

* **Bulk** : dynamique locale (équations de champ, contraintes, évolution).
* **Bord** : **interface d’échange** (conditions au bord, données caractéristiques, état entrant/sortant, sources imposées).

Distinction cruciale (à rendre explicite) :

* **Bord structurel** : une limite/surface où des conditions doivent être posées pour fermer le problème (au sens PDE / charges conservées).
* **Bord actif** : le bord porte un **input non trivial**, i.e. une donnée entrante **J**.

Dans la perspective RevHalt, la non-dégénérescence (RouteII) est :

```
J ≠ 0   (bord actif / input non trivial)
```

---

### 2) Loi physique correcte : bilans de flux (pas d’additivité statique)

#### 2.1 Choix de l’énergie E(t) (cadre-dependent, donc annoncé)

En GR, “l’énergie du bulk” n’est pas une densité locale universelle. On choisit donc une notion de charge adaptée au contexte global, par exemple :

* **Asymptotiquement plat** : énergie **ADM** (spatiale) ou **Bondi** (à l’infini nul, avec pertes par rayonnement).
* **AdS** : énergie définie via les **charges au bord** (conditions au bord non optionnelles).
* **Quasi-local / horizon** : énergie quasi-locale associée à une surface de contrôle (convention annoncée).

Dans ce document, **E(t)** désigne “la charge d’énergie pertinente pour le cadre choisi”.

#### 2.2 Bilan d’énergie (forme générale)

Sur un domaine de contrôle avec surfaces de bord explicites (infini, bord AdS, horizon, etc.), la loi opérationnelle est :

```
dE/dt = P_in(J) - P_out(E, bulk) + P_sources(bulk)
```

* **P_in(J)** : puissance **entrante** imposée par le bord actif (donnée entrante J).
* **P_out(E, bulk)** : puissance **sortante totale** (flux de matière/champs + flux gravitationnel lorsque défini, p. ex. à l’infini nul).
* **P_sources(bulk)** : sources internes (si vous souhaitez distinguer “sources volumétriques” de “conditions au bord”; sinon on peut les regrouper dans P_in).

Point RevHalt (verrouillé physiquement) :

* Le “terme RevHalt” n’est pas un additif statique ; c’est l’obligation de traiter le système comme **ouvert** et donc de spécifier **les flux** (en particulier P_in via J).

---

### 3) Sens physique de J (RouteII : cas non dégénérés)

Dans RouteII, **J** est une donnée **opérationnelle** : une **donnée entrante** (au sens “état entrant / donnée caractéristique entrante / condition imposée au bord”).

Exemples typiques :

* **Asymptotiquement plat (infini nul passé)** : état entrant des modes “in” (occupation/spectre entrant), ou flux entrant depuis l’infini.
* **AdS (bord temporel)** : champs/sources imposés au bord (données entrantes), qui déterminent l’injection/extraction d’énergie et d’entropie.
* **Frontière nulle / horizon (formalisme caractéristique)** : donnée radiative entrante sur une frontière nulle (degré de liberté libre entrant).

Condition RouteII :

```
J ≠ 0  (input non trivial ; le bulk seul ne ferme pas la dynamique globale)
```

---

### 4) Thermodynamique des trous noirs (cas exploitable et mesurable)

On illustre la logique “flux” sur un trou noir, dans un régime où les bilans thermo sont opérationnels.

#### 4.1 Bilan d’énergie (masse)

Pour un trou noir (ex. Schwarzschild) dans un régime quasi-statique :

```
d(M c^2)/dt = P_in(J) - P_out(M)
```

* **P_out(M)** : flux sortant total (incluant, en régime semi-classique, le flux de type Hawking ; plus généralement tout flux sortant défini).
* **P_in(J)** : flux entrant contrôlé par l’état entrant / condition au bord / injection (J).

RouteII (J ≠ 0) signifie : il existe un apport entrant non trivial qui **modifie** l’évolution de M(t).

#### 4.2 Entropie d’horizon (Schwarzschild, quasi-statique)

Sous hypothèses standard (Schwarzschild, quasi-statique, sans rotation/charge), on peut écrire :

```
dS_BH/dt = (1/T_H) * d(M c^2)/dt
         = (1/T_H) * [ P_in(J) - P_out(M) ]
```

Remarque de robustesse :

* Si rotation/charge sont présentes, des **termes de “travail”** apparaissent (ex. variation de moment angulaire et charge). Pour éviter toute collision de notation, ces grandeurs doivent être notées distinctement de votre J (par exemple “J_ang” pour le moment angulaire). Votre J reste la donnée de bord entrante RevHalt.

#### 4.3 Deuxième loi généralisée (GSL, cadre semi-classique)

La loi pertinente (au niveau global) est :

```
d/dt [ S_BH + S_outside ] ≥ 0
```

* **S_outside** : entropie hors horizon (champs, rayonnement, etc.).
* Avec **J ≠ 0**, il existe en général un **flux d’entropie entrant** associé à l’état entrant (bord actif). Le bord devient donc un terme **contraignable** via bilans énergie/entropie.

#### 4.4 Point fixe non dégénéré (équilibre ouvert)

Un point fixe stationnaire non trivial est un équilibre **entrée = sortie** :

```
d(M c^2)/dt = 0  ⇔  P_in(J) = P_out(M)
```

Ce n’est pas “absence de bord”, c’est un **équilibre ouvert** avec J ≠ 0.

---

### 5) Portée formelle : dictionnaire minimal (RevHalt → complexité)

Le projet établit un **théorème conditionnel** (pont rigide) dans un cadre formel (Lean). Pour éviter que ce bloc soit lu comme une analogie, on explicite un dictionnaire minimal :

* **“Bord actif” (physique)** ↔ **“frontière logique non vide” (formel)**
  Intuition : l’évolution/extension n’est pas close sans information de bord ; formellement, il subsiste un contenu de frontière.
* **“Bord stable / se vide à la limite” (physique)** ↔ **“stabilité au bord” (formel)**
  Intuition : la frontière cesse de porter du contenu dans une limite contrôlée ; formellement, la frontière devient vide.

Énoncé conditionnel (tel que vous le formulez) :

```
(Stabilité au Bord + Price of P) ⇒ Collapse (P=NP)
```

Définitions (rappel) :

```
Stabilité : frontière logique vide à la limite
S1Rel(ωΓ) = ∅

Price of P : toute vérité admet une preuve polynomialement compressée
PolyCompressionWC
```

Cartographie (conséquence logique) :

```
Le projet ne prouve pas P=NP.
Il force l’alternative suivante pour refuser Collapse :

¬Collapse ⇒ (¬Stabilité) ∨ (¬Price of P)
```

Lecture “RouteII” (sans cas nuls) :

* Refuser Collapse impose de renoncer soit à la **stabilité** (admettre une frontière/bord actif : S1Rel(ωΓ) ≠ ∅), soit à l’hypothèse **Price of P** (admettre une non-compressibilité générale).

---

### 6) Apport physique (RouteII, sans cas nuls)

Dans la lecture physique de RouteII, la contribution RevHalt n’est pas un terme additif arbitraire ; c’est une contrainte structurelle :

* Le système doit être traité comme **ouvert**.
* Il faut spécifier une **donnée entrante J ≠ 0** (état entrant / condition au bord / donnée caractéristique).
* Les quantités globales (énergie, entropie généralisée) se ferment et se comparent via des **bilans de flux**, uniquement lorsque J est explicitement spécifié.

Autrement dit : RevHalt impose que “Bulk seul” ne suffit pas à fermer la narration prédictive ; le **Bord** (au sens opérationnel) devient un objet mesurable/paramétrable/contraignable par des bilans.

---
