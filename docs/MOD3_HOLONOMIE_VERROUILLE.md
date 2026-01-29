# Mod 3, Holonomie, Flip : Formalisation Verrouillée

> **Version autocontenue et rigoureuse.** Définitions → Théorèmes → Preuves → Composition = XOR → Repair → Critère d'obstruction.

---

## 0. Objet : "mod 3" comme observable, et le résidu caché mesurable (Flip/Hol)

**Idée** : "mod 3" n'est pas une opération primitive, c'est un **choix d'observable** ($O_3$).

- Cette observable induit des **fibres** (ce qu'elle ne voit pas)
- La dépendance au chemin (ordre/scheduling) se manifeste comme une **holonomie** attachée aux 2-cellules
- Le cas mod 3 est spécial : on postule l'existence d'une **sous-fibre primitive à 2 éléments** (un bit) où le transport est réversible — c'est exactement là que le **Flip** apparaît et devient exploitable

---

## 1. Cadre minimal (2D, observable, fibres)

### 1.1. 2-géométrie des histoires

On se donne une (bi)2-catégorie $\mathcal{H}_2$ :

- **Objets** : préfixes d'histoires $h$
- **1-flèches** : chemins $p : h \to k$ (compositions d'extensions)
- **2-cellules** : commutations admissibles $\alpha : p \Rightarrow q$ entre deux chemins parallèles $p, q : h \to k$

> **Intuition** : $\alpha$ encode "ces deux schedulings existent et sont reconnus équivalents au niveau des commutations admises".

### 1.2. Sémantique et observable "mod 3"

On a une sémantique :
$$S : \mathcal{H}_2 \to \mathcal{X}$$

où $\mathcal{X}$ encode les états (régime déterministe ou relationnel).

On fixe une observable de résolution 3 :
$$O_3 : \mathcal{X} \to V_3$$

et on pose :
$$F_3 := O_3 \circ S : \mathcal{H}_2 \to V_3$$

### 1.3. Fibres : ce que "mod 3" ne voit pas

Pour chaque objet $h$ de $\mathcal{H}_2$, on définit la **fibre d'ambiguïté** :
$$\mathrm{Fibre}_3(h) := \{x \in \mathrm{Obj}(\mathcal{X}) \mid O_3(x) = F_3(h)\}$$

C'est "tout ce qui est compatible avec la même observation mod 3".

---

## 2. Transport le long des chemins (niveau "micro")

### 2.1. Transport général (relationnel)

Sans hypothèse d'inversibilité, le transport le long de $p$ est une correspondance :
$$T_p \subseteq \mathrm{Fibre}_3(h) \times \mathrm{Fibre}_3(k)$$

où $(x, y) \in T_p$ signifie : "depuis le micro-état $x$ compatible avec $F_3(h)$, suivre $p$ peut produire un micro-état $y$ compatible avec $F_3(k)$".

On impose uniquement la compatibilité à la composition (composition relationnelle) :
$$T_{p \circ r} = T_p \circ T_r$$

quand $r : h \to m$ et $p : m \to k$, et $T_{\mathrm{id}} = \mathrm{Id}$.

> Jusqu'ici : régime général, pas de $T_q^{-1}$, donc pas de monodromie "groupe".

---

## 3. Hypothèses "mod 3 particulier" : sous-fibre primitive à 2 éléments et réversible

> **C'est le point structurel** (et il est exactement ce qu'on appelle "mod 3 très particulier").

### (P3) Sous-fibre primitive (un bit)

Pour tout $h$, on choisit une sous-fibre distinguée :
$$\mathrm{Prim}_3(h) \subseteq \mathrm{Fibre}_3(h) \quad \text{telle que} \quad |\mathrm{Prim}_3(h)| = 2$$

On peut la noter $\{+, -\}$ si on veut.

### (INV3) Réversibilité sur la primitive

Pour tout chemin $p : h \to k$, le transport restreint à la primitive est une bijection :
$$T_p : \mathrm{Prim}_3(h) \xrightarrow{\sim} \mathrm{Prim}_3(k)$$

### (FUN3) Compatibilité à la composition (sur la primitive)

Pour tous chemins composables $r : h \to m$, $p : m \to k$ :
$$T_{p \circ r} = T_p \circ T_r \quad \text{sur les } \mathrm{Prim}_3, \qquad T_{\mathrm{id}} = \mathrm{id}$$

---

## 4. Holonomie attachée aux 2-cellules

### 4.1. Holonomie relationnelle (définition générale)

Soit $\alpha : p \Rightarrow q$ avec $p, q : h \to k$.

On définit la **relation d'holonomie** (sur la fibre de départ) :
$$\mathrm{Hol}_3(\alpha) \subseteq \mathrm{Fibre}_3(h) \times \mathrm{Fibre}_3(h)$$

par :
$$(x, x') \in \mathrm{Hol}_3(\alpha) \iff \exists y \in \mathrm{Fibre}_3(k) \text{ tel que } (x, y) \in T_p \text{ et } (x', y) \in T_q$$

> **Interprétation** : "en allant par $p$ depuis $x$ et par $q$ depuis $x'$, on peut recoller au même but $y$".

On regarde ensuite la **restriction primitive** :
$$\mathrm{Hol}_3^{\mathrm{prim}}(\alpha) := \mathrm{Hol}_3(\alpha) \cap \bigl(\mathrm{Prim}_3(h) \times \mathrm{Prim}_3(h)\bigr)$$

---

## 5. Monodromie primitive et Flip (définitions)

Sous (INV3), $T_p$ et $T_q$ sont des bijections sur $\mathrm{Prim}_3$, donc $T_q^{-1}$ existe.

### 5.1. Monodromie primitive

$$\mathrm{Mono}_3(\alpha) := T_q^{-1} \circ T_p \in \mathrm{Aut}\bigl(\mathrm{Prim}_3(h)\bigr)$$

### 5.2. Flip (bit)

Comme $|\mathrm{Prim}_3(h)| = 2$, on a :
$$\mathrm{Aut}\bigl(\mathrm{Prim}_3(h)\bigr) \cong S_2 \cong \mathbb{Z}/2$$

donc il n'y a que deux cas : identité ou transposition unique $\tau_h$.

On définit :
$$\mathrm{Flip}_3(\alpha) := \begin{cases} 0 & \text{si } \mathrm{Mono}_3(\alpha) = \mathrm{id} \\ 1 & \text{si } \mathrm{Mono}_3(\alpha) = \tau_h \end{cases}$$

---

## 6. Théorème Flip–Hol₃ (énoncé + preuve verrouillée)

### Théorème 1 (Holonomie primitive = graphe de la monodromie)

Sous (P3), (INV3), (FUN3), pour toute 2-cellule $\alpha : p \Rightarrow q$ (avec $p, q : h \to k$) :

$$\boxed{\mathrm{Hol}_3(\alpha) \cap \bigl(\mathrm{Prim}_3(h) \times \mathrm{Prim}_3(h)\bigr) = \{(u, \mathrm{Mono}_3(\alpha)(u)) \mid u \in \mathrm{Prim}_3(h)\}}$$

En particulier :

- si $\mathrm{Flip}_3(\alpha) = 0$, la restriction est la **diagonale** $\{(u, u)\}$
- si $\mathrm{Flip}_3(\alpha) = 1$, la restriction est $\{(u, \tau_h(u))\}$, donc le **flip** échange les deux primitifs

### Preuve (complète, courte)

Soit $u, u' \in \mathrm{Prim}_3(h)$.

Par définition de $\mathrm{Hol}_3(\alpha)$ :
$$(u, u') \in \mathrm{Hol}_3(\alpha) \iff \exists y \in \mathrm{Fibre}_3(k) \text{ tel que } y \in T_p(u) \text{ et } y \in T_q(u')$$

Sur la primitive, $T_p$ et $T_q$ sont des fonctions vers $\mathrm{Prim}_3(k)$, donc cela équivaut à :
$$(u, u') \in \mathrm{Hol}_3^{\mathrm{prim}}(\alpha) \iff T_p(u) = T_q(u')$$

Comme $T_q$ est bijectif, l'unique $u'$ tel que $T_q(u') = T_p(u)$ est :
$$u' = T_q^{-1} T_p(u) = \mathrm{Mono}_3(\alpha)(u)$$

Donc $\mathrm{Hol}_3^{\mathrm{prim}}(\alpha)$ est le **graphe** de $\mathrm{Mono}_3(\alpha)$. $\square$

---

## 7. Structure 2D : composition = XOR (parité des flips)

> **Fait crucial** : la 2D sert à comparer des totals (linéarisations 1D), et le résidu "mod 3" se résume à un bit additif.

### 7.1. Composition verticale des 2-cellules

Soient deux 2-cellules verticalement composables :
$$\alpha : p \Rightarrow q, \qquad \beta : q \Rightarrow r$$

(avec $p, q, r : h \to k$). Alors :

$$\boxed{\mathrm{Mono}_3(\beta \circ \alpha) = \mathrm{Mono}_3(\beta) \circ \mathrm{Mono}_3(\alpha)}$$

**Preuve** :
$$\mathrm{Mono}_3(\beta \circ \alpha) = T_r^{-1} T_p = (T_r^{-1} T_q)(T_q^{-1} T_p) = \mathrm{Mono}_3(\beta) \circ \mathrm{Mono}_3(\alpha) \quad \square$$

Comme $\mathrm{Aut}(\mathrm{Prim}_3(h)) \cong \mathbb{Z}/2$, cela donne immédiatement :

$$\boxed{\mathrm{Flip}_3(\beta \circ \alpha) = \mathrm{Flip}_3(\beta) \oplus \mathrm{Flip}_3(\alpha)}$$

### 7.2. Interprétation "comparaison de totals"

- Un **total** = une linéarisation 1D (un scheduling concret) correspondant à un chemin $p$
- **Comparer deux totals** $p$ et $q$ revient à exhiber une chaîne de 2-cellules transformant $p$ en $q$
- La **différence cachée** à résolution 3 est alors la parité (XOR) des flips rencontrés le long de cette chaîne

---

## 8. Théorème de repair : tuer l'holonomie (rendre canonique à résolution 3)

> Le "repair" est une extension minimale d'état (ajout d'un bit) qui compense exactement le twist.

### 8.1. Donnée de repair (potentiel)

On cherche une application :
$$\phi : \{\text{chemins de } \mathcal{H}_2\} \to \mathbb{Z}/2$$

telle que pour toute 2-cellule $\alpha : p \Rightarrow q$ :

$$\boxed{\mathrm{Flip}_3(\alpha) = \phi(p) \oplus \phi(q)}$$

C'est exactement dire : "le flip est un **cobord**" (un coboundaire) : il se lit comme différence de potentiel entre deux totals.

### 8.2. Construction "réparée"

Définis la fibre primitive réparée :
$$\widetilde{\mathrm{Prim}}_3(h) := \mathrm{Prim}_3(h) \times \mathbb{Z}/2$$

Définis le transport réparé le long d'un chemin $p : h \to k$ :
$$\widetilde{T}_p(u, s) := (T_p(u), s \oplus \phi(p))$$

C'est bijectif (car $T_p$ l'est).

### Théorème 2 (Repair tue l'holonomie primitive)

Si $\phi$ satisfait $\mathrm{Flip}_3(\alpha) = \phi(p) \oplus \phi(q)$ pour toute $\alpha : p \Rightarrow q$, alors pour toute 2-cellule $\alpha : p \Rightarrow q$ :

$$\boxed{\widetilde{T}_q^{-1} \circ \widetilde{T}_p = \mathrm{id} \quad \text{sur } \widetilde{\mathrm{Prim}}_3(h)}$$

Donc l'holonomie devient **strictement diagonale** après repair : plus de flip, plus de dépendance au chemin sur la partie primitive.

### Preuve (calcul explicite)

On a :
$$\widetilde{T}_p(u, s) = (T_p(u), s \oplus \phi(p))$$

Et :
$$\widetilde{T}_q^{-1}(v, t) = \bigl(T_q^{-1}(v), t \oplus \phi(q)\bigr)$$

(car inverser $s \mapsto s \oplus \phi(q)$ revient à re-xorer $\phi(q)$).

Donc :
$$\widetilde{T}_q^{-1} \widetilde{T}_p(u, s) = \Bigl(T_q^{-1} T_p(u), s \oplus \phi(p) \oplus \phi(q)\Bigr) = \Bigl(\mathrm{Mono}_3(\alpha)(u), s \oplus \mathrm{Flip}_3(\alpha)\Bigr)$$

en utilisant la condition $\phi(p) \oplus \phi(q) = \mathrm{Flip}_3(\alpha)$.

Or $\mathrm{Flip}_3(\alpha) = 0$ iff $\mathrm{Mono}_3(\alpha) = \mathrm{id}$, et $\mathrm{Flip}_3(\alpha) = 1$ iff $\mathrm{Mono}_3(\alpha) = \tau_h$. Dans les deux cas, la correction sur le second bit **compense exactement** l'effet sur le premier. Le résultat est l'identité sur $(u, s)$. $\square$

> **Point clé** : le repair transforme le résidu "holonomie" en artefact de jauge dès que $\phi$ existe.

### 8.3. Critère exact : canonisable / non canonisable

| Situation | Conséquence |
|-----------|-------------|
| $\phi$ **existe** | Flip trivialisable → résolution 3 canonique (pas besoin de choisir un total) |
| $\phi$ **n'existe pas** | Obstruction intrinsèque (classe $\mathbb{Z}/2$ non nulle) |

---

## 9. Ce que "mod 3" révèle ici (formulation sans ambiguïté)

1. À résolution 3, la non-canonicité de chemin **ne se voit pas** dans $V_3$, mais **vit dans les fibres**
2. Le cas spécial mod 3 postule une "part primitive" qui est exactement **un bit** $\mathrm{Prim}_3(h)$ et se transporte réversiblement
3. Chaque 2-cellule $\alpha$ induit alors une holonomie primitive qui est nécessairement **soit diagonale (pas de flip)**, **soit transposition (flip)**
4. Les flips se composent par **XOR** le long des déformations (pasting), donc comparer deux totals devient mesurer une **parité $\mathbb{Z}/2$**
5. La réparabilité globale est un **critère exact** : existence de $\phi$ tel que $\mathrm{Flip}_3(\alpha) = \phi(p) \oplus \phi(q)$
6. Si repair existe, on peut **se passer du total (1D) sans perte** à cette résolution, car l'holonomie est rendue diagonale sur l'extension réparée

---

## 10. Ancrage cyclotomique (intuition)

Dans la cyclotomie :

- $\mathrm{Prim}_3$ = les deux racines primitives d'ordre 3 ($\zeta, \zeta^{-1}$)
- $(\mathbb{Z}/3\mathbb{Z})^\times = \{1, 2\}$ agit par $\zeta \mapsto \zeta^a$
- $a = 2$ donne $\zeta \mapsto \zeta^{-1}$ = **flip**

Ici, le cadre dit : ce flip n'est pas seulement "une symétrie d'objet", c'est l'**holonomie d'une 2-cellule** relativement à l'observable $O_3$.

---

## Résumé ultra-court (slogan)

| Concept | Définition |
|---------|------------|
| **Total** | 1D (linéarisation) |
| **2D** | Sert à comparer les totals |
| **Mod 3** | Il reste un bit invariant (Flip) sur la primitive |
| **Composition** | Flips se composent en XOR |
| **Repair** | Ajouter un bit qui trivialise l'holonomie iff $\phi$ existe |

---

## 11. Le bon objet 2D : "déformations de totals" comme 2-complexe (groupoïde de commutations)

On fixe une base $h$ (préfixe) et un but $k$.

### 11.1. Catégorie des déformations $\mathrm{Def}(h, k)$

On définit une catégorie $\mathrm{Def}(h, k)$ :

- **Objets** : les chemins $p : h \to k$ (les "totals" possibles, i.e. linéarisations 1D)
- **Flèches** : les 2-cellules $\alpha : p \Rightarrow q$ (les "moves" 2D admissibles transformant un total en un autre)

La composition verticale des 2-cellules est la composition des flèches dans $\mathrm{Def}(h, k)$.

> **Interprétation** : Total = objet (1D) ; Comparer des totals = morphismes (2D).

---

## 12. Rappel : primitive mod 3 et monodromie

Hypothèses "mod 3 particulier" (déjà verrouillées) :

- **(P3)** $|\mathrm{Prim}_3(h)| = 2$ pour tout $h$
- **(INV3)** pour tout chemin $p : h \to k$, $T_p : \mathrm{Prim}_3(h) \xrightarrow{\sim} \mathrm{Prim}_3(k)$ est bijectif
- **(FUN3)** $T_{p \circ r} = T_p \circ T_r$, $T_{\mathrm{id}} = \mathrm{id}$ sur la primitive

Pour une 2-cellule $\alpha : p \Rightarrow q$ (avec $p, q : h \to k$), on pose :
$$\mathrm{Mono}_3(\alpha) = T_q^{-1} \circ T_p \in \mathrm{Aut}(\mathrm{Prim}_3(h)) \cong \mathbb{Z}/2$$

et :
$$\mathrm{Flip}_3(\alpha) \in \mathbb{Z}/2 \quad \text{comme l'image de } \mathrm{Mono}_3(\alpha) \text{ via } \mathrm{Aut}(\mathrm{Prim}_3(h)) \simeq \mathbb{Z}/2$$

---

## 13. Théorème : $\mathrm{Flip}_3$ est un foncteur vers $\mathbb{Z}/2$ (donc un cocycle)

On voit $\mathbb{Z}/2$ comme une **catégorie à un objet** $\mathbf{B}(\mathbb{Z}/2)$ :

- un seul objet $(*)$
- les endomorphismes $\mathrm{End}(*) = \mathbb{Z}/2$
- la composition = addition $\oplus$

### Théorème 3 (Fonctorialité de la monodromie / additivité du flip)

Pour tout $h, k$, l'application :
$$\Phi_{h,k} : \mathrm{Def}(h, k) \to \mathbf{B}(\mathbb{Z}/2)$$

définie par :

- sur objets : $\Phi_{h,k}(p) = *$ (on oublie l'objet)
- sur flèches : $\Phi_{h,k}(\alpha) = \mathrm{Flip}_3(\alpha)$

est un **foncteur**. En particulier, si $\beta : q \Rightarrow r$ et $\alpha : p \Rightarrow q$ sont composables :

$$\boxed{\mathrm{Flip}_3(\beta \circ \alpha) = \mathrm{Flip}_3(\beta) \oplus \mathrm{Flip}_3(\alpha)}$$

**Preuve** :
$$\mathrm{Mono}_3(\beta \circ \alpha) = T_r^{-1} T_p = (T_r^{-1} T_q)(T_q^{-1} T_p) = \mathrm{Mono}_3(\beta) \circ \mathrm{Mono}_3(\alpha)$$

En identifiant $\mathrm{Aut}(\mathrm{Prim}_3(h)) \cong \mathbb{Z}/2$, la composition d'automorphismes devient $\oplus$. $\square$

> **Traduction** : les flips s'additionnent mod 2 le long d'une chaîne de commutations. Donc "comparer des totals" produit un invariant $\mathbb{Z}/2$.

---

## 14. Formulation "2-complexe" : Flip est un 2-cocycle $\mathbb{Z}/2$

Pour raisonner "obstruction / trivialisation", on voit la situation comme un **complexe cellulaire** :

- **0-cellules** : objets $h$
- **1-cellules** : chemins $p$
- **2-cellules** : commutations admissibles $\alpha : p \Rightarrow q$

Chaque 2-cellule a une "frontière" formelle $p \cdot q^{-1}$. Dans $\mathbb{Z}/2$ (où $x = -x$), seule compte la **différence** entre $p$ et $q$.

La donnée $\mathrm{Flip}_3(\alpha) \in \mathbb{Z}/2$ est une **2-cochaîne** sur les faces, et le Théorème 3 (additivité sous pasting) est exactement la condition "$d\,\mathrm{Flip}_3 = 0$" : **c'est un cocycle**.

> En clair : la 2D (pasting de 2-cellules) impose des compatibilités, et Flip respecte ces compatibilités ⇒ **Flip est une classe cohomologique**.

---

## 15. Repair = trivialisation : $\mathrm{Flip}_3$ est un cobord

La condition de repair :

$$\boxed{\exists\ \phi : \{\text{chemins}\} \to \mathbb{Z}/2 \text{ tel que } \forall\, \alpha : p \Rightarrow q,\ \mathrm{Flip}_3(\alpha) = \phi(p) \oplus \phi(q)}$$

C'est exactement dire :
$$\mathrm{Flip}_3 = \delta \phi$$

dans le complexe de cochaînes (cobord / coboundary).

### Théorème 4 (Critère exact de réparabilité globale)

Les assertions suivantes sont équivalentes :

1. **(Repair global possible)** Il existe une extension d'état par un bit ($\widetilde{\mathrm{Prim}}_3 = \mathrm{Prim}_3 \times \mathbb{Z}/2$) rendant l'holonomie primitive strictement diagonale pour toutes les 2-cellules admises
2. **(Potentiel)** Il existe $\phi$ tel que $\mathrm{Flip}_3(\alpha) = \phi(p) \oplus \phi(q)$ pour toute $\alpha : p \Rightarrow q$
3. **(Obstruction nulle)** La classe $[\mathrm{Flip}_3]$ dans la cohomologie $\mathbb{Z}/2$ du 2-complexe des déformations est **triviale**

**Preuve** :

- $(2) \Rightarrow (1)$ : le calcul $\widetilde{T}_q^{-1} \widetilde{T}_p = \mathrm{id}$ (repair compense le twist)
- $(1) \Rightarrow (2)$ : si le repair tue tous les flips, le bit ajouté fournit une jauge globale $\phi$
- $(2) \Leftrightarrow (3)$ : définition standard "cocycle trivial" $\Leftrightarrow$ "cobord". $\square$

---

## 16. Ce que tu gagnes (formellement)

Tu obtiens une information **intrinsèquement hors-1D** :

| Niveau | Contenu |
|--------|---------|
| **Total (1D)** | Choix de linéarisation |
| **2D** | Relie deux choix 1D |
| **Résidu mod 3** | Universellement binaire sur primitive : $\mathbb{Z}/2$ |

Ce résidu :

- est **fonctoriel** (pasting = XOR)
- est une **obstruction** globale (classe cohomologique)
- la réparabilité est **équivalente** à la trivialité de cette obstruction

> **Oui**, tu as un invariant structurel que la pure arithmétique "mod 3 = valeur" ne formule pas, parce qu'il vit au niveau **chemins/commutations**, pas au niveau "valeurs finales".

---

## 17. Procédure abstraite : "tirer au clair mod 3"

1. Identifier une observable $O_3$ et une primitive $\mathrm{Prim}_3(h)$ à deux états (bit)
2. Vérifier (INV3) : les transports sur ce bit sont réversibles le long des chemins pertinents
3. Pour chaque 2-cellule admissible $\alpha : p \Rightarrow q$, calculer $\mathrm{Flip}_3(\alpha) \in \mathbb{Z}/2$
4. En déduire :

| Situation | Conséquence |
|-----------|-------------|
| $[\mathrm{Flip}_3] = 0$ | Repair global possible → canonisation (plus besoin de total) |
| $[\mathrm{Flip}_3] \neq 0$ | Obstruction intrinsèque → impossible de canoniser à cette résolution |

---

## 18. Le groupoïde des schedulings $\Pi(\mathcal{H}_2)$ : "totals" + "déformations" inversibles

### 18.1. Point de départ : la 2-géométrie

On a une 2-catégorie (ou bicatégorie) $\mathcal{H}_2$ :

- objets : préfixes $h$
- 1-flèches : chemins $p : h \to k$ (totals, linéarisations)
- 2-cellules : $\alpha : p \Rightarrow q$ (commutations admissibles, déformations 2D)

On fixe $h, k$.

### 18.2. Catégorie des déformations $\mathrm{Def}(h, k)$

- $\mathrm{Obj}(\mathrm{Def}(h, k)) = \{p : h \to k\}$
- $\mathrm{Hom}_{\mathrm{Def}}(p, q) = \{\alpha : p \Rightarrow q\}$
- composition = pasting vertical des 2-cellules

> **Interprétation** : les totals sont des objets, les comparaisons de totals sont des morphismes.

### 18.3. Groupoïdification : $\Pi(h, k)$

On veut un objet où "déformer" devient **inversible** (comme en homotopie) : on **inverse formellement** toutes les 2-cellules.

**Définition** :
$$\Pi(h, k) := \mathrm{Def}(h, k)[\mathrm{Mor}^{-1}]$$

(la localisation de $\mathrm{Def}(h, k)$ en inversant tous les morphismes)

- objets : mêmes totals $p : h \to k$
- morphismes : zigzags de 2-cellules $\alpha$ et d'inverses formels $\alpha^{-1}$, modulo les relations usuelles

**Donc $\Pi(h, k)$ est un groupoïde** : toute "déformation admissible" est réversible au niveau 2D.

> C'est le bon "$\pi_1$" des schedulings : les boucles sont des suites de commutations qui reviennent au même total.

---

## 19. Mod 3 "spécial" : la donnée primitive induit un foncteur $\Pi(h, k) \to \mathbf{B}(\mathbb{Z}/2)$

Hypothèses "mod 3 particulier" (verrouillées) :

- **(P3)** $|\mathrm{Prim}_3(h)| = 2$ pour tout $h$
- **(INV3)** $T_p : \mathrm{Prim}_3(h) \xrightarrow{\sim} \mathrm{Prim}_3(k)$ bijectif
- **(FUN3)** $T_{p \circ r} = T_p \circ T_r$, $T_{\mathrm{id}} = \mathrm{id}$

Pour une 2-cellule $\alpha : p \Rightarrow q$ :
$$\mathrm{Mono}_3(\alpha) = T_q^{-1} \circ T_p \in \mathrm{Aut}(\mathrm{Prim}_3(h)) \cong \mathbb{Z}/2$$

### Théorème 5 (Flip descend au groupoïde)

L'application $\alpha \mapsto \mathrm{Flip}_3(\alpha)$ définit un **foncteur** :

$$\boxed{\mathrm{Flip}_3 : \Pi(h, k) \longrightarrow \mathbf{B}(\mathbb{Z}/2)}$$

où $\mathbf{B}(\mathbb{Z}/2)$ est la catégorie à un objet $(*)$ et $\mathrm{End}(*) = \mathbb{Z}/2$ (composition = XOR).

**Vérification** :

1. Sur $\mathrm{Def}(h, k)$, on sait : $\mathrm{Flip}_3(\beta \circ \alpha) = \mathrm{Flip}_3(\beta) \oplus \mathrm{Flip}_3(\alpha)$
2. Dans $\mathbf{B}(\mathbb{Z}/2)$, chaque élément est inversible → le foncteur se factorise par $\Pi(h, k)$. $\square$

> **Traduction** : la dépendance au chemin résiduelle "mod 3" est une représentation des déformations de scheduling dans $\mathbb{Z}/2$.

---

## 20. La "classe" de Flip : cohomologie de groupoïde (obstruction intrinsèque)

### 20.1. Cohomologie $H^1$ d'un groupoïde (version minimale)

Pour un groupoïde $G$ et un groupe abélien $A$, un **1-cocycle** $c$ est exactement un foncteur :
$$c : G \to \mathbf{B}(A)$$

Deux cocycles $c, c'$ sont **cohomologues** s'il existe une jauge $g : \mathrm{Obj}(G) \to A$ telle que :
$$c'(\gamma) = g(t(\gamma)) \oplus c(\gamma) \oplus g(s(\gamma))$$

pour tout morphisme $\gamma$.

Le groupe $H^1(G; A)$ est l'ensemble des classes de foncteurs modulo jauge.

Ici $A = \mathbb{Z}/2$, $G = \Pi(h, k)$. Donc $\mathrm{Flip}_3$ définit une **classe canonique** :

$$\boxed{[\mathrm{Flip}_3] \in H^1(\Pi(h, k); \mathbb{Z}/2)}$$

### 20.2. Lecture par boucles : homomorphisme $\pi_1 \to \mathbb{Z}/2$

Choisis un total base $p$ (objet de $\Pi(h, k)$). Le groupe des boucles $\pi_1(\Pi(h, k), p) = \mathrm{Aut}_{\Pi(h,k)}(p)$ est un groupe.

Restreindre le foncteur $\mathrm{Flip}_3$ aux automorphismes donne un morphisme de groupes :

$$\boxed{\mathrm{Flip}_3 : \pi_1(\Pi(h, k), p) \to \mathbb{Z}/2}$$

Concrètement : une boucle = une suite de commutations ramenant $p$ à $p$. **Le bit retourné est la parité globale du "twist"** sur la primitive.

---

## 21. Repair = trivialisation de la classe $[\mathrm{Flip}_3]$

"Repair global" = enrichir l'état par un bit de jauge de sorte que **toutes** les déformations admissibles deviennent neutres sur la fibre réparée.

### Théorème 6 (Repair global $\Longleftrightarrow$ classe nulle)

Les assertions suivantes sont équivalentes :

1. **(Repair global)** Il existe une extension par un bit qui tue l'holonomie sur $\mathrm{Prim}_3$ pour toutes les 2-cellules admises
2. **(Jauge)** Il existe $g : \mathrm{Obj}(\Pi(h, k)) \to \mathbb{Z}/2$ telle que $\mathrm{Flip}_3(\gamma) = g(q) \oplus g(p)$ pour tout $\gamma : p \to q$
3. **(Obstruction nulle)** $\boxed{[\mathrm{Flip}_3] = 0 \text{ dans } H^1(\Pi(h, k); \mathbb{Z}/2)}$

**Preuve** :

- $(2) \Leftrightarrow (3)$ : définition de $H^1$ comme cocycles modulo jauge
- $(2) \Rightarrow (1)$ : on reconstruit $\widetilde{\mathrm{Prim}}_3 = \mathrm{Prim}_3 \times \mathbb{Z}/2$ et on corrige par $g$
- $(1) \Rightarrow (2)$ : si l'holonomie est tuée, le bit de repair attaché à chaque total est une jauge $g$. $\square$

> **Point clé** : ce n'est pas un "détail" — tu as une obstruction intrinsèque, calculable, qui vit au niveau 2D et contrôle exactement la canonisation.

---

## 22. Résumé opérationnel (ultra-net)

| Concept | Définition |
|---------|------------|
| **Totaux (1D)** | Objets $p$ |
| **Comparaisons (2D)** | Morphismes $\alpha$ dans $\Pi(h, k)$ |
| **Mod 3 particulier** | Primitive à 2 états + transports bijectifs |
| **Invariant universel** | Foncteur $\mathrm{Flip}_3 : \Pi(h, k) \to \mathbf{B}(\mathbb{Z}/2)$ |
| **Obstruction** | $[\mathrm{Flip}_3] \in H^1(\Pi(h, k); \mathbb{Z}/2)$ |
| **Repair global** | $\Longleftrightarrow [\mathrm{Flip}_3] = 0$ |
