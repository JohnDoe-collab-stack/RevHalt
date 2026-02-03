# Manifeste — Holonomie primitive (2D avant quotient)

Ce texte résume la fondation exposée dans `docs/PRIMITIVE_HOLONOMY.md` et ses conséquences conceptuelles. Il est volontairement sans "raccourcis classiques" : on sépare strictement (i) la géométrie 2D des histoires, (ii) la sémantique relationnelle, (iii) l’observable et ses fibres, (iv) les invariants et obstructions avant tout quotient.

## 1) Changement de primitif (le point fondamental)

La différence avec une grande partie des mathématiques "usuelles" (en pratique, dans les fondations des modèles de calcul et de sémantique) n’est pas une astuce technique : c’est un changement de primitif.

- Approche standard (souvent) : on fixe d’abord une exécution 1D (une timeline, un ordre, une linéarisation), puis on quotient les commutations, puis on cherche des invariants qui survivent à ce quotient.
- Ici : l’objet primitif est la géométrie 2D des histoires (chemins + comparabilité par moves admissibles). Le 1D n’est pas un socle : c’est un "shadow" dérivé d’un choix de chaîne cofinale. Le quotient n’est donc plus une étape fondatrice, mais une projection possible.

Conséquence immédiate : si une information est perdue par toute projection 1D, alors elle est réellement 2D (intrinsèque). On ne peut plus la "récupérer" en ajoutant des hypothèses ad hoc sur la timeline.

## 2) Primitive géométrique : H2 (histoires en 2D)

On suppose une structure 2D minimale (stricte ou bicatégorique, l’essentiel est le rôle) :

- Objets : préfixes d’histoires (états de contexte).
- 1-flèches : totals / schedulings (chemins) entre préfixes.
- 2-cellules : moves de commutation admissibles, écrites `alpha : p ⇒ q` avec `p, q : h → k`.

Point clé : `alpha` n’est pas une "égalité" de chemins, ni une neutralisation sémantique. C’est un index de comparabilité 2D : il désigne quelles paires de chemins on autorise à comparer.

## 3) Le temps comme shadow (cofinalité, pas primitif)

On définit une relation d’accessibilité : `Reach(h, k)` signifie "k est atteignable depuis h" (il existe au moins un total `p : h → k`).

Un "futur pertinent" est un ensemble `C` de préfixes tel que pour tout préfixe `h`, il existe `k` dans `C` atteignable depuis `h` (cofinalité).

Une "timeline" n’est pas primitive : c’est un choix de chaîne cofinale (une linéarisation cofinale). Le temps ordinal est un invariant dérivé de ce choix.

## 4) Sémantique minimale : relationnelle, sur le 1-squelette

On fixe un ensemble (ou type) de micro-états `X`.

La sémantique minimale est une affectation sur les 1-flèches seulement :

- à chaque total `p : h → k`, on associe une relation `S1(p) ⊆ X × X`.
- `S1` respecte l’identité et la composition des 1-flèches (au sens du 1-squelette).

Point clé : on ne demande pas que `alpha : p ⇒ q` soit envoyé sur quoi que ce soit. Les 2-cellules ne sont pas "déjà neutralisées" par la sémantique.

## 5) Observation et fibres : l’ambiguïté est une donnée, pas un défaut

On fixe une observable `O : X → V`.

Pour chaque préfixe `h`, on suppose donnée une valeur visible `v_h` (issue de l’exécution observée).

On définit la fibre d’ambiguïté au-dessus de `h` :

- `F(h) := { x ∈ X | O(x) = v_h }`.

Point clé : on ne postule pas une section globale `sigma(h)` dans `X`. On travaille directement avec l’ensemble (ou type) des micro-états compatibles avec l’observation.

## 6) Transport sur fibres (relationnel)

Pour un total `p : h → k`, on définit le transport restreint aux fibres :

- `T_p := S1(p)` restreinte à `F(h) × F(k)`.

Intuitivement : `T_p` capture ce que le chemin `p` peut faire entre les micro-états compatibles avec l’observation aux extrémités.

## 7) Holonomie primitive (avant quotient)

Pour une 2-cellule `alpha : p ⇒ q` (avec `p, q : h → k`), on définit l’holonomie relative à `O` :

- `Hol_O(alpha) ⊆ F(h) × F(h)`
- `(x, x') ∈ Hol_O(alpha)` ssi il existe `y ∈ F(k)` tel que `(x, y) ∈ T_p` et `(x', y) ∈ T_q`.

Forme calcul relationnel :

- `Hol_O(alpha) = T_p o (T_q)^dagger`

où `( )^dagger` est la relation réciproque, et `o` la composition relationnelle (sens fixé).

Ce point est central : l’invariant est défini avant tout quotient, sans hypothèse d’inverse, et sans forcer la neutralité des 2-cellules.

### Trois régimes (toujours relationnel)

- Holonomie faible : tout `x` de `F(h)` est relié à lui-même par `Hol_O(alpha)` (la diagonale est incluse).
- Holonomie plate (forte) : `Hol_O(alpha)` est exactement la diagonale (pas de twist).
- Holonomie tordue : il existe `x ≠ x'` dans `F(h)` tels que `(x, x') ∈ Hol_O(alpha)`.

## 8) Lag : twist invisible maintenant, visible plus tard

Dans le cas `X = Y × B` et `O(y, b) = y` :

- deux chemins `p` et `q` peuvent être indiscernables au niveau visible `Y`,
- mais produire une holonomie tordue sur la partie cachée `B`,
- et devenir "observable plus tard" dès qu’une étape future dépend de `b`.

Ici, "plus tard" se formalise proprement sans introduire un temps primitif : c’est une incompatibilité future avec la trace observée (une des deux possibilités cachées cesse d’être compatible avec une fibre ultérieure).

## 9) Auto-régulation cofinale : trivialiser les holonomies (ou exhiber l’obstruction)

On choisit un futur cofinal pertinent (un ensemble cofinal de préfixes), et on ne regarde que les 2-cellules dont les extrémités vivent dans ce futur.

Une jauge (repair) relationnelle associe à chaque total `p : h → k` une relation `phi(p) ⊆ F(k) × F(k)` (réparation sur la fibre d’arrivée).

On définit alors :

- transport corrigé : `T_p# := T_p o phi(p)`
- holonomie corrigée : `Hol_O#(alpha) := T_p# o (T_q#)^dagger`

Auto-régulation cofinale : il existe une jauge `phi` telle que pour toutes les 2-cellules pertinentes `alpha`, `Hol_O#(alpha)` est la diagonale.

Sinon : obstruction structurelle cofinale. Formellement, c’est un schéma de quantificateurs :

- pas de "solution globale" `exists phi` qui règle tout,
- mais un témoin systématique : pour toute jauge `phi`, il existe une 2-cellule `alpha` (dans le futur cofinal) où la holonomie corrigée reste tordue.

## 10) Barrière 1D : un shot ne récupère pas la donnée 2D en général

Un "shot 1D" est une compression `q` qui associe à un chemin `p : h → k` un code `q(p) : Q`.

On dit que l’holonomie factorise par `q` si `Hol_O(alpha)` ne dépend que du couple `(q(p), q(q))`.

Critère témoin (non-réduction) :

- s’il existe deux 2-cellules `alpha1 : p1 ⇒ q1` et `alpha2 : p2 ⇒ q2` avec les mêmes codes `(q(p1), q(q1)) = (q(p2), q(q2))` mais des holonomies différentes, alors aucune factorisation par ce shot 1D n’est possible.

Interprétation : toute compression 1D qui oublie la géométrie 2D peut identifier des chemins qui portent pourtant des holonomies différentes. L’invariant est donc intrinsèquement 2D.

## 11) Ce que ça change (résumé de fondation)

- Le 1D (timeline, ordre) devient un choix dérivé, pas un primitif.
- Les 2-cellules ne sont pas traitées comme des égalités : elles indexent la comparabilité 2D.
- L’invariant central (holonomie) est défini avant quotient, sans inverses.
- L’observation est structurée par fibres, sans imposer d’état interne canonique.
- Les impossibilités deviennent géométriques : obstruction cofinale et échange de quantificateurs (procédure globale impossible vs réparations locales possibles).

## 12) Vérifiabilité (Lean, sans axiomes de fondation cachés)

La formalisation Lean associée est dans :

- `RevHalt/Theory/PrimitiveHolonomy.lean`
- `RevHalt/Theory/HolonomyBridge.lean`

La discipline appliquée est : pas de `classical`, pas de `noncomputable`, et préférence systématique pour des équivalences point par point (`RelEq`, `UpEqv`) plutôt que l’égalité de fonctions. Les fichiers contiennent des lignes `#print axioms ...` pour vérifier que les énoncés clés ne dépendent pas d’axiomes additionnels.

