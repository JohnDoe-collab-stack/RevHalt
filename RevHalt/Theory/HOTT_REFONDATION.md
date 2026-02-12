# Refondation de la Théorie des Types Homotopiques (HoTT)

Ce document formalise la nécessité de refonder HoTT sur la base de l'Holonomie Primitive (`PrimitiveHolonomy.lean`) et de la Caractérisation des Groupoïdes (`GroupoidCharacterization.lean`).

## 1. La Critique Fondamentale : Le Groupoïde n'est pas Primitif

Dans HoTT standard, l'identité `Id A x y` est axiomatiquement dotée d'une structure de ∞-groupoïde (chemins inversibles, composition associative à homotopie près, etc.). Cette structure est **donnée**.

Notre travail démontre que cette structure est **émergente et conditionnelle**. Elle n'existe pas a priori dans l'univers computationnel brut (le `HistoryGraph`).

### Le Théorème d'Émergence

Le fichier `GroupoidCharacterization.lean` établit l'équation fondamentale :

$$ \text{Groupoïde (Type HoTT)} \iff \text{C1 (Réversibilité)} + \text{C2 (Platitude)} $$

1. **C1 (Réversibilité)** : La base computationnelle doit permettre de "défaire" toute action à homotopie près (`HomotopyRev`).
2. **C2 (Platitude)** : L'holonomie le long de toute boucle contractile (déformation triviale) doit être l'identité (`FlatUnits`).

## 2. L'Obstruction : La Fissure dans l'Identité

Le fichier `PrimitiveHolonomy.lean` formalise des scénarios (`Obstruction`, `TwistedHolonomy`, `LagEvent`) où la condition **C2** échoue structurellement.

* Dans ces cas, le transport le long d'un chemin $p$ suivi de son inverse $p^{-1}$ ne ramène pas au point de départ.
* Il y a une "dérive" ou un "lag" (retard) qui rend l'inversion imparfaite.

### Conséquence : L'Effondrement de HoTT

Si **C2** est faux (présence d'obstruction), alors **la structure de groupoïde s'effondre**.

* On ne peut plus définir l'égalité comme dans HoTT.
* L'univers n'est plus un "Espace" homotopique, mais une structure dirigée et irréversible.

## 3. Vers une "Théorie des Types Dirigée" (Directed Type Theory)

La refondation consiste à poser le `HistoryGraph` (Graphe d'Histoires) et la `Semantics` (Sémantique Relationnelle) comme les objets primitifs, **avant** toute notion de Type ou d'Espace.

* **Le Cas "Plat" (HoTT)** : C'est un cas particulier dégénéré où l'obstruction est nulle. C'est le domaine des "mathématiques réversibles" et "stables".
* **Le Cas "Courbe" (RevHalt)** : C'est le cas général où l'obstruction est non-nulle. C'est le domaine de la complexité computationnelle irréductible (Problème de l'Arrêt, Indécidabilité).

## Conclusion

HoTT n'est pas la théorie universelle de l'égalité. C'est la théorie de l'égalité **sans obstruction**. Pour comprendre l'indécidabilité et la dynamique transfinie, il faut sortir de HoTT pour revenir à l'Holonomie Primitive.
