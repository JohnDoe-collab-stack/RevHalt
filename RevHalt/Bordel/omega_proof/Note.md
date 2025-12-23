Consolidation 

---

0) But et posture

Cadre minimal et opératif pour :

isoler une valuation canonique liée à l’arrêt (halting),

montrer une frontière d’internalisation dans une théorie interne (type S2),

fournir une méthode opérative pour continuer malgré cette frontière : complémentarité (T3), extensions sound, itération,

préparer une lecture “poset-catégorie” (stabilité par extension, unions dirigées), sans exiger de math lourde.


Le cadre évite deux illusions :

illusion “décider l’arrêt globalement” (décision totale interne),

illusion “internaliser totalement la vérité” (total + correct + complet dans S2).



---

1) Trace : noyau temporel minimal (Trace.lean)

1.1 Définition

Trace : une trace est une fonction Nat → Prop.

Intuition : à l’instant n, un événement/propriété est vrai ou faux.


Halts T : l’arrêt est “il existe un témoin”.

Forme : Halts T est (définitionnellement ou équivalent à) ∃ n, T n.



1.2 Monotonisation : wrapper historique

up T n : “il y a eu quelque chose de vrai au plus tard à l’instant n”.

Forme : up T n := ∃ k ≤ n, T k.



Propriétés prouvées :

up_mono : Monotone (up T) (une fois vrai, reste vrai).

exists_up_iff : (∃ n, up T n) ↔ (∃ n, T n).


Point clé opératif :

up rend n’importe quelle trace compatible avec une hypothèse “monotone”.



---

2) Kit : l’observateur comme interface d’existence sur monotones (Kit.lean)

2.1 RHKit

Un kit K expose une opération :

Proj : Trace → Prop


Intuition : le kit produit une réponse (verdict) sur une trace.

2.2 Hypothèse centrale : DetectsMonotone

DetectsMonotone K signifie :

pour toute trace X,

si X est monotone,

alors K.Proj X ↔ ∃ n, X n.


C’est uniforme : cela vaut pour toutes les traces monotones, pas juste une classe spéciale.

2.3 Rev_K / Rev0_K

Idée opérative :

au lieu d’appliquer le kit directement à T,

on l’applique à up T (qui est monotone).


Conceptuellement :

Rev_K K T := K.Proj (up T) (forme conceptuelle)

Rev0_K est l’objet effectivement utilisé dans les théorèmes T1/T2 (défini via Rev_K dans votre code).


Point clé :

Rev0_K est “le verdict canonique induit par le kit via monotonisation”.



---

3) T1 : canonicité / rigidité de la valuation (Canonicity.lean)

3.1 Théorème principal : T1_traces

Énoncé :

si hK : DetectsMonotone K, alors pour toute trace T :

Rev0_K K T ↔ Halts T.



Squelette de preuve (exactement ce que fait le code) :

1. dérouler Rev0_K (et Rev_K si nécessaire),


2. appliquer hK à up T en utilisant up_mono,


3. réécrire via exists_up_iff.



Interprétation stricte :

sous DetectsMonotone, la valuation Rev0_K est exactement la valuation “halting”.


3.2 Unicité : T1_uniqueness

Deux kits satisfaisant DetectsMonotone coïncident extensionnellement sur toutes les traces.

Rigidité : l’interface force une valuation unique (au sens extensionnel).


3.3 La phrase anglaise (sens Lean)

Claim :

“All observers capable of detecting existence on monotone traces implement a valuation of the halting problem.”


Traduction Lean-faithful :

“Tout kit K satisfaisant DetectsMonotone induit un Rev0_K extensionnellement égal à Halts sur toute trace.”


Important :

ce n’est pas “détecter un existentiel particulier”,

c’est “réaliser uniformément l’existence sur toutes traces monotones”.



---

4) Valuation vs Decision : séparation fondamentale (niveau conceptuel)

Halts T et Rev0_K K T (quand canonique) sont des valuations : elles donnent une valeur de vérité.

Une valuation n’est pas automatiquement :

calculable,

ni internalisable dans une théorie de preuve.



Cette séparation est cruciale : T1 est extensionnel, pas “algorithmique”.


---

5) S2 : théorie interne de preuve (dans Impossibility.lean)

Vous représentez une théorie interne (S2) par :

un type interne PropT,

Provable : PropT → Prop,

FalseT,

Not : PropT → PropT,

une consistance minimale ¬ Provable FalseT,

une règle absurd : Provable p → Provable (Not p) → Provable FalseT.


Ce n’est pas “vague” : c’est une structure explicite, suffisante pour l’argument diagonal.


---

6) T2 : non-internalisabilité de la valuation canonique (Impossibility.lean)

6.1 Internalisation : InternalHaltingPredicate

Formalise “S2 internalise Rev0_K” via un prédicat interne H : Code → PropT qui est :

total : Provable (H e) ou Provable (Not (H e)) pour tout e,

correct : si Rev0_K ... e est vrai externement, alors Provable (H e),

complet : si Rev0_K ... e est faux externement, alors Provable (Not (H e)).


6.2 Impossibilité : T2_impossibility

Énoncé :

il n’existe pas de tel H (pas de total + correct + complet).


Point de dépendance essentiel (et assumé dans le code) :

la structure ImpossibleSystem contient un champ de diagonalisation diagonal_program qui relie Rev0_K à Provable(Not(H e)).


Interprétation :

la valuation canonique existe (T1),

mais S2 ne peut pas l’absorber comme prédicat interne parfait (total/correct/complet) sous diagonalisation + consistance minimale.



---

7) Statut “sans axiome Lean”

pas d’axiomes Lean (axiom, constant non défini, sorry),

mais des hypothèses mathématiques explicites :

DetectsMonotone pour T1,

consistance + absurd + diagonal_program pour T2,

hypothèses Truth/soundness et témoins explicites pour T3.



C’est un point de force : la porte d’entrée est explicite.


---

8) T3 : complémentarité opérative (Complementarity.lean)

Idée : T3 n’essaie pas de rendre S2 complète. T3 donne des opérateurs pour continuer :

identifier des frontières (vrai au sens externe / non prouvable),

construire des extensions sound qui ajoutent ce qui manque,

organiser des familles d’extensions.


8.1 Frontière one-sided : S1Set et extension S3Set

S1Set S encode_halt : ensemble des formules encode_halt e telles que :

kit-certified : Rev0_K (KitOf S) (Machine e),

non prouvable : ¬ Provable (encode_halt e).


S3Set S S2 encode_halt := S2 ∪ S1Set S encode_halt.


8.2 Extension faible explicite : T3_weak_extension_explicit

Ce théorème ne fabrique pas le témoin.

Il dit :

si tu as un témoin (e, kit-certified, non-prouvable),

et une notion externe Truth avec soundness sur S2,

et une hypothèse de correction Rev0_K → Truth(encode_halt e),


alors S3 := S2 ∪ S1Set :

reste sound,

contient l’énoncé ajouté,

et se reconnecte proprement au “halting réel” via T1.


C’est un opérateur d’extension sound.

8.3 Lemme strictement plus faible : exists_unprovable_encode_halt

Donne un e tel que ¬Provable(encode_halt e) sous certaines hypothèses.

Important :

il ne donne pas automatiquement “kit-certified”.

il est explicitement plus faible que “S1Set non vide”.


8.4 Théorème fort en famille : T3_strong

InfiniteS1 packe une infinité de témoins (certifiés + non prouvables),

Partition découpe les indices,

on construit une famille d’extensions sound S3_family n, avec propriétés de disjonction liées à la partition.


8.5 Variante two-sided locale : OraclePick et T3_oracle_extension_explicit

OraclePick choisit soit encode_halt e soit encode_not_halt e, certifié par le kit.

Le théorème d’extension ajoute exactement le choix, conserve soundness, et relie le choix à une assertion halting/non-halting via T1 (avec hypothèses h_pos/h_neg).


Point clé :

T3 fournit des opérateurs concrets pour avancer sans prétendre à une complétude interne impossible.



---

9) Lecture “catégorie poset” (niveau conceptuel, sans dépendance Lean)

Théories comme objets d’un poset (inclusion),

Extensions comme morphismes,

Unions dirigées de chaînes comme “colimites filtrées” (dans un poset, c’est juste l’union).


Ce que T3 apporte dans cette lecture :

“soundness” est stable par certains opérateurs d’extension (si les hypothèses Truth associées tiennent),

donc on peut itérer des extensions tout en restant dans la zone sound.



---

10) Extension optionnelle : dériver la diagonale au lieu de la postuler (non validée ici)

Dans Impossibility.lean, la diagonalisation est un champ (diagonal_program). Un raffinement possible (si vous avez ou ajoutez les fichiers/modèles requis) est :

remplacer l’axiome structurel par des ingrédients standard (représentation de la preuve par machine + point fixe / recursion theorem),

puis dériver diagonal_program.


Ce point est une amélioration d’ingénierie et de canonicité, mais il n’est pas nécessaire pour la cohérence T1/T2/T3 telle qu’elle est déjà prouvée.


---

11) Pipeline complet “sans illusion”

1. Traces : halting = existence d’un témoin


2. up : rend toute trace monotone


3. Kit + DetectsMonotone : ∃ uniforme sur monotones


4. T1 : valuation canonique = halting, et unicité


5. S2 : théorie interne de preuve (Provable/Not/FalseT + consistance)


6. T2 : impossible d’internaliser totalement la valuation canonique (total+correct+complet) sous diagonalisation


7. T3 : opérateurs d’extensions sound (frontière one-sided, oracle two-sided, familles) pour continuer sans complétude interne globale




---

12) Formulations prêtes (sans LaTeX)

(A) T1 (anglais, Lean-faithful)

All observers that uniformly detect existence on monotone traces implement a halting valuation: their canonical verdict agrees extensionally with halting on every trace.

(B) T2 (anglais)

No sufficiently strong internal proof theory can internalize this canonical halting valuation as a total, correct, and complete internal predicate (under a diagonalization bridge and minimal consistency).

(C) T3 (anglais)

Complementarity provides explicit, sound extension operators (including one-sided frontier extensions and two-sided oracle picks) that allow modeling to proceed without assuming impossible global internal completeness; these extensions can be organized into families.

