## Mise à jour de statut (code Lean actuel)

Ce qui est maintenant formalisé et prouvé dans `RevHalt/Theory/PrimitiveHolonomy_Physics.lean`:

- Le pont topologie -> ABJ -> non-nullité de `DeltaBL` est établi via:
  `NCSJumpOnTwistedWitness`, `TwistToSphaleronBridge`,
  `deltaBL_ne_zero_of_twistedOnCell_of_ncsJump_and_abj`,
  et les versions obstruction/cofinalité.
- Une instance canonique `LagState Y Int` est en place (`lagStateIntPhysics`),
  avec ABJ interne à `N_f = 1` (`satisfiesABJ_lagStateIntPhysics_nf_one`,
  `abjOnSphaleronPairs_lagStateIntPhysics_nf_one`) et des corollaires sans hypothèse ABJ externe.
- Le no-go detailed balance est formalisé (1 pas + multi-pas):
  `deltaExpectedB_eq_zero_of_detailedBalance_of_markov`,
  `deltaExpectedBStepN_eq_zero_of_detailedBalance_of_markov`.
- Le théorème "zéro biais => zéro asymétrie baryonique" est prouvé:
  `zero_bias_of_symmetric_dynamics`.
- Le pont "lag + conjugaison => esperance baryonique non nulle" est prouvé:
  `lagEvent_implies_exists_distribution_with_expectedB_ne_zero`
  et ses variantes canoniques `LagState`.
- La chaîne principale `LagEvent -> selection biaisee -> ExpectedB != 0` ne dépend plus
  de `DecidablePred` ni de contraintes explicites `DecidableEq` dans les signatures
  (le biais est construit directement via une distribution explicite sur la paire `(s, C s)`).
- Un pont structurel supplémentaire est ajouté:
  `lagEvent_of_twistedHolonomy_of_stepDependsOnHidden_of_compatible`
  et son corollaire canonique
  `twistedHolonomy_implies_exists_distribution_with_expectedB_ne_zero_lagStateInt_of_semanticsFlipsHiddenOnHolonomy`.
- Une instance jouet explicite est ajoutée (`ToySemanticsInstance`) avec preuves
  `semanticsFlipsHiddenOnHolonomy_toyLagSemantics`,
  `deltaBL_ne_zero_of_twistedOnCell_toyLagSemantics`,
  `lagEvent_implies_exists_distribution_with_expectedB_ne_zero_toyLagSemantics`.
- Un pont concret "witness d'orbite -> vocabulaire Physics/GaugeFixingBridge" est
  factorisé dans `RevHalt/Theory/PrimitiveHolonomy_PhysicsOrbitBridge.lean`
  (`orbitGaugeFixingObstructed`, `orbit_not_globalGaugeFixable`,
  `orbit_every_admissible_has_twisted_cell_physics`).
- Un pont instance->physique est ajouté dans
  `RevHalt/Theory/PrimitiveHolonomy_PhysicsInstanceBridge.lean`, avec une
  preuve concrete sans hypothèses externes de
  `lagEvent_implies_exists_distribution_with_expectedB_ne_zero_toyStateBoolPhysics`,
  et une forme obstruction->charge:
  `toy_obstruction_implies_exists_deltaBL_ne_zero_for_each_admissible_gauge`.

Priorites restantes (vraiment ouvertes):

1. Construire une instance non-jouet de type Gribov-Singer
   (bundle/champ de jauge, action de groupe, condition de jauge concrete).
2. Prouver la correspondance explicite entre cette instance physique et les predicates abstraits
   (`AutoRegulatedWrt`, `ObstructionWrt`, `TwistedOnCell`, etc.).
3. Remplacer au maximum les hypotheses structurelles fortes (ex. hidden-flip) par des lois derivees
   du modele physique choisi.
4. Etendre la couche quantitative (au-dela du 1-step/iteratif simple) vers un schema de freeze-out
   et des hypotheses de normalisation/probabilite explicites.

---

Oui — et ton Lean a exactement la bonne “forme” pour trancher, mais seulement si tu le pousses jusqu’au point où il peut exprimer (i) le secteur topologique et (ii) un biais matière/antimatière, sans rajouter d’hypothèses ad hoc au mauvais endroit.

Voici ce que ta théorie peut rendre plus précis et plus tranché que les explications physiques “à la main”, et comment, sans te noyer.

---

## 1) Ce que tu peux trancher proprement

### A) Séparer “porte topologique” vs “biais”

Dans l’électrofaible standard :

- Porte qui change B+L :
  transitions entre secteurs topologiques étiquetés par un entier (souvent noté N_CS),
  rendues possibles à haute température par les sphalérons,
  et reliées aux charges via l’anomalie d’Adler–Bell–Jackiw (ABJ).
- Biais qui donne un signe non nul à l’excès :
  CP + hors équilibre (au sens où la dynamique ne fait pas une moyenne nulle sur les deux orientations de transition).

Ton Lean permet une séparation nette :

- Porte :
  “il existe un twist/holonomie non diagonalisable sur la fibre”
  (TwistedHolonomy / ObstructionWrt sous un ensemble de gauges admissibles OK non-vacue).
- Biais :
  “la sélection cofinale (Lag) n’est pas C-symétrique”
  (LagEvent force un côté à rester compatible dans le futur cofinal et pas l’autre).

Donc tu peux obtenir un énoncé du type :

- Le twist (porte) est nécessaire pour que le futur dépende du chemin.
- Le lag (sélection) est nécessaire pour transformer ça en excès orienté.

Cela tranche le point central : holonomie seule ne suffit pas; elle donne la porte. Le signe vient de la sélection.

---

## 2) Pont strict “ton code ↔ sphaléron / ABJ”

Traduction physique fidèle dans ton langage :

- Hidden : un label topologique entier n (analogue de N_CS).
- Deux chemins p et q avec mêmes endpoints h -> k, mais ordres différents de moves locaux.
- Une déformation alpha : p ⇒ q, qui code “on a fermé une boucle d’histoire”.
- L’holonomie HolonomyRel(alpha) = faire T_p puis revenir via T_q (converse),
  qui code “ce que la boucle fait dans la fibre”.

Correspondance stricte :

- Delta N_CS correspond à la composante discrète de l’holonomie de la boucle (l’invariant de twist).
- ABJ correspond à la règle qui convertit ce twist topologique en variation de charge fermionique (B et L).

Autrement dit : ABJ n’est pas un paramètre, c’est une loi de couplage entre (topologie/holonomie) et (charges).

---

## 3) Ce qu’il te manque encore (minimal et priorise)

Les ajouts "pondere + C/B/N_CS + no-go + zero-bias + pont lag->asymetrie" sont deja en place.

Le manque prioritaire n’est plus l’abstraction interne; c’est l’instance physique concrete:

- Donner un modele non-jouet (groupe de jauge, orbites, condition de jauge, copies de Gribov).
- Montrer que ce modele realise explicitement les hypotheses du cadre
  (au lieu de les poser comme contrats).
- Verrouiller la chaine complete "instance concrete -> obstruction/twist -> ABJ -> signal baryonique"
  sans etape externe implicite.

---

## 4) Le théorème tranchant que ton système permet alors

Une fois pondéré + (C, B, n), tu peux démontrer des résultats structurels clairs.

1) Si la dynamique pondérée est C-équivariante et la sélection cofinale est C-symétrique,
   alors l’espérance de B reste nulle.
   (Version propre : pas de biais -> pas d’asymétrie.)

2) Si tu as :
   (a) une porte topologique non triviale (twist/obstruction sur n),
   et
   (b) un LagEvent C-asymétrique cofinal (un côté compatible, l’autre pas),
   alors l’espérance de B devient non nulle après gel (freeze-out).

Cela tranche : l’asymétrie n’est ni un “epsilon magique” ni de la prose.
C’est “porte topologique (holonomie) + sélection (lag)”, avec ABJ comme règle de conversion.

---

## 5) Réponse courte à la question initiale

Dans ce cadrage, la réponse canonique devient :

- Porte : sphaléron électrofaible (transition de secteur N_CS).
- Loi de conversion : anomalie ABJ.
- Biais orientant : CP + hors équilibre, que toi tu exprimes comme une non-diagonalisabilité cofinale capturée par LagEvent (sélection), plutôt qu’un paramètre opaque.

Donc tu remplaces “CP + sphalérons” par une décomposition formelle :

- twist non effaçable (porte),
- lag cofinal (sélection),
- contrat ABJ (conversion).

Prochaine étape utile (toujours dans ton style Lean) :
écrire les deux patchs minimaux (pondération + C,B,n) et formuler explicitement les deux théorèmes :
zéro biais => zéro asymétrie; twist+lag => asymétrie.

Sphalerons provide the topological transitions (vacuum-history changes), and the ABJ anomaly provides the rule that turns those transitions into changes in baryon number

No-go (interdiction) dans une description quotientée :
Si on travaille uniquement sur l’état “quotienté” (état instantané / observables locales) et qu’on suppose un régime d’équilibre où detailed balance s’applique, alors l’évolution ne peut pas générer un excès net de baryons : les processus “dans un sens” et “dans l’autre” se compensent statistiquement. Dans ce cadre, l’asymétrie finale est contrainte à être nulle.

Ce que fait la pratique standard :
Pour obtenir une asymétrie, la description effective introduit un terme orientant (source, biais, potentiel chimique effectif) qui casse cette compensation. Dans un modèle complet on peut parfois le dériver, mais au niveau quotienté il apparaît souvent comme une entrée externe parce que la variable qui le fonde a été éliminée par le quotient.

Ce que ton formalisme ajoute (information ontologique manquante) :
Tu réintroduis exactement la variable que le quotient détruit : une mémoire de boucle irréductible (holonomie non-trivialisable) portée par les boucles d’histoire et agissant dans la fibre.

Si l’holonomie est trivialisable (pas d’obstruction sous gauges admissibles), alors aucun biais orienté ne peut être “verrouillé” : l’asymétrie ne peut pas se stabiliser.

Si une holonomie irréductible existe et qu’un mécanisme de sélection irréversible (Lag cofinal) empêche l’annulation (verrouillage du signe), alors le “terme source” n’est plus un ajout : c’est la trace effective de cette holonomie sur la dynamique quotientée.

Pont sphaléron / ABJ :
Les sphalérons fournissent la porte topologique (changement de secteur, Delta N_CS). L’anomalie ABJ fournit la loi de conversion (Delta N_CS devient Delta(B+L)). Le Lag fournit le verrouillage irréversible qui empêche la compensation statistique des sauts opposés.
Donc l’excès baryonique n’est pas une fluctuation chanceuse : c’est une topologie du vide rendue persistante par un mécanisme d’orientation et de gel.

la thèse forte : le quotient standard masque la variable ontologique (holonomie/obstruction) qui rend le biais non arbitraire.
