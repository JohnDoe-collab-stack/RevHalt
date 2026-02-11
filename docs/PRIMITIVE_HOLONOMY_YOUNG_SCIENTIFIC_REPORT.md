# Rapport Scientifique de Validation
## Module `PrimitiveHolonomy.Physics` - Couche Young

## Résumé exécutif
Ce module ne remplace pas l'algèbre standard de Young; il la formalise et la factorise.

Il conserve exactement les mêmes lois d'intensité que la MQS pour le montage à deux chemins, tout en déplaçant la source conceptuelle de la phase relative: dans ce cadre, la phase peut être dérivée d'une structure holonomique (selon des contrats précis), au lieu d'être seulement un paramètre cinématique posé d'emblée.

En bref:
1. Invariance prédictive: mêmes formules, mêmes bornes, mêmes cas limites.
2. Changement ontologique: le statut de `U` passe de donnée primitive à objet dérivable sous hypothèses de pont.
3. Gain théorique: la chaîne `holonomie -> phase -> interférence` est formalisée theorem-by-theorem.

## 1. Objet et périmètre
Le fichier `RevHalt/Theory/PrimitiveHolonomy_Young.lean` formalise la couche phénoménologique de l'interférence dans Lean:
- amplitudes complexes par fente,
- intensités cohérente/incohérente,
- terme d'interférence,
- paramètre de visibilité `η` pour la décohérence,
- pont vers les témoins holonomiques de `PrimitiveHolonomy`.

Contrainte méthodologique explicite:
- développement constructif (`no noncomputable`, `no classical`).

## 2. Noyau algébrique (identique à Young standard)
Définitions structurantes:
- `totalAmp = A_L + A_R`
- `coherentIntensity = |A_L + A_R|^2`
- `incoherentIntensity = |A_L|^2 + |A_R|^2`
- `interferenceTerm = 2 Re(A_L * conj(A_R))`
- `decoheredIntensity η = I_incoh + η I_int`

Identités fondamentales:
- `coherentIntensity_eq_incoherent_plus_interference`
- `decohered_minus_coherent_eq_eta_sub_one_mul_interference`
- `incoherent_minus_decohered_eq_neg_eta_mul_interference`

Conséquence physique immédiate:
- la décohérence agit comme un contrôle linéaire du terme d'interférence.

## 3. Couplage de phase: structure mathématique explicite
Le contrat local de phase est:
- `PhaseCoupledAt m x U : rightAmp = U * leftAmp`.

Résultats de structure:
- existence par quotient quand `A_L != 0`: `phaseCoupledAt_of_div`
- unicité du facteur de phase: `phaseCoupledAt_unique_of_leftAmp_ne_zero`
- unitarité du quotient sous égalité des normes: `normSq_div_eq_one_of_normSq_eq`

Lecture:
- sous hypothèses de ratio unitaire, la phase relative n'est pas arbitraire; elle est forcée par la dynamique des amplitudes.

## 4. Loi d'interférence sous couplage
Résultat clef:
- `interferenceTerm_of_phaseCoupled`

Forme:
- `I_int = 2 Re(U) |A_L|^2`.

Puis:
- `incoherentIntensity_of_phaseCoupled`
- `coherentIntensity_of_phaseCoupled`

et, en régime unitaire `|U|=1`:
- `incoherentIntensity_of_phaseCoupled_unit`
- `coherentIntensity_of_phaseCoupled_unit`
- `decoheredIntensity_of_phaseCoupled_unit`

Lecture physique:
- `Re(U)` est le canal de modulation effectif des franges.
- `η` est un gain de visibilité, pas un changement de loi de base.

## 5. Frange sombre: caractérisation forte
Théorème pivot:
- `coherentIntensity_zero_iff_re_eq_neg_one_of_phaseCoupled_unit_of_leftAmp_ne_zero`

Sous `|U|=1` et `A_L != 0`:
- `I_coh = 0 <-> Re(U) = -1`.

Conséquences:
- `interferenceTerm_of_phaseCoupled_of_re_eq_neg_one`
- `incoherentIntensity_sub_coherentIntensity_of_phaseCoupled_unit_of_re_eq_neg_one`
- `incoherentIntensity_sub_decoheredIntensity_of_phaseCoupled_unit_of_re_eq_neg_one`

Interprétation robuste:
- la frange sombre n'est pas seulement "absence de détection"; c'est un état de contrainte de phase extrême dans l'espace des couplages admissibles.

## 6. Pont holonomie -> observables
### 6.1 Contrat de pont
`HolonomyRelInducesPhaseAt` encode:
- pour un témoin holonomique `HolonomyRel ... α x x'`, il existe un `U` unitaire couplant les deux amplitudes au détecteur.

Théorèmes d'export:
- `exists_interference_formula_of_holonomyRel`
- `exists_coherent_formula_of_holonomyRel`
- `exists_decohered_formula_of_holonomyRel`

### 6.2 Régime sombre dérivé d'un témoin holonomique
- `exists_phase_re_eq_neg_one_of_coherent_zero_of_holonomyRel_of_leftAmp_ne_zero`
- `coherent_zero_iff_exists_phase_re_eq_neg_one_of_holonomyRel_of_leftAmp_ne_zero`
- `exists_incoherent_sub_decohered_formula_of_holonomyRel_of_coherent_zero_of_leftAmp_ne_zero`

Lecture:
- les formules expérimentales sont récupérées avec une variable de phase désormais indexée par la donnée holonomique.

## 7. Dérivation non-oraculaire de la phase
La section `DerivedPhaseFromWeightedSemantics` clarifie un point épistémique majeur:

1. Contrat fort `SemanticsRatioUnitaryOnHolonomy`:
- `A_L != 0`
- `|A_R|^2 = |A_L|^2`

2. Alors:
- existence: `semanticsDerivedUnitPhaseOnHolonomy_of_ratioUnitary`
- identification: `phase_eq_div_of_ratioUnitary`
- unicité: `existsUnique_unitPhaseCoupling_of_holonomyRel_of_ratioUnitary`

Conclusion:
- la phase peut être prouvée comme quotient contraint, pas seulement introduite par postulat.

## 8. Jouets concrets et fermeture opérationnelle
La section `ConcreteToyClosure` prouve la fermeture de la chaîne sur des instances explicites:
- `toyWeightedSemanticsUnit`, `toyCompleteHolonomyPhaseData`
- `holonomyRel_xPlus_xMinus_alphaFlip`
- `fixedPhaseYoungModel`

Cas limites reproduits:
- constructif maximal: `coherentIntensity_toyHolonomy_inPhase`
- quadrature sans contraste: `coherent_eq_incoherent_toyHolonomy_quadrature`
- angle `θ`: `coherentIntensity_fixedPhaseYoungModel_of_angle`, bornes et endpoints.

Ces preuves servent de validation d'intégration: le pont abstrait calcule correctement sur des objets fermés.

## 9. Compatibilité MQS: pourquoi il n'y a pas contradiction
Votre affirmation est correcte: ce cadre ne peut pas contredire les calculs standards de Young tant que l'on reste dans ce périmètre, car:

1. Les observables calculées sont les mêmes fonctions d'amplitudes complexes.
2. Les identités utilisées sont les identités usuelles de l'algèbre complexe.
3. Les résultats d'angle et de visibilité coïncident avec les lois attendues (`cos θ`, facteur `η`).

Références directes:
- `coherentIntensity_eq_incoherent_plus_interference`
- `decoheredIntensity_zero`, `decoheredIntensity_one`
- `coherentIntensity_fixedPhaseYoungModel_bounds_of_angle`
- `coherentIntensity_fixedPhaseYoungModel_zero_angle`
- `coherentIntensity_fixedPhaseYoungModel_pi_angle`

Donc la nouveauté n'est pas prédictive au niveau de ces formules; elle est structurale sur l'origine de la phase.

## 10. Différentiel épistémologique précis
| Axe | MQS (lecture standard) | Primitive Holonomy (lecture formalisée) |
| --- | --- | --- |
| Statut de `U` | Paramètre de phase de la description d'état | Objet dérivable d'un témoin holonomique (sous contrat) |
| Frange sombre | Annulation d'amplitudes | Condition nécessaire et suffisante `Re(U)=-1` (avec hypothèses explicites) |
| Décohérence `η` | Réduction de visibilité | Loi exacte du gap: `I_incoh - I_η = -η I_int` |
| Niveau de preuve | Calcul physique usuel | Certification Lean theorem-by-theorem |

## 11. Limites explicites (importantes)
Ce que ce fichier prouve:
- des implications formelles dans le cadre de ses définitions,
- une reconstruction cohérente des formules de Young,
- un pont mathématique de la holonomie vers la phase d'interférence.

Ce qu'il ne prouve pas à lui seul:
- une exclusivité ontologique globale sur toute MQS,
- une réfutation de modèles alternatifs de décohérence,
- une extension automatique à QFT, spin, relativité ou multi-fentes sans nouvelles sections formelles.

## 12. En quoi cela change la comprehension du phenomene
Le point clef est que tu transformes l'interference d'un fait descriptif (superposition) en un fait diagnostique (lecture d'une contrainte).

### 12.1 Nouvel invariant observable isole
Le module isole un invariant directement mesurable a partir des intensites:
- `ΔI(x) := I_coh(x) - I_incoh(x)` (defaut de coherence).

Et il prouve que cet invariant n'est pas une "interpretation", mais une identite:
- `coherenceDefect_eq_interferenceTerm` (donc `ΔI = I_int`).

Lecture: l'interference n'est pas un surplus vague de la superposition, c'est exactement le defaut `I_coh - I_incoh` encode en un terme unique.

### 12.2 Ce que cet invariant signifie sous contrat de phase
Sous `PhaseCoupledAt` (donc `A_R = U A_L`), l'invariant prend une forme canonique:
- `interferenceTerm_of_phaseCoupled`: `ΔI = 2 Re(U) |A_L|^2`.

En regime unitaire (`|U|=1`) et de normes egales, on obtient une lecture inverse en intensites seules:
- `incoherentIntensity_of_phaseCoupled_unit`: `I_incoh = 2 |A_L|^2`,
- `coherentIntensity_of_phaseCoupled_unit`: `I_coh = (2 + 2 Re(U)) |A_L|^2`,
- donc `Re(U) = I_coh / I_incoh - 1` (a condition de satisfaire les hypotheses de couplage unitaire).

Ce que ca change: le motif de franges ne "demande" pas une phase; il permet de reconstruire `Re(U)` a partir de donnees d'intensite, donc de contraindre la structure qui produit ce `U`.

### 12.3 Frange sombre: de l'absence a un marqueur structurel
La frange sombre devient une certification de contrainte, pas une simple annulation:
- `coherentIntensity_zero_iff_re_eq_neg_one_of_phaseCoupled_unit_of_leftAmp_ne_zero` donne `I_coh = 0 <-> Re(U) = -1` (si `A_L != 0`).

Lecture: un zero d'intensite, dans ce cadre, identifie un regime de couplage maximalement destructif (projection reelle minimale) et non un "vide".

### 12.4 De la prediction au probleme inverse (ce qui change vraiment la comprehension)
En MQS, l'effort porte surtout sur "donner une phase" (depuis une action, un modele d'onde, etc.) puis calculer les franges.
Ici, la question scientifique devient: "quelles contraintes holonomiques sur les histoires suffisent pour imposer l'existence (et parfois l'unicite) d'un `U` unitaire qui explique le motif observe?".

Ce deplacement est formalise par:\n+- `exists_unitPhaseCoupling_of_holonomyRel` (existence de `U` depuis holonomie),\n+- `phase_eq_div_of_ratioUnitary` et `existsUnique_unitPhaseCoupling_of_holonomyRel_of_ratioUnitary` (phase forcee par un quotient, donc non arbitraire).

En termes simples: tu ne proposes pas une nouvelle "arithmetique des franges", tu proposes une nouvelle theorie de ce que les franges attestent (une contrainte holonomique projetee).

## 13. Conclusion scientifique
La contribution du module est triple:

1. Conservativite empirique:
- les calculs et signatures standards de Young sont preserves.

2. Requalification ontologique:
- la phase n'est plus seulement un ingredient de depart; elle devient un objet derive d'une structure relationnelle.

3. Gain explicatif:
- l'interference n'est plus seulement un fait algebrique local, mais l'effet mesurable d'une organisation holonomique des trajectoires.

Autrement dit, la couche Young de `PrimitiveHolonomy.Physics` ne change pas les nombres predits; elle change ce que ces nombres veulent dire physiquement.
