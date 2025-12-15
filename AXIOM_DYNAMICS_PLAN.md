# Axiom Dynamics - Plan d'implementation

## Vue d'ensemble

Objectif : Construire un calcul de manipulation d'axiomes ou on deplace une theorie locale dans un espace de theories, en controlant la soundness, avec Rev comme invariant operatif.

---

## I. Inventaire des theoremes existants

### A. Theorie fondamentale (Theory/)

| Theoreme | Fichier | Role |
|----------|---------|------|
| T1_traces | Canonicity.lean | Invariant - Rev canonise le verdict |
| T1_uniqueness | Canonicity.lean | Invariant - independance du kit |
| T1_semantics | Canonicity.lean | Invariant - lien CloK et Truth |
| T2_impossibility | Impossibility.lean | Carburant - source du gap |
| T3_weak_extension | Complementarity.lean | Move - existence de deplacement |
| T3_strong | Complementarity.lean | Bifurcation - structure de branchement |

### B. Contextes et Gap (Bridge/Context.lean)

| Theoreme | Role |
|----------|------|
| encoding_cannot_be_complete | Carburant - version directe de T2 |
| undecidable_code_exists | Carburant - code indecidable existe |
| true_but_unprovable_exists | Carburant - verite non prouvable existe |
| gapWitness_nonempty | Carburant - le temoin existe |
| GapWitness.truth | Node - certificat de verite |
| GapWitness.not_provable | Carburant - hors ProvableSet |
| independent_code_exists | Carburant - independance avec soundness |
| ProvableSet_sound | Node - ProvableSet est sound |
| strict_extension | Move + Strictness |
| strict_extension' | Move + Strictness variante |

### C. API de complementarite (Bridge/ComplementarityAPI.lean)

| Theoreme | Role |
|----------|------|
| extension_sound_of_gapWitness | Preservation - move preserve soundness |
| extension_strict_of_fresh | Strictness - fraicheur implique inclusion stricte |
| extension_strict_of_gapWitness_of_fresh | Strictness specialise |
| extension_strict_of_gapWitness_of_subset_Provable | Strictness via ProvableSet |
| no_sound_contains_p_and_not_p | Bifurcation - pas de contradiction |
| not_both_sound_extend_p_and_not | Bifurcation - pas de double extension |
| not_both_sound_extensions_of_gapWitness | Bifurcation specialise |

### D. API locale (Bridge/LocalAPI.lean)

| Theoreme | Role |
|----------|------|
| extend_sound_of_gapWitness | Preservation duplicata |
| singleton_disjoint_singleton_not | Bifurcation - structure ensembliste |
| newPart_eq_singleton_of_not_mem | Move - caracterisation du delta |
| disjoint_newParts_of_gapWitness | Bifurcation - deltas disjoints |

### E. Modele rigoureux (Bridge/RigorousModel.lean)

| Theoreme | Role |
|----------|------|
| rm_compile_halts_equiv | Node - Program et Halts |
| rm_diagonal_def | Carburant - diagonale |
| no_anti_halting | Carburant - pas de complement RE |
| RevHalt_Master_Rigorous | Master - T1+T2+T3 pour RigorousModel |

### F. Master (Bridge/Master.lean)

| Theoreme | Role |
|----------|------|
| strict_extension_sound | Preservation + Strictness |
| RealHalts_eq_Halts | Invariant - T1 incarne |
| RevHalt_Master_Complete | Master - theoreme complet |

### G. Systeme Kinetique (Kinetic/)

| Theoreme | Fichier | Role |
|----------|---------|------|
| Gap_eq_GapTruth | System.lean | Invariant - pont Gap et Truth |
| gap_nonempty | System.lean | Carburant - le gap existe |
| independent_witness | System.lean | Carburant - version renforcee |
| gap_witness_truth | System.lean | Node - certificat |
| gap_witness_halts | System.lean | Invariant - lien avec Halts |
| VerRev_eq_CloK | System.lean | Invariant - Rev = CloK |
| gapK_nonempty | System.lean | Carburant - via kit |
| VerRev_invariant | System.lean | Invariant - kit-invariance |
| GapK_invariant | System.lean | Invariant - gap kit-invariant |

### H. Stratification (Kinetic/Stratification.lean)

| Theoreme | Role |
|----------|------|
| mem_MasterClo_iff | Path - caracterisation membership |
| mem_NewLayer_iff | Path - couche nouvelle |
| mem_GapLayer_iff | Path - couche gap |
| mem_BaseGap_iff | Carburant - caracterisation base |
| Next_mono | Path - monotonie du next |
| Chain_mono_succ | Path - chaine croissante |
| Chain_mono | Path - chaine monotone |
| BaseGap_nonempty | Carburant |
| NewLayer0_eq_Chain1 | Path - lien couches |
| GapLayer0_eq_BaseGap | Path - lien couches |
| GapLayer0_nonempty | Carburant |
| Chain_truth | Path + Node - chaine implique verite |
| Truth_for_all_of_MasterClo_univ | Path - couverture totale |

### I. Instance Stratifiee (Instances/StratifiedInstance.lean)

| Theoreme | Role |
|----------|------|
| Chain1_eq_TruthSet | Path - Chain 1 = Truth |
| MasterClo_eq_TruthSet | Path - stabilisation |
| MasterClo_univ_iff_all_true | Path - couverture ssi tout vrai |
| mem_BaseGap_iff_truth_not_provable | Carburant |
| BaseGap_eq_MasterClo_diff_Provable | Carburant - gap = exces |
| ProvableSet_ssubset_MasterClo | Carburant - inclusion stricte |
| gap_always_exists | Carburant |
| gap_drives_cover | Path + Carburant - gap implique couverture |
| gap_iff_cover_with_propagation | Path + Carburant - equivalence |
| gap_cover_structural_facts | Resume structurel |

### J. Oracle (Unified/Oracle.lean)

| Theoreme | Role |
|----------|------|
| oracle_not_internalizable | Invariant - Truth non internalisable |
| bridge_is_oracular | Invariant - pont = oracle |
| provable_implies_oracle | Invariant - Provable inclus dans Oracle |
| oracle_surplus_iff_gapTruth | Carburant - surplus = gap |
| oracle_authority_is_gap | Invariant - autorite externe = gap |

### K. MasterClosure (Unified/MasterClosure.lean)

| Theoreme | Role |
|----------|------|
| Master_Closure | Path - ProvableSet inclus strict dans CloK |
| Truth_is_CloK | Invariant - Truth = CloK |
| TheGreatChain | Invariant - chaine d'equivalences |

### L. Closure (Unified/Closure.lean)

| Theoreme | Role |
|----------|------|
| DR0_semantic_iff_verdict | Invariant - consequence ssi verdict |
| DR1_verdict_invariant | Invariant - verdict kit-invariant |
| CloRev_mem_iff_CloK_mem | Invariant - CloRev = CloK |
| CloRev_mem_invariant | Invariant |
| Bridge_semantic_iff_CloK_mem | Invariant - pont |
| DR0_semantic_iff_CloRev_mem | Invariant |
| DR1_CloRev_mem_invariant | Invariant |

### M. Extensions (RefSystem, OmegaChaitin)

| Theoreme | Role |
|----------|------|
| DR0_ref | Transport - verdict via RefSystem |
| DR1_ref | Transport - invariance |
| DR0_omega | Transport - specialise Omega |
| DR1_omega | Transport - Omega kit-invariant |
| omega_bit_halts | Transport - Omega via bits |

### N. Instances concretes (Arithmetization, PA)

| Theoreme | Role |
|----------|------|
| pr_diagonal_halting | Carburant - diagonale Mathlib |
| pr_loop_non_halting | Node - code non-halting |
| pr_no_complement_halts | Carburant - pas de complement |
| pr_kit_correct | Invariant - kit PRModel |
| pr_encode_correct | Node - encodage correct |
| pr_repr_provable_not | Carburant - arithmetisation |
| PRModel_Master_Theorem | Master - instance complete |
| PA_Master_Theorem | Master - instance PA |

---

## II. Classification par role

### Invariant (Rev comme etiquetage stable)
- T1_traces, T1_uniqueness, T1_semantics
- Gap_eq_GapTruth, VerRev_eq_CloK, VerRev_invariant, GapK_invariant
- TheGreatChain, Truth_is_CloK
- DR0_*, DR1_* (6 theoremes)
- oracle_not_internalizable, bridge_is_oracular, oracle_authority_is_gap

### Carburant (T2 comme generateur de moves)
- T2_impossibility
- true_but_unprovable_exists, gapWitness_nonempty, independent_code_exists
- gap_nonempty, BaseGap_nonempty, gap_always_exists
- ProvableSet_ssubset_MasterClo, oracle_surplus_iff_gapTruth

### Preservation (moves preservent soundness)
- extension_sound_of_gapWitness
- extend_sound_of_gapWitness
- strict_extension_sound

### Strictness (moves sont non-triviaux)
- extension_strict_of_fresh
- extension_strict_of_gapWitness_of_fresh
- extension_strict_of_gapWitness_of_subset_Provable
- strict_extension, strict_extension'

### Bifurcation (pas de double extension contradictoire)
- T3_strong
- no_sound_contains_p_and_not_p
- not_both_sound_extend_p_and_not
- disjoint_newParts_of_gapWitness

### Path (trajectoires dans le graphe)
- Chain_mono, Chain_truth
- Master_Closure
- gap_drives_cover, gap_iff_cover_with_propagation
- Truth_for_all_of_MasterClo_univ

### Transport (morphismes entre representations)
- DR0_ref, DR1_ref
- DR0_omega, DR1_omega, omega_bit_halts

---

## III. Theoremes manquants

| Concept | Theoreme requis | Existe |
|---------|-----------------|--------|
| Node bundle | TheoryNode comme Sigma-type | Non |
| Move type | Move comme inductive | Non |
| Apply fonctionnel | Move.apply : Move -> Node -> Node | Non |
| Edge relation | Edge T T' := existe m, apply m T = T' | Non |
| Path inductif | Path ctx T T' | Non (Chain implicite) |
| Rev explicite | RevLabel : PropT -> Prop nomme | Non (implicite) |
| Fuel theoreme | fuel_from_T2 : T inclus Provable -> existe move strict | Non |
| Transport morphisme | TheoryMorphism | Non |

---

## IV. Plan d'execution

### Phase 0 : Decisions

1. Certificat : TheorySound seul (OK - suffisant)
2. Move : Inductive avec preuve embarquee (recommande)
3. Apply : Fonction, pas relation (plus simple)
4. Path : Generalisation de Chain (oui)

### Phase 1 : Fondations

Fichiers : Dynamics/Node.lean, Dynamics/Move.lean

Reutilise :
- TheorySound de ComplementarityAPI.lean
- Extend de ComplementarityAPI.lean
- GapWitness de Context.lean

Ajoute :
- TheoryNode = (theory : Set PropT, sound : TheorySound ctx theory)
- Move = extend | extend_gap | restrict
- Move.apply

### Phase 2 : Lois

Fichier : Dynamics/Laws.lean

Migre avec reformulation :
- extension_sound_of_gapWitness -> apply_preserves_sound
- extension_strict_of_fresh -> apply_strict
- not_both_sound_extend_p_and_not -> no_dual_sound

Conserve en place :
- Les theoremes originaux (pas de breaking change)

### Phase 3 : Carburant

Fichier : Dynamics/Fuel.lean

Combine :
- true_but_unprovable_exists
- gap_nonempty
- ProvableSet_ssubset_MasterClo

Produit :
- fuel_from_T2 : T inclus ProvableSet -> existe strict move

### Phase 4 : Invariant

Fichier : Dynamics/Invariant.lean

Extrait et nomme :
- RevLabel := Halts (LR vide p)
- rev_eq_truth (depuis h_bridge)
- rev_kit_invariant (depuis VerRev_invariant)

### Phase 5 : Graph + Path

Fichiers : Dynamics/Graph.lean, Dynamics/Path.lean

Definit :
- Edge T T'
- Path T T' (inductif)
- Path.length, Path.concat

Lie :
- Chain n <-> Path de longueur n

### Phase 6 : Transport

Fichier : Dynamics/Transport.lean

Definit :
- TheoryMorphism
- transport_node
- transport_preserves_edge

Connecte a RefSystem.lean

### Phase 7 : Structure unifiee

Fichier : Dynamics/System.lean

Bundle tout dans AxiomDynamics

---

## V. Estimation

| Phase | Lignes | Dependances |
|-------|--------|-------------|
| 1 | 80 | - |
| 2 | 100 | Phase 1 |
| 3 | 60 | Phase 2 |
| 4 | 50 | Phase 1 |
| 5 | 100 | Phase 2 |
| 6 | 100 | Phase 5 |
| 7 | 50 | Toutes |

Total : environ 540 lignes

---

## VI. Theoremes a ne pas toucher

Ces theoremes restent dans leurs fichiers d'origine :
- T1_*, T2_*, T3_* (Theory/)
- *_Master_* (Bridge/, Instances/)
- TheGreatChain, Master_Closure (Unified/)
- DR0_*, DR1_* (Unified/Closure, Extensions/)

Le module Dynamics/ reutilise ces theoremes, il ne les remplace pas.

---

## VII. Architecture finale

```
RevHalt/
  Dynamics/
    Node.lean        <- Sigma-type (T, certificat)
    Move.lean        <- Inductive des operations
    Graph.lean       <- Relation d'arete
    Laws.lean        <- Reformulation de ComplementarityAPI
    Fuel.lean        <- T2 comme generateur
    Invariant.lean   <- Rev comme etiquetage
    Path.lean        <- Generalisation de Chain
    Transport.lean   <- Connexion avec RefSystem
    System.lean      <- Structure unifiee AxiomDynamics
```
