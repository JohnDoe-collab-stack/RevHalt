# Axiom Dynamics - Plan d'implementation (v2)

## Vue d'ensemble

Objectif : Construire un calcul de manipulation d'axiomes ou on deplace une theorie locale dans un espace de theories, en controlant la soundness, avec Rev comme invariant operatif.

---

## CORRECTIONS STRUCTURELLES

### Correction 1 : Deux couches distinctes

- **Dynamics-Core** (niveau EnrichedContext)
  - Theorie = Set PropT
  - Validite = TheorySound ctx T
  - Moves = Extend
  - Bifurcation via Not
  - Carburant via GapWitness / independent_code_exists

- **Dynamics-Operative** (niveau VerifiableContext)
  - Ajoute LR, Halts, CloK, Rev
  - Bridge dynamique
  - Invariance kit

Consequence : Dynamics/Invariant.lean depend de VerifiableContext, pas EnrichedContext.

### Correction 2 : Path general vs Chain embedding

- Path = structure generale du graphe (plusieurs types de moves)
- Chain = cas particulier (iteration d'un seul endofoncteur Next)
- Relation : Chain s'embarque dans Path, mais pas equivalence

### Correction 3 : Deduplication API

- ComplementarityAPI.lean = API canonique pour le calcul
- LocalAPI.lean = helper pour lemmes ensemblistes (pas fondation)

### Correction 4 : Transport functoriel

- Move interne = agit sur Set PropT dans le meme langage
- Transport = passage PropT -> PropT' (relie deux graphes)
- Dynamics/Transport.lean = module functoriel, pas variante d'Extend

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

### C. API de complementarite (Bridge/ComplementarityAPI.lean) - CANONIQUE

| Theoreme | Role |
|----------|------|
| extension_sound_of_gapWitness | Preservation - move preserve soundness |
| extension_strict_of_fresh | Strictness - fraicheur implique inclusion stricte |
| extension_strict_of_gapWitness_of_fresh | Strictness specialise |
| extension_strict_of_gapWitness_of_subset_Provable | Strictness via ProvableSet |
| no_sound_contains_p_and_not_p | Bifurcation - pas de contradiction |
| not_both_sound_extend_p_and_not | Bifurcation - pas de double extension |

### D. API locale (Bridge/LocalAPI.lean) - HELPER

| Theoreme | Role |
|----------|------|
| newPart_eq_singleton_of_not_mem | Helper - caracterisation du delta |
| disjoint_newParts_of_gapWitness | Helper - deltas disjoints |

### E. Systeme Kinetique (Kinetic/) - NIVEAU VERIFIABLE

| Theoreme | Fichier | Role |
|----------|---------|------|
| Gap_eq_GapTruth | System.lean | Invariant-Operative |
| gap_nonempty | System.lean | Carburant |
| VerRev_eq_CloK | System.lean | Invariant-Operative |
| VerRev_invariant | System.lean | Invariant-Operative - kit-invariance |
| GapK_invariant | System.lean | Invariant-Operative |

### F. Stratification (Kinetic/Stratification.lean)

| Theoreme | Role |
|----------|------|
| Chain_mono | Path-Embedding (cas particulier) |
| Chain_truth | Path-Embedding + Node |
| Truth_for_all_of_MasterClo_univ | Path - couverture totale |
| gap_drives_cover | Path + Carburant |

### G. Oracle (Unified/Oracle.lean) - NIVEAU VERIFIABLE

| Theoreme | Role |
|----------|------|
| oracle_not_internalizable | Invariant-Operative |
| bridge_is_oracular | Invariant-Operative |
| oracle_authority_is_gap | Invariant-Operative |

### H. MasterClosure + Closure (Unified/) - NIVEAU VERIFIABLE

| Theoreme | Role |
|----------|------|
| TheGreatChain | Invariant-Operative - chaine d'equivalences |
| DR0_*, DR1_* | Invariant-Operative - kit-invariance |

### I. Extensions (RefSystem, OmegaChaitin) - TRANSPORT

| Theoreme | Role |
|----------|------|
| DR0_ref, DR1_ref | Transport-Functoriel |
| DR0_omega, DR1_omega | Transport-Functoriel |

---

## II. Classification par role et niveau

### NIVEAU ENRICHED (Dynamics-Core)

**Carburant**
- T2_impossibility
- true_but_unprovable_exists, gapWitness_nonempty, independent_code_exists

**Preservation**
- extension_sound_of_gapWitness

**Strictness**
- extension_strict_of_fresh
- extension_strict_of_gapWitness_of_*

**Bifurcation**
- T3_strong
- no_sound_contains_p_and_not_p
- not_both_sound_extend_p_and_not

### NIVEAU VERIFIABLE (Dynamics-Operative)

**Invariant-Operative**
- T1_traces, T1_uniqueness
- Gap_eq_GapTruth, VerRev_eq_CloK, VerRev_invariant, GapK_invariant
- TheGreatChain, DR0_*, DR1_*
- oracle_not_internalizable, bridge_is_oracular, oracle_authority_is_gap

**Path (general) + Chain (embedding)**
- Chain_mono, Chain_truth (embedding dans Path)
- gap_drives_cover, Truth_for_all_of_MasterClo_univ

### TRANSPORT (inter-graphes)

- DR0_ref, DR1_ref
- DR0_omega, DR1_omega

---

## III. Theoremes manquants

| Concept | Theoreme requis | Niveau |
|---------|-----------------|--------|
| Node bundle | TheoryNode comme Sigma-type | Core |
| Move type | Move comme inductive | Core |
| Apply fonctionnel | Move.apply : Move -> Node -> Node | Core |
| Edge relation | Edge T T' | Core |
| Fuel theoreme | fuel_from_T2 | Core |
| Path inductif | Path ctx T T' | Core |
| Chain embedding | chain_embeds_path | Core |
| Rev explicite | RevLabel | Operative |
| Transport morphisme | TheoryMorphism | Transport |

---

## IV. Plan d'execution revise

### Phase 1 : Dynamics-Core (niveau EnrichedContext)

Fichiers :
- Dynamics/Core/Node.lean
- Dynamics/Core/Move.lean
- Dynamics/Core/Laws.lean
- Dynamics/Core/Fuel.lean

Contenu :
- TheoryNode = (theory, sound)
- Move = extend | extend_gap | restrict
- Move.apply
- Lois : preservation, strictness, bifurcation
- fuel_from_T2

Dependances : Bridge/Context, Bridge/ComplementarityAPI

### Phase 2 : Graph + Path (niveau EnrichedContext)

Fichiers :
- Dynamics/Core/Graph.lean
- Dynamics/Core/Path.lean

Contenu :
- Edge T T'
- Path T T' (inductif general)
- Path.length, Path.concat

### Phase 3 : Chain Embedding (niveau VerifiableContext)

Fichier : Dynamics/Operative/ChainEmbed.lean

Contenu :
- chain_embeds_path : Chain n induit Path de longueur n
- (pas d'equivalence generale)

Dependances : Kinetic/Stratification, Dynamics/Core/Path

### Phase 4 : Invariant Operatif (niveau VerifiableContext)

Fichier : Dynamics/Operative/Invariant.lean

Contenu :
- RevLabel := Halts (LR vide p)
- rev_eq_truth (depuis h_bridge)
- rev_kit_invariant (depuis VerRev_invariant)
- gap_via_rev

Dependances : Kinetic/System, Kinetic/MasterClosure

### Phase 5 : Transport Functoriel (inter-graphes)

Fichier : Dynamics/Transport/Morphism.lean

Contenu :
- TheoryMorphism (ctx1 -> ctx2)
  - map : PropT1 -> PropT2
  - preserves_truth
  - preserves_not
- transport_node
- transport_preserves_edge

Ce n'est PAS un Move interne, c'est un foncteur entre graphes.

Dependances : Extensions/RefSystem

### Phase 6 : Structure unifiee

Fichier : Dynamics/System.lean

Bundle :
- AxiomDynamicsCore (niveau EnrichedContext)
- AxiomDynamicsOperative (niveau VerifiableContext, etend Core)

---

## V. Architecture finale

```
RevHalt/
  Dynamics/
    Core/
      Node.lean         <- TheoryNode (niveau EnrichedContext)
      Move.lean         <- Move inductive
      Laws.lean         <- Preservation, Strictness, Bifurcation
      Fuel.lean         <- T2 comme generateur
      Graph.lean        <- Edge
      Path.lean         <- Path general
    Operative/
      ChainEmbed.lean   <- Chain s'embarque dans Path
      Invariant.lean    <- Rev (niveau VerifiableContext)
    Transport/
      Morphism.lean     <- TheoryMorphism (functoriel)
    System.lean         <- Bundle unifie
```

---

## VI. Estimation

| Phase | Lignes | Dependances |
|-------|--------|-------------|
| 1 | 150 | - |
| 2 | 80 | Phase 1 |
| 3 | 40 | Phase 2 |
| 4 | 60 | Phase 1 |
| 5 | 80 | Phase 2 |
| 6 | 50 | Toutes |

Total : environ 460 lignes

---

## VII. Fichiers existants

Restent en place sans modification :
- Theory/* (T1, T2, T3)
- Bridge/ComplementarityAPI.lean (API canonique)
- Bridge/LocalAPI.lean (helper)
- Kinetic/* (Gap, Chain, Stratification)
- Oracle.lean
- Extensions/RefSystem.lean

Le module Dynamics/ reutilise ces theoremes.

