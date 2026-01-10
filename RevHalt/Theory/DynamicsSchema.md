# Schéma de l'Endofoncteur Dynamique (TheoryStepFunctor)

Ce document décrit uniquement l'endofoncteur dynamique `TheoryStepFunctor` défini dans `RevHalt.Theory.TheoryDynamics` (pas d'arguments ω/transfinis, pas de croissance stricte, pas de théorèmes annexes).

## Schéma (vue d'ensemble)

```mermaid
graph TD
    %% CONTEXTE MINIMAL
    subgraph Axioms [Axiomes Requis (Minimal)]
        A1[CnIdem : pour tout X, Cn (Cn X) = Cn X]
        A2[ProvClosedCn : pour tout Γ, ProvClosed (Cn Γ)]
        A3[CnMonotone : Γ inclus Δ => Cn Γ inclus Cn Δ]
    end

    %% FLUX DU FONCTEUR
    subgraph Functor [TheoryStepFunctor : ThState -> ThState]
        
        %% ETAT A
        subgraph StateA [Objet A : ThState]
            GammaA[Corpus GammaA]
            InvA1[Invariant: Cn(GammaA)=GammaA]
            InvA2[Invariant: ProvClosed(GammaA)]
        end

        %% MECANIQUE DE TRANSFORMATION
        GammaA -->|Calcul de S1Rel(GammaA)| S1A[Frontière S1Rel(GammaA)]
        GammaA -->|Union| Base[Base: GammaA U S1Rel(GammaA)]
        S1A -->|Union| Base
        Base -->|Clôture Cn| GammaB[Corpus GammaB = Cn(Base)]
        
        %% INFLUENCE DES AXIOMES
        A1 -.-> GammaB
        A1 -.-> InvB1
        A2 -.-> InvB2
    
        %% ETAT B (SORTIE)
        subgraph StateB [Objet F(A) : ThState]
            GammaB
            InvB1[Invariant: Cn(GammaB)=GammaB]
            InvB2[Invariant: ProvClosed(GammaB)]
        end
    end

    %% LOGIQUE DE FONCTORIALITE (PREUVE)
    subgraph Monotonicity [Action sur morphismes (idée)]
        direction TB
        Hyp[Hyp: A.Γ inclus B.Γ]
        Case1[Cas 1: p reste non prouvable dans B -> p dans S1Rel(B.Γ)]
        Case2[Cas 2: p devient prouvable dans B -> p dans B.Γ via ProvClosed(B.Γ)]
        Concl[Donc: F(A.Γ) inclus F(B.Γ)]
        
        Hyp --> Case1
        Hyp --> Case2
        Case1 --> Concl
        Case2 --> Concl
    end

    StateA -.-> Monotonicity
    StateB -.-> Monotonicity
```

## Spécification (définitions exactes)

### 1. Données
*   `PropT : Type`
*   `Provable : Set PropT → PropT → Prop`
*   `Cn : Set PropT → Set PropT`
*   `Code : Type`, `Machine : Code → Trace`
*   `K : RHKit`
*   `encode_halt : Code → PropT`

### 2. Axiomes minimaux (pour définir et rendre fonctoriel)
*   `CnIdem(Cn) : ∀ X, Cn (Cn X) = Cn X`
*   `ProvClosedCn(Provable,Cn) : ∀ Γ, (∀ p, Provable (Cn Γ) p → p ∈ Cn Γ)`
*   `CnMonotone(Cn) : ∀ {Γ Δ}, Γ ⊆ Δ → Cn Γ ⊆ Cn Δ`

### 3. Catégorie `ThState`
*   **Objet** : `A` est un corpus `A.Γ : Set PropT` avec deux invariants :
    *   `Cn (A.Γ) = A.Γ`
    *   `ProvClosed(A.Γ)` c.-à-d. `∀ p, Provable (A.Γ) p → p ∈ A.Γ`
*   **Morphisme** : `A ⟶ B` est l'inclusion `A.Γ ⊆ B.Γ` (catégorie mince).

### 4. Définitions dynamiques
*   `S1Rel(Γ) := { p | ∃ e, p = encode_halt e ∧ Rev0_K K (Machine e) ∧ ¬ Provable Γ (encode_halt e) }`
*   `F0(Γ) := Γ ∪ S1Rel(Γ)`
*   `F(Γ) := Cn (Γ ∪ S1Rel(Γ))`

### 5. Endofoncteur `TheoryStepFunctor`
*   **Sur objets** : `FState(A)` est l'objet de `ThState` de porteur `F(A.Γ)`.
    *   `CnIdem` fournit l'invariant `Cn(F(A.Γ)) = F(A.Γ)`.
    *   `ProvClosedCn` fournit l'invariant `ProvClosed(F(A.Γ))`.
*   **Sur morphismes** : si `A ⟶ B` (donc `A.Γ ⊆ B.Γ`), alors `FState(A) ⟶ FState(B)` (donc `F(A.Γ) ⊆ F(B.Γ)`).
    *   La preuve passe par `CnMonotone` et par le fait que `ProvClosed(B.Γ)` permet de contrôler les éléments de `S1Rel(A.Γ)` qui deviennent prouvables dans `B.Γ`.
