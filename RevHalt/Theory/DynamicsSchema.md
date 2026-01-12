# Schéma de l'Endofoncteur Dynamique (Exhaustif)

Ce document détaille l'architecture complète de l'endofoncteur `TheoryStepFunctor` défini dans `RevHalt.Theory.TheoryDynamics`. Il inclut le contexte paramétrique, les invariants d'état, la décomposition logique fine et les dépendances axiomatiques, sans utiliser de notation LaTeX.

## Diagramme Structurel Complet

```mermaid
graph TD
    %% CONTEXTE PARAMETRIQUE
    subgraph Context [Contexte & Paramètres]
        K[Kit de Détection K]
        M[Machine de Turing]
        Logic[Logique & Provabilité]
        CnOp[Opérateur de Clôture Cn]
    end

    %% FLUX PRINCIPAL
    subgraph Functor [L'Endofoncteur F : ThState -> ThState]
        
        %% ETAT INITIAL
        subgraph Input [Entrée : État Admisible A]
            Gamma[Corpus Gamma]
            InvA1[Inv: Cn(Gamma) = Gamma]
            InvA2[Inv: Provable implique Membre]
        end

        %% MECANIQUE INTERNE
        subgraph Step_F0 [Étape 1 : Expansion (F0)]
            Direction[Analyse de la Frontière]
            S1[S1: {Halt(e) | Réel ET Improuvable}]
            Union[Union: Gamma U S1]
        end

        subgraph Step_F [Étape 2 : Stabilisation (F)]
            Closure[Clôture Déductive Cn(...)]
        end

        %% ETAT FINAL
        subgraph Output [Sortie : État Admisible F(A)]
            GammaPrime[Corpus F(Gamma)]
            InvB1[Inv: Cn(FGamma) = FGamma]
            InvB2[Inv: Provable implique Membre]
        end
    end

    %% RELATIONS
    Gamma --> Direction
    K --> Direction
    M --> Direction
    Logic --> Direction
    
    Gamma --> Union
    S1 --> Union
    
    Union --> Closure
    CnOp --> Closure
    
    Closure --> GammaPrime

    %% PROPRIETES
    subgraph Properties [Propriétés Garanties]
        Monotonicity[Monotonie: A inclus B => F(A) inclus F(B)]
        Extensivity[Extensivité: Gamma inclus F(Gamma)]
        Strictness[Croissance Stricte: S1 non vide => Gamma strict. plus petit que F(Gamma)]
    end

    Input -.- Monotonicity
    Output -.- Monotonicity
```

## Description Détaillée des Composants

### 1. Le Contexte (Paramètres)

L'endofoncteur n'existe pas dans le vide. Il dépend de quatre paramètres structurels fixés :

* **Kit K** : L'oracle ou le mécanisme qui certifie la vérité de l'arrêt (`Rev0`).
* **Machine** : Le modèle de calcul (qui lie le code à l'exécution).
* **Logique (Provable)** : La relation de déductibilité interne.
* **Clôture (Cn)** : L'opérateur de conséquence logique.

### 2. L'Objet d'Entrée (ThState)

Le foncteur ne traite pas de simples ensembles, mais des objets structurés **A** qui portent deux preuves (Invariants) :

* **Déductivement Clos** : La théorie se connaît elle-même (`Cn(Gamma) = Gamma`).
* **Prov-Closed** : La théorie contient tout ce qu'elle peut prouver. Formellement : `Provable(Gamma, p) IMPLIQUE p appartient à Gamma`.

### 3. La Mécanique Interne (Décomposition F0 / F)

Le processus se déroule en deux temps distincts dans le code :

* **F0 (L'Expansion)** : C'est l'ajout de matière brute.
  * On calcule `S1(Gamma)` (les vérités de type Halt qui échappent à `Provable`).
  * On forme l'union `Gamma U S1(Gamma)`.
* **F (La Stabilisation)** : C'est la digestion logique.
  * On applique `Cn` sur l'union pour rétablir l'invariant de clôture.
  * On obtient la nouvelle théorie `F(Gamma)`.

### 4. La Sortie et les Garanties

Le résultat est un nouvel objet **F(A)** qui est automatiquement un `ThState` valide.

* L'invariant de clôture est restauré par `Cn`.
* L'invariant `ProvClosed` est garanti par l'axiome `ProvClosedCn`.

### 5. Les Propriétés Algébriques

* **Monotonie (Fonctorialité)** : Le schéma montre que le processus respecte l'ordre d'inclusion. Voir le théorème `F0_monotone_of_provClosed`.
* **Extensivité** : On ne perd jamais d'information (`Gamma est inclus dans F(Gamma)`).
* **Croissance Stricte** : Si la frontière n'est pas vide (garanti par Route II), la théorie grandit strictement.

## Dépendances Axiomatiques (Exhaustif)

La validité mathématique de la construction repose sur les hypothèses suivantes (spécifiées dans `TheoryDynamics.lean`) :

1. **CnIdem** : `Cn(Cn(Γ)) = Cn(Γ)` (Idempotence de la clôture).
2. **CnExtensive** : `Γ est inclus dans Cn(Γ)` (La clôture préserve les axiomes).
3. **CnMonotone** : `A inclus B IMPLIQUE Cn(A) inclus Cn(B)` (Monotonie de la déduction).
4. **ProvRelMonotone** : `A inclus B ET Provable(A, p) IMPLIQUE Provable(B, p)` (Monotonie de la preuve).
5. **ProvClosedCn** : `Pour tout Γ, ProvClosed(Cn(Γ))` (La clôture déductive produit des théories qui contiennent leurs propres théorèmes).

Sans ces 5 axiomes, la construction `TheoryStepFunctor` ne compile pas ou est mathématiquement invalide.
