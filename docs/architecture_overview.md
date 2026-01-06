# Architecture Complète de RevHalt

Ce document détaille l'architecture "Full Stack" du projet RevHalt. Au-delà de la méthode de preuve par Splitters, RevHalt constitue une **théorie unifiée de l'information computationnelle**, allant de l'arithmétique pure jusqu'à la méta-logique.

Le projet est structuré en quatre strates fondamentales.

---

## 1. Le Substrat Arithmétique (`RevHalt/Theory/Arithmetization`)

C'est la fondation "low-level". RevHalt ne s'appuie pas sur une machine virtuelle abstraite ou externe, mais reconstruit la notion de calcul directement dans la logique du premier ordre.

*   **`EvalnGraph0.lean`** : Implémentation certifiée du graphe de la fonction `evaln` (step-indexing).
    *   *Innovation* : Utilise une arithmétisation pure (sans axiomes) via la fonction beta de Gödel.
    *   *Rôle* : Permet au système de raisonner sur sa propre exécution.
*   **`GodelBeta0.lean`** : Encodage des séquences finies.

C'est ce qui garantit que tout résultat de non-arrêt est une vérité arithmétique standard, et non un artefact d'un modèle de calcul exotique.

---

## 2. Les Fondations Abstraites (`RevHalt/Base`)

Cette couche définit les concepts primaires de "Trace" et d' "Observation" sans les lier à une dynamique particulière.

*   **`Trace.lean`** : Définit ce qu'est un comportement (`ℕ → Prop`) et l'opérateur fondamental `up` (clôture monotone).
*   **`Kit.lean`** : Définit le concept de **Kit** (`RHKit`), une structure abstraite capable de détecter la monotonie (`DetectsMonotone`).
    *   *Concept* : Un Kit est un "observateur" qui peut avoir une logique interne complexe, tant qu'il "voit" correctement les processus qui montent (monotones).

---

## 3. La Stabilisation Algébrique (`RevHalt/Theory/Categorical.lean`)

Ici, la théorie de l'arrêt rejoint l'algèbre et la topologie.

*   **L'Opérateur `up`** : Ce n'est pas juste un utilitaire. C'est un **opérateur de fermeture** (Closure Operator) au sens catégorique.
*   **Stabilisation par le Noyau** :
    *   Classiquement : `Stabilizes T := ∀ n, ¬ T n`.
    *   RevHalt (Algébrique) : `T ∈ Kernel(up) ⟺ up T = ⊥`.
    La stabilisation est vue comme une **nullité structurelle** détectée par l'opérateur.

Cette couche prouve que l'espace des traces a une structure de catégorie (fine), et que la stabilisation est une propriété topologique du système.

---

## 4. La Méta-Théorie et Complémentarité (`RevHalt/Theory/Complementarity.lean`)

C'est le sommet de l'édifice théorique. Cette couche utilise tout ce qui précède pour démontrer des propriétés sur les limites de la preuve elle-même.

*   **Théorème T3 (Complémentarité)** :
    > S3 = S2 ∪ S1
    
    Il formalise la décomposition de la vérité en deux parts :
    *   **S2** : Le corps de base (ce qui est prouvable classiquement).
    *   **S1 (La Frontière)** : L'ensemble des énoncés vrais mais non-prouvables dans S2, qui sont capturés par les certificats du Kit (Splitters).

Ce théorème montre que la méthode des Splitters est **nécessaire** : elle permet d'atteindre la partie S1 que la preuve standard (S2) ne peut pas toucher.

---

## Résumé du Flux Logique

1.  Le système est encodé arithmétiquement (**Niveau 1**).
2.  Son comportement est vu comme une Trace dans un treillis complet (**Niveau 2**).
3.  L'arrêt ou le non-arrêt est décidé par le noyau d'un opérateur de fermeture `up` (**Niveau 3**).
4.  Les cas difficiles (indécidables) sont résolus en étendant le système avec des certificats d'observation finis (S1) (**Niveau 4**).
