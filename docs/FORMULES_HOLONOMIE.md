# Formules d’Holonomie — Cadre Histoires/Observables (fondationnel)

## 1) Primitives : 2-géométrie des histoires (pas de temps externe)

On se donne une 2-structure d’histoires 𝓗₂ :

* Objets : préfixes d’histoires h, k, …
* 1-flèches : chemins (totals/schedulings) p : h → k
* 2-cellules : déformations/commutations admissibles α : p ⇒ q entre chemins parallèles p, q : h → k

> Le “temps/ordinal” n’est pas une donnée : c’est un invariant dérivé des linéarisations cofinales de cette géométrie (shadow).

---

## 2) Sémantique + observable : ce qui est vu / ce qui est caché

* Sémantique (exécution) : S : 𝓗₂ → 𝓧
* Observable (résolution) : O : 𝓧 → V
* Observation induite sur les histoires : F := O ∘ S : 𝓗₂ → V

### Fibre d’ambiguïté (partie cachée relative à O)

Pour un objet h, définis :

* v_h := F(h)
* Fibre(h) := { x ∈ Obj(𝓧) | O(x) = v_h }

> Fibre(h) = “tout ce que l’observable O ne distingue pas” au niveau de h.

---

## 3) Transport (général : non-inversible / relationnel)

Pour chaque chemin p : h → k, le transport sur la partie cachée est **une correspondance** :

* T_p ⊆ Fibre(h) × Fibre(k)

Lecture : (x, y) ∈ T_p signifie “en suivant p depuis le micro-état x (compatible avec O au départ), on peut atteindre le micro-état y (compatible avec O à l’arrivée)”.

Compatibilité minimale (composition relationnelle) :

* T_id = Id
* T_{p ∘ r} = T_p ∘ T_r  (composition de relations)

> Ici, on ne suppose ni déterminisme, ni bijectivité, ni existence d’un inverse.

---

## 4) Définition fondamentale : holonomie relative à l’observable

Soit une 2-cellule α : p ⇒ q avec p, q : h → k.

### Holonomie (relation sur la fibre de départ)

On définit :

* Hol_O(α) ⊆ Fibre(h) × Fibre(h)

par la condition d’appartenance :

* (x, x′) ∈ Hol_O(α)  ⇔  ∃ y ∈ Fibre(k) tel que (x, y) ∈ T_p et (x′, y) ∈ T_q

Lecture : “p depuis x et q depuis x′ peuvent recoller au même micro-état final y”, même si O ne distingue pas p et q.

> C’est **ça** l’holonomie : la dépendance au chemin de la partie cachée, attachée aux 2-cellules, sans aucune hypothèse d’inversibilité.

---

## 5) Trivialité / torsion (définition interne)

Pour une 2-cellule α : p ⇒ q :

* Holonomie faible : Δ ⊆ Hol_O(α)
  (tout x peut se recoller à lui-même : pas forcément unique)
* Holonomie strictement triviale : Hol_O(α) = Δ
  (recollage sans twist : si ça recolle, c’est avec le même x)
* Holonomie tordue : ∃ x ≠ x′ avec (x, x′) ∈ Hol_O(α)
  (le chemin “ne change rien observablement”, mais tord l’invisible)

où Δ = { (x, x) | x ∈ Fibre(h) }.

---

## 6) Où le “quotient” intervient (après coup, et seulement sur les objets)

Le quotient canonique relatif à O (sur les objets/préfixes) identifie les histoires indiscernables **au niveau observable** :

* h ~_O h′  ⇔  F(h) = F(h′)   (ou famille d’observables)

Cela produit un quotient sur objets (1D) qui capture “ce que O voit”.

Mais l’holonomie Hol_O vit au niveau **2D (chemins/2-cellules)** et mesure précisément ce que ce quotient **ne capture pas** : l’action du scheduling sur l’invisible.

---

## 7) Cas spécial dérivé : quand une “monodromie” existe (optionnel)

Ce n’est **pas** la base. C’est un **cas particulier** où l’holonomie se rigidifie en fonction.

### 7.1. Cas fonctionnel (déterministe sur fibres)

Si chaque T_p est une fonction Fibre(h) → Fibre(k), alors :

* (x, x′) ∈ Hol_O(α)  ⇔  T_p(x) = T_q(x′)

### 7.2. Cas bijectif (réversible sur une fibre stable)

Si, sur une sous-fibre stable F₀(h) ⊆ Fibre(h), les T_p sont bijectifs, alors on peut définir :

* Mono_O(α) := (T_q|*{F₀})⁻¹ ∘ (T_p|*{F₀})  ∈ Aut(F₀(h))

et Hol_O(α) restreinte à F₀(h) devient le **graphe** de Mono_O(α).

> Important : ceci est un **raffinement** quand les hypothèses le permettent, pas une définition générale.

---

## 8) Auto-régulation (version générale, sans exiger l’inversibilité de la dynamique)

L’auto-régulation porte sur les **déformations admissibles** (les 2-cellules) et l’holonomie qu’elles induisent sur l’invisible.

* Fixe h, k.
  Définis Def(h, k) : objets = chemins p : h → k ; morphismes = 2-cellules α : p ⇒ q.

### Principe (canonisation interne)

Le système est “auto-régulé” (à résolution O, sur le domaine considéré) s’il existe une **jauge** qui rend plates les déformations, c.-à-d. qui transforme les transports (ou la représentation induite quand elle existe) de sorte que, pour toute 2-cellule α : p ⇒ q, l’holonomie devienne strictement diagonale sur la partie pertinente.

* En régime bijectif (quand une représentation ρ existe), cela se formule classiquement comme “ρ est un cobord”.
* En régime purement relationnel, la formulation correcte reste : “il existe une reparamétrisation interne qui diagonalise Hol_O(α) (sur la fibre pertinente) pour toutes les 2-cellules admissibles”.

> Donc : l’inversibilité n’est pas requise pour **définir** Hol_O ; elle n’est requise que si tu veux remplacer l’holonomie-relation par une **action** (automorphismes) et parler de classes H¹ au sens groupoïde.

---

### Résumé (une ligne)

**Holonomie relative à O** = relation Hol_O(α) sur Fibre(h) définie par “recollage au même y” le long de deux chemins p, q reliés par une 2-cellule α : p ⇒ q ; tout le reste (monodromie, H¹, etc.) est **dérivé** quand des hypothèses supplémentaires le justifient.
