# Formules d’Holonomie : Cadre LLM / Grothendieck Étendu (version corrigée)

Notations minimales :

* α : p ⇒ q est une 2-cellule, avec p, q : h → k (même source h, même but k).
* Fibre(h) = micro-états compatibles avec l’observable au point h.
* Transport le long d’un chemin p :

  * en général : Tp ⊆ Fibre(h) × Fibre(k) (correspondance / relation)
  * en régime réversible : Tp : Fibre(h) → Fibre(k) (bijection)

---

## 1) Cadre général (dynamique non-inversible : relationnel / probabiliste)

**Holonomie (relation sur la fibre de départ)**
Hol(α) ⊆ Fibre(h) × Fibre(h)

**Condition d’appartenance**
(x, x') ∈ Hol(α)  ⇔  ∃ y ∈ Fibre(k) : (x, y) ∈ Tp  ET  (x', y) ∈ Tq

Lecture : “x transporté par p” et “x' transporté par q” peuvent **recoller** au même micro-état final y.

Remarque (importante) : ici Hol dépend de la 2-cellule α (donc de la paire (p,q) *et* de leur statut de ‘déformation admissible’).

---

## 2) Cadre réversible (régime étale / Grothendieck)

Hypothèse : Tp et Tq sont des **bijections** Fibre(h) → Fibre(k). Alors Tq⁻¹ existe.

**Monodromie (automorphisme de la fibre de départ)**
Mono(α) = Tq⁻¹ ∘ Tp  ∈ Aut(Fibre(h))

Lecture : “aller par p puis revenir par l’inverse de q”.

Fait utile : dans ce régime bijectif, Hol(α) devient le **graphe** de Mono(α) :

* (x, x') ∈ Hol(α) ⇔ x' = Mono(α)(x)

---

## 3) Cas “mod 3” (holonomie primitive binaire)

On suppose une observable O₃ et une sous-fibre primitive stable :

**Sous-fibre primitive**

* Prim₃(h) ⊆ Fibre₃(h)
* |Prim₃(h)| = 2
* stabilité + réversibilité sur la primitive : pour tout p : h → k,
  Tp|Prim : Prim₃(h) → Prim₃(k) est une bijection

**Monodromie primitive**
Mono₃(α) = (Tq|Prim)⁻¹ ∘ (Tp|Prim)  ∈ Aut(Prim₃(h)) ≅ ℤ/2

**Critère de flip (correction d’ordre)**
Le flip apparaît ssi la monodromie primitive est l’involution non triviale τₕ :

* Mono₃(α) = τₕ
* équivalemment : (Tq|Prim)⁻¹ ∘ (Tp|Prim) = τₕ

⚠️ Correction clé : ce n’est **pas** (Tp|Prim)⁻¹ ∘ (Tq|Prim).
La convention “verrouillée” (et cohérente) est Mono = Tq⁻¹∘Tp.

**Caractérisation par un bit**

* Flip(α) ∈ ℤ/2
* Mono₃(α) = τₕᴾᵘⁱˢˢᵃⁿᶜᵉ(Flip(α))  (donc Flip=0 → id, Flip=1 → τₕ)

---

## 4) Propriétés structurelles (2D → cocycle, repair, obstruction)

### 4.1 Additivité (pasting vertical = XOR)

Si α : p ⇒ q et β : q ⇒ r, alors :

* Mono₃(β ∘ α) = Mono₃(β) ∘ Mono₃(α)
* donc Flip(β ∘ α) = Flip(β) ⊕ Flip(α)

### 4.2 Repair (trivialisation cohomologique)

On considère le groupoïde Π(h,k) des “totals” et de leurs déformations (2-cellules inversées formellement).

Le flip définit une classe :

* [Flip] ∈ H¹(Π(h,k); ℤ/2)

**Condition exacte de réparabilité (trivialisation)**
Il existe une jauge φ sur les objets (totals) telle que pour toute 2-cellule α : p ⇒ q :

* Flip(α) = φ(p) ⊕ φ(q)

(équivalent à [Flip] = 0)

### 4.3 “Non-réduction” (formulation correcte : non-factorisation / boîte noire structurelle)

Si [Flip] ≠ 0 dans H¹(Π(h,k); ℤ/2), alors :

* il n’existe **pas** de résumé/projection 1D qui “oublie la 2D” (les déformations) et permette de reconstruire Flip ;
* autrement dit, toute projection 1D qui identifie les histories au niveau des objets (quotient observable) laisse subsister une variable 2D (Flip) non récupérable : **boîte noire structurelle à cette résolution**.
