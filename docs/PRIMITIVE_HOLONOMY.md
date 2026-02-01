# Holonomie Primitive : la 2-géométrie avant le quotient (version verrouillée, corrigée)

## 0) Convention de calcul (pour lever toute ambiguïté)

**Converse (relation réciproque).**
Pour une relation R ⊆ A×B :

* R† ⊆ B×A
* (b, a) ∈ R† ⇔ (a, b) ∈ R

**Composition relationnelle (sens fixé, gauche→droite).**
Pour R ⊆ A×B et S ⊆ B×C :

* R ○ S ⊆ A×C
* (a, c) ∈ R ○ S ⇔ ∃b ∈ B : (a, b) ∈ R et (b, c) ∈ S

**Diagonale.**
Δ_A := {(a, a) | a ∈ A} ⊆ A×A

> Avec ces conventions, “Hol = Tₚ ○ (T_q)†” correspond exactement à la condition ∃y.

---

## 1) Primitive : la 2-catégorie des histoires H₂

On définit une 2-catégorie **H₂** (supposée **stricte** pour simplifier l'exposition, ou bicatégorie sinon) :

* **Objets** : préfixes d’histoires h.
* **1-flèches** (p : h → k) : totals/schedulings (chemins).
* **2-cellules** (α : p ⇒ q) : moves de commutation admissibles (déformations 2D **prises comme primitives**).

> Ici, **le temps ordinal n’existe pas** : une “timeline” est un **choix** de 1-flèche (éventuellement cofinale pour parler d’“avenir effectif”).

---

## 1bis) Cofinalité et “shadow” du temps (définitions minimales)

On note Reach(h, k) la relation “k est atteignable depuis h” :

* Reach(h, k) ⇔ il existe au moins un total p : h → k.

Un “futur pertinent” est modélisé par un sous-ensemble C ⊆ Obj(H₂) tel que :

* Cofinal(C) ⇔ pour tout préfixe h, il existe k ∈ C avec Reach(h, k).

Intuition : C capture “l’avenir effectif” (ou la zone d’exécution qui finit par être atteinte).

**Shadow du temps.**
Une “timeline” n’est pas primitive ; c’est un choix de linéarisation, c’est-à-dire une suite (ou chaîne) de préfixes qui est cofinale :

* une chaîne cofinale est une sélection h₀, h₁, h₂, … telle que :

  * Reach(hᵢ, hᵢ₊₁) pour tout i,
  * et pour tout h, il existe i tel que Reach(h, hᵢ).

Donc l’ordinal/temps est un invariant dérivé : le “shadow” d’un choix de chaîne cofinale dans la géométrie interne des histoires.

---

## 2) Sémantique non-inversible : codomaine relationnel (sans forcer la neutralité des 2-cellules)

On fixe un ensemble X de **micro-états**.

**Relₓ (catégorie à un seul objet).**
Relₓ est la catégorie à un seul objet X, dont les endomorphismes sont les relations R ⊆ X×X, avec composition ○ et unité Δ_X.

**Donnée sémantique minimale (conforme à ta nouveauté).**
Une sémantique est un foncteur sur le **1-squelette** :

> **S₁ : (H₂)₁ → Relₓ** respecte l’identité et la composition des 1-flèches (au sens strict sur le 1-squelette).

* à chaque objet h, on associe (implicitement) “être à h” comme contexte d’exécution,
* à chaque total p : h→k, S₁(p) ⊆ X×X est une relation de transition.

**Point crucial (correction).**
On ne demande pas que S envoie α : p⇒q sur quoi que ce soit : α sert d’index 2D de comparaison, pas de neutralisation sémantique.
Sinon tu détruis précisément le cas central : **α existe comme move admissible, mais Tₚ et T_q peuvent tordre différemment la fibre**.

> Les 2-cellules α sont donc primitives dans H₂ et servent d’**index de comparaison** (elles désignent quelles paires de totals on compare). Elles ne sont pas “déjà neutralisées” par la sémantique.

---

## 3) Observable et fibres (ce que le quotient ne voit pas)

Fixe une observable (résolution) :

> O : X → V

Pour chaque préfixe h, on suppose donnée :

> **vₕ ∈ V**, la valeur visible fixée au préfixe h (donnée par l’exécution observée).
>
> vₕ est une donnée observable de l’exécution (trace/résolution), pas un index temporel.

**Fibre d’ambiguïté au-dessus de h (relatif à O) :**

> F(h) := { x ∈ X | O(x) = vₕ }
> Important : **O** définit les fibres, mais **le temps n’apparaît nulle part** et on n'exige aucune "naturalité" d'un état interne σ(h).

---

## 4) Transport sur fibres (toujours relationnel)

Pour un total p : h → k :

> Tₚ := S₁(p) ∩ (F(h)×F(k))  ⊆  F(h)×F(k)

---

## 5) Définition canonique de l’holonomie (primitive, avant quotient)

Pour une 2-cellule α : p ⇒ q (p, q : h → k), l’holonomie relative à O est :

> Hol_O(α) ⊆ F(h)×F(h)

définie par :

> (x, x′) ∈ Hol_O(α) ⇔ ∃y ∈ F(k) : (x, y) ∈ Tₚ et (x′, y) ∈ T_q

Forme “calcul relationnel” (sans inversibilité) :

> Hol_O(α) = Tₚ ○ (T_q)†
> C’est bien **holonomie primitive**, avant quotient, avant groupoïdification, et sans hypothèse d’inverse.

### Trois régimes (toujours 100% relationnel)

* **Holonomie faible** : Δ_F(h) ⊆ Hol_O(α)
* **Holonomie plate (forte)** : Hol_O(α) = Δ_F(h)
* **Holonomie tordue** : ∃x≠x′ avec (x, x′) ∈ Hol_O(α)

---

## 6) “Lag” (répercussion différée) : codage propre

Si X = Y×B et O(y, b) = y, alors :

* p et q peuvent être indiscernables sur Y (donc “quotientables” côté visible),
* mais Hol_O(α) peut être tordue sur B,
* et **le lag** = “twist maintenant sur B, observable plus tard” dès que l’étape suivante dépend de b.

---

## 7) Auto-régulation cofinale (sans inversibilité)

Fixe un futur cofinal pertinent J, et ne regarde que les 2-cellules α qui vivent dans J.

**Jauge (repair) relationnelle** : à chaque total p : h→k, on associe :

> φ(p) ⊆ F(k)×F(k)

Transport corrigé (post-composition sur la fibre d’arrivée) :

> Tₚ^♯ := Tₚ ○ φ(p)

Holonomie corrigée :

> Hol_O^♯(α) := Tₚ^♯ ○ (T_q^♯)†

**Auto-régulation (plateur cofinale) sur J** ssi :

> ∃φ tel que ∀α : p⇒q dans J,  Hol_O^♯(α) = Δ_F(h)

Sinon **obstruction structurelle cofinale** :

> ∀φ, ∃α dans J tel que Hol_O^♯(α) ≠ Δ_F(h)

---

## 8) Shot 1D et non-réduction (définition + témoin)

On appelle **shot 1D** (ou “résumé 1D”) toute application q qui compresse un total en un code :

* q : {totals p : h → k} → Q

où Q est un ensemble de codes (une “valeur 1D” attachée au chemin).

On dit que **l’holonomie factorise par un shot 1D** s’il existe une règle H telle que, pour toute 2-cellule α : p ⇒ q (avec p, q : h → k) :

* Hol_O(α) dépend seulement du couple ( q(p), q(q) ).

Formellement :

* il existe H : Q×Q → Rel(F(h)) tel que, pour toute α : p ⇒ q,

  * Hol_O(α) = H( q(p), q(q) ).

**Témoin de non-réduction (critère minimal).**
Si l’on peut exhiber deux 2-cellules α₁ : p₁ ⇒ q₁ et α₂ : p₂ ⇒ q₂ telles que :

* q(p₁) = q(p₂) et q(q₁) = q(q₂),
* mais Hol_O(α₁) ≠ Hol_O(α₂),

alors **aucune** factorisation de Hol_O par ce shot q n’est possible.

Interprétation : toute compression 1D qui “oublie” le 2D peut identifier des chemins qui ont pourtant des holonomies différentes ; l’holonomie est donc une donnée intrinsèquement 2D, non récupérable depuis un code 1D en général.

---

## Mini-résumé (une ligne)

**Holonomie primitive = Tₚ ○ (T_q)† sur les fibres définies par O, dans H₂ (2D) avant toute linéarisation/quotient ; auto-régulation = trivialisation cofinale par une jauge relationnelle.**
