# Holonomie Primitive : la 2-géométrie avant le quotient (version verrouillée)

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

> Avec ces conventions, “Hol = Tₚ ○ (T_q)†” correspond exactement à ta condition ∃y.

---

## 1) Primitive : la 2-catégorie des histoires H₂

On définit une bicatégorie (ou 2-catégorie faible) **H₂** :

* **Objets** : préfixes d’histoires h.
* **1-flèches** (p : h → k) : *totals/schedulings*, i.e. chemins (compositions d’événements).
* **2-cellules** (α : p ⇒ q) : *moves de commutation admissibles* (les déformations 2D que tu prends comme primitives).

> Ici, **le temps ordinal n’existe pas** : une “timeline” n’est qu’un **choix** de 1-flèche linéarisée dans H₂ (et cofinale si tu veux parler d’“avenir effectif”).

---

## 2) Sémantique non-inversible : codomaine relationnel (avec 2-cellules)

On fixe un ensemble X de **micro-états**.

On utilise la 2-structure relationnelle standard :

* Objets : ensembles (ici, on vivra “dans” X)
* 1-cellules : relations R ⊆ A×B
* 2-cellules : inclusions R ⊆ R′

Une sémantique est (au minimum) un 2-foncteur lax :

> S : H₂ → Rel

Données effectives (lecture opérationnelle) :

* à chaque objet h, S associe un “support” de micro-états possibles (dans le cas déterministe : un singleton {xₕ})
* à chaque total p : h → k, S(p) ⊆ X×X est une relation de transition
* à chaque 2-cellule α : p ⇒ q, on a typiquement une 2-information **relationnelle** (inclusion) du style S(p) ⊆ S(q) (ou l’inverse), selon ce que “commutation admissible” signifie dans ton milieu

> Point clé : rien ici ne suppose d’inversibilité. Les 2-cellules existent *avant* tout quotient : elles sont la géométrie primitive.

---

## 3) Observable et fibres (ce que le quotient ne voit pas)

Fixe une observable (résolution) :

> O : X → V

Pour chaque préfixe h, fixe une valeur visible vₕ (par ex. vₕ = O(x̄ₕ) si tu pointes une branche x̄ₕ).

**Fibre d’ambiguïté au-dessus de h (relatif à O) :**

> F(h) := { x ∈ X | O(x) = vₕ }

---

## 4) Transport sur fibres (toujours relationnel)

Pour un total p : h → k, on restreint la transition à ce que l’observable laisse indistingué :

> Tₚ := S(p) ∩ (F(h)×F(k))  ⊆  F(h)×F(k)

---

## 5) Définition canonique de l’holonomie (primitive, avant quotient)

Pour une 2-cellule α : p ⇒ q (avec p, q : h → k), l’holonomie relative à O est la relation :

> Hol_O(α) ⊆ F(h)×F(h)

définie par :

> (x, x′) ∈ Hol_O(α) ⇔ ∃y ∈ F(k) : (x, y) ∈ Tₚ et (x′, y) ∈ T_q

Forme “calcul relationnel” (sans inversibilité) :

> Hol_O(α) = Tₚ ○ (T_q)†

> C’est exactement ton point : **holonomie primitive**, avant quotient, avant groupoïdification, et sans hypothèse d’inverse.

### Trois régimes (utile, et toujours 100% relationnel)

* **Holonomie faible** : Δ_F(h) ⊆ Hol_O(α) (recollage possible “sans perdre la diagonale”)
* **Holonomie plate (forte)** : Hol_O(α) = Δ_F(h) (aucun twist résiduel)
* **Holonomie tordue** : ∃x≠x′ avec (x, x′) ∈ Hol_O(α)

---

## 6) “Lag” (répercussion différée) : codage propre

Si X = Y×B et O(y, b) = y (B caché), alors :

* deux totals peuvent être indiscernables sur Y (donc “quotientables” côté visible),
* mais Hol_O(α) peut être tordue sur la composante B,
* et **le lag** est : la torsion sur B **devient** différence visible plus tard dès qu’une étape suivante dépend de b.

(Autrement dit : le lag = “twist maintenant, observable plus tard”.)

---

## 7) Auto-régulation cofinale (formule courte, sans inversibilité)

Fixe un futur cofinal pertinent J (idéal/cofinalité interne dans ta base), et ne regarde que les 2-cellules α “qui vivent” dans ce futur.

On cherche une **jauge** (repair) qui agit *au niveau des fibres* **sans imposer d’inverses** :

* une jauge φ assigne à chaque total p : h→k une endorelation sur la fibre d’arrivée :

  > φ(p) ⊆ F(k)×F(k)

* transport corrigé (post-composition sur la fibre d’arrivée) :

  > Tₚ^♯ := Tₚ ○ φ(p)

* holonomie corrigée :

  > Hol_O^♯(α) := Tₚ^♯ ○ (T_q^♯)†

**Auto-régulation (plateur cofinale) sur J** ssi :

> ∃φ tel que ∀α : p⇒q dans J,  Hol_O^♯(α) = Δ_F(h)

Sinon : **obstruction structurelle cofinale** (ton “OU”) :

> ∀φ, ∃α dans J tel que Hol_O^♯(α) ≠ Δ_F(h)

> Ici, tout est relationnel : pas d’inversibilité, pas de monodromie-groupe exigée, pas de quotient préalable.

---

## Mini-résumé (une ligne, ultra-fidèle à ton axe)

**Holonomie primitive = “Tₚ ○ (T_q)†” sur les fibres définies par l’observable, dans H₂ (2D) avant toute linéarisation/quotient ; l’auto-régulation est la trivialisation cofinale de cette holonomie par une jauge relationnelle.**
