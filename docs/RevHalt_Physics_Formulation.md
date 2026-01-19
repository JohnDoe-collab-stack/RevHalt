# Formulation Physique de RevHalt (Sans LaTeX)

Ce document propose une extension formelle de l'équivalence Masse-Énergie pour intégrer la dynamique de frontière (Route II) de RevHalt.

---

## 1. Le Principe Physique

En Physique Standard (Relativité Générale), on suppose que l'énergie est localisée dans le volume (Tenseur Energie-Impulsion).
Dans RevHalt, un système physique est défini par un couple **(Bulk, Bord)**.

L'énergie totale n'est donc pas seulement la masse au repos, mais la somme :

1. De l'énergie de masse (coût d'existence statique).
2. De l'énergie de calcul (coût de cohérence dynamique à la frontière).

---

## 2. L'Équation Généralisée

L'équation étendue s'écrit :

```
E_total  =  ( m * c^2 )  +  ( h_barre * J_flux )
```

Où :

* **m * c^2** : Est le terme d'Einstein classique. Il représente l'énergie stockée dans la structure locale (le Bulk F).
* **h_barre * J_flux** : Est le terme RevHalt (Quantique/Informationnel).
  * **J_flux** est la fréquence d'information entrant par le bord (le Jump).
  * Ce terme représente l'énergie nécessaire pour *mettre à jour* le système face à l'indécidable.

---

## 3. Interprétation des Régimes

* **Régime Classique (Système Isolé)** :
    Si **J_flux = 0** (pas d'information entrante, système fermé), alors :
    `E_total = m * c^2`
    On retrouve la physique standard.

* **Régime RevHalt (Système Ouvert / Trou Noir)** :
    Si **J_flux > 0** (le système traite de l'information à l'horizon), alors :
    `E_total > m * c^2`
    L'excès d'énergie correspond à l'entropie ou à la complexité du bord.

Cela signifie qu'un objet "complexe" (au sens de Kolmogorov ou RevHalt) pèse littéralement plus lourd qu'un objet "simple" de même constitution, car il contient de l'énergie de liaison informationnelle.

---

## 4. Lien avec la Perte de Masse

Si on dérive par rapport au temps :

```
d(E_total) / dt  =  - Puissance_Rayonnée
```

Ceci unifie la perte de masse de Bondi et le coût de calcul. Un système qui "calcule" (réduit sa complexité) doit rayonner de l'énergie.
