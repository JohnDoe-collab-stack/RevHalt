# Fixpoint fort (cadre RevHalt)

1. **Politique de limite**
   `L : LimitOp PropT` est une donnée primitive (`LimitOp.apply`).

2. **Candidat-limite canonique**
   Pour `F : Set PropT → Set PropT`, `A0 : Set PropT`, `lim : Ordinal`, on définit :

* `Γ_lim := transIterL L F A0 lim`.
  Ce `Γ_lim` est **le seul objet** auquel on attache le “fixpoint” au sens fort.

1. **Fixpoint (sens fort)**
   Le fixpoint est l’égalité **sur ce candidat** :

* `Fix(L,F,A0,lim) := (F Γ_lim = Γ_lim)`.

1. **Compatibilité limite/itération (continuité au rang limite)**
   `ContinuousAtL (L := L) F A0 lim` est la propriété :

* `F (transIterL L F A0 lim) = L.apply (alpha := lim) (fun β (_:β<lim) => F (transIterL L F A0 β))`.

1. **Règle “continuité ⇒ fixpoint” (pas implicite)**
   `FixpointFromContinuity (L := L) F A0 lim` est **le contrat explicite** :

* `ContinuousAtL … → F Γ_lim = Γ_lim`.

1. **Union/transfini = cas particulier de politique**

* `unionLimitOp` donne `transIter := transIterL unionLimitOp`.
* `cnUnionLimitOp Cn` donne la limite `Cn (union)` au rang limite.
* `jumpLimitOp Cn J` donne la limite `Cn (preLimit ∪ J preLimit)`.

1. **Ce que l’escape démontre (noyau)**
   Vous avez un théorème général :

* `structural_escape_transfinite_L` : à partir d’hypothèses dynamiques locales au rang `lim` (absorption sous `lim`, RouteII à `lim`, inclusion des stades, fixpoint à `lim`, ProvClosed à `lim`) on obtient `False`.

1. **Conséquence “pas de continuité” (Fork Law)**
   En ajoutant uniquement `FixpointFromContinuity`, vous obtenez :

* `structural_escape_at_limit_L` :
  `¬ ContinuousAtL (L := L) (F …) A0.Γ lim`.

1. **Version “jump” prête à l’emploi**
   Pour `L := jumpLimitOp Cn J` :

* `jump_fixpoint_from_continuity` fournit `FixpointFromContinuity` (si `hExt`).
* `part7_change_of_sense_jump` conclut directement `¬ ContinuousAtL …` sous les hypothèses d’escape.

1. **Donc, précisément**
    Le “fixpoint fort” n’est **ni** `∃ Γ, F Γ = Γ` **ni** un slogan :
    c’est `F (transIterL L F A0 lim) = transIterL L F A0 lim`, et votre cadre prouve que, sous les hypothèses dynamiques d’escape, **toute notion de continuité qui implique ce fixpoint au candidat-limite est impossible** (`¬ ContinuousAtL`).
