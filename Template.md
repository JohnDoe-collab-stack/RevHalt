## Template abstrait réutilisable (sans LaTeX) — avec version two-sided

### 0) Données

On fixe :

* A : objets “bruts”
* B ⊆ A : objets “bien formés”
* c : A → B : opérateur de clôture (projection vers B)
* E : A → Prop : propriété fondamentale
* K : B → Prop : observateur (ou “kit”)

---

## I) Clôture ⇒ rigidité (canonicité forcée)

### I.1 Clôture

On suppose que c est une clôture :

* Extensif : pour tout a, a ≤ c(a)
* Monotone : si a ≤ a' alors c(a) ≤ c(a')
* Idempotent : c(c(a)) = c(a)

### I.2 Détection sur les objets clos

K est correct sur B :

* Pour tout b dans B : K(b) ↔ E(b)

### I.3 Stabilité de E par clôture

* Pour tout a dans A : E(c(a)) ↔ E(a)

### I.4 Définition canonisée

* Rev(a) := K(c(a))

### I.5 Théorème de rigidité

* Pour tout a : Rev(a) ↔ E(a)

Lecture : K ne peut plus porter une “puissance” après canonisation, car on ne l’évalue que sur c(a) ∈ B.

---

## II) Barrière de globalisation (diagonalisation)

On fixe :

* Code : espace de codes/programmes
* E0(e) : propriété existentielle dure (ex. “e converge”)

On suppose qu’un système interne S tente une internalisation uniforme via H(e) :

* Total : S prouve H(e) ou S prouve Not(H(e))
* Correct : E0(e) ⇒ S prouve H(e)
* Complet : non E0(e) ⇒ S prouve Not(H(e))
* * condition r.e. minimale pour diagonaliser

Point fixe → e tel que :

* E0(e) ↔ S prouve Not(H(e))

Puis contradiction (cas sur la totalité). Donc pas de H uniforme.

---

## III) Quantifier swap : extensions sonores instance par instance

### III.1 Données

* PropT : univers de phrases
* Truth(p) : vérité externe
* S2 ⊆ PropT : corpus de base sound : p ∈ S2 ⇒ Truth(p)
* Pour chaque instance e, on dispose d’un certificat externe

Il y a deux variantes : one-sided et two-sided.

---

## III.A) Variante one-sided (frontière positive)

### III.A.1 Frontière

On ne s’autorise qu’à ajouter des “positifs” :

* encode_pos(e) : phrase “e est du bon côté” (ex. “halt(e)”)
* S1 := { encode_pos(e) | CertifiePos(e) et non Provable(encode_pos(e)) }

### III.A.2 Extension

* S3 := S2 ∪ S1

### III.A.3 Sonorité

On suppose un lien de correction externe :

* CertifiePos(e) ⇒ Truth(encode_pos(e))

Alors :

* p ∈ S3 ⇒ Truth(p)

Lecture : on obtient une couche de vérités “certifiées” qui ne sont pas internalisées.

Limite : on ne décide pas les négatifs, on ajoute une frontière positive.

---

## III.B) Variante two-sided (oracle local, décision “au cas par cas”)

C’est la version “complète” : pour chaque e, on choisit soit le positif soit le négatif, sans décidabilité préalable.

### III.B.1 Deux encodages

* encode_pos(e) : phrase positive (ex. “halt(e)”)
* encode_neg(e) : phrase négative (ex. “not_halt(e)”)

### III.B.2 Certificat two-sided (oracle pick)

Pour un e donné, un témoin externe fournit un couple (p, cert) tel que :

* soit (CertifiePos(e) et p = encode_pos(e))
* soit (CertifieNeg(e) et p = encode_neg(e))

Important : on ne calcule pas la branche ; le témoin porte la branche.

### III.B.3 Hypothèses de correction externe

* CertifiePos(e) ⇒ Truth(encode_pos(e))
* CertifieNeg(e) ⇒ Truth(encode_neg(e))

### III.B.4 Extension locale (une étape)

* S_e := S2 ∪ {p}

### III.B.5 Sonorité et décision locale

* p ∈ S_e
* pour tout q ∈ S_e : Truth(q)
* et p “décide e” au sens corpus : p est exactement l’une des deux phrases encode_pos(e) ou encode_neg(e)

Lecture : on obtient “pour tout e, il existe une extension sound qui décide e”, sans jamais produire une règle uniforme interne.

---

## IV) Schéma d’architecture (machine / compilation / oracle)

On sépare :

* a-machine : mécanique pure (exécution)
* c-machine : compilation (Γ, φ) ↦ code
* o-bridge : oracle reliant conséquence sémantique à convergence

Principe : décidabilité uniforme de l’oracle + couverture de compilation ⇒ décidabilité de la convergence/halting, ce qui heurterait la barrière II) si on suppose une internalisation uniforme.

---

# Instanciation RevHalt (avec one-sided + two-sided)

## I) Clôture ⇒ rigidité

* A = Trace = Nat → Prop
* B = traces monotones
* c = up
* E(T) = Halts(T) = ∃ n, T n
* K = RHKit.Proj
* Rev(T) = Rev0_K K T = K.Proj (up T)

T1_traces : Rev0_K K T ↔ Halts T

---

## III.A) One-sided

* encode_pos = encode_halt
* CertifiePos(e) = Rev0_K S.K (S.Machine e)
* S1Set : { encode_halt(e) | Rev(e) et non Provable(encode_halt(e)) }
* S3Set = S2 ∪ S1Set
* Hypothèse : Rev(e) ⇒ Truth(encode_halt(e))
* Théorème : tout élément de S3Set est vrai (sound corpus)

---

## III.B) Two-sided 

* encode_pos = encode_halt
* encode_neg = encode_not_halt
* CertifiePos(e) = Rev0_K S.K (S.Machine e)
* CertifieNeg(e) = non Rev0_K S.K (S.Machine e)

OraclePick e contient :

* un p : PropT
* un certificat : soit (Rev(e) et p = encode_halt(e)) soit (non Rev(e) et p = encode_not_halt(e))

Hypothèses :

* Rev(e) ⇒ Truth(encode_halt(e))
* non Rev(e) ⇒ Truth(encode_not_halt(e))

Extension :

* S_e = S2 ∪ {pick.p}

Théorème oracle local : S_e est sound et pick.p décide localement e (au sens p = encode_halt(e) ou p = encode_not_halt(e)).
