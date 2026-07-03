{-# OPTIONS --safe --cubical --lossy-unification #-}

module Utils.RelativeEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

private
  variable
    ℓA ℓB ℓP ℓQ : Level

haeOverInv-rinv :
  {A : Type ℓA} {B : Type ℓB}
  {P : A → Type ℓP} {Q : B → Type ℓQ}
  {f : A → B} (h : isHAEquiv f)
  {F : mapOver f P Q}
  (hₒ : isHAEquivOver (f , h) P Q F)
  (b : B) (p : P (isHAEquiv.g h b)) →
  isHAEquivOver.inv hₒ b
    (subst Q (isHAEquiv.rinv h b) (F (isHAEquiv.g h b) p))
    ≡ p
haeOverInv-rinv {P = P} {Q = Q} {f = f} h {F = F} hₒ b p =
  sym (substCommSlice Q (λ b → P (isHAEquiv.g h b))
    (λ b → isHAEquivOver.inv hₒ b)
    (isHAEquiv.rinv h b)
    (F (isHAEquiv.g h b) p))
  ∙ cong (λ l → subst P l
      (isHAEquivOver.inv hₒ (f (isHAEquiv.g h b))
        (F (isHAEquiv.g h b) p)))
      (isHAEquiv.com-op h b)
  ∙ fromPathP (isHAEquivOver.linv hₒ (isHAEquiv.g h b) p)

compPath-filler'-filler : {A : Type ℓA} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) (j i k : I) → A
compPath-filler'-filler p q j i =
  hfill (λ k → λ
    { (i = i0) → p (~ j)
    ; (i = i1) → q k
    ; (j = i0) → q (i ∧ k) })
    (inS (p (i ∨ ~ j)))

compPathP'-filler' :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y z : A} {p : x ≡ y} {q : y ≡ z}
  {x' : B x} {y' : B y} {z' : B z}
  (P : PathP (λ i → B (p i)) x' y')
  (Q : PathP (λ i → B (q i)) y' z') →
  PathP (λ j → PathP (λ i → B (compPath-filler' p q j i)) (P (~ j)) z')
    Q (compPathP' {B = B} P Q)
compPathP'-filler' {B = B} {p = p} {q = q} P Q j i =
  comp (λ k → B (compPath-filler'-filler p q j i k))
    (λ k → λ
      { (i = i0) → P (~ j)
      ; (i = i1) → Q k
      ; (j = i0) → Q (i ∧ k) })
    (P (i ∨ ~ j))

assocP' :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y z w : A} {p : x ≡ y} {q : y ≡ z} {r : z ≡ w}
  {x' : B x} {y' : B y} {z' : B z} {w' : B w}
  (P : PathP (λ i → B (p i)) x' y')
  (Q : PathP (λ i → B (q i)) y' z')
  (R : PathP (λ i → B (r i)) z' w') →
  PathP (λ k → PathP (λ i → B (assoc p q r k i)) x' w')
    (compPathP' {B = B} P (compPathP' {B = B} Q R))
    (compPathP' {B = B} (compPathP' {B = B} P Q) R)
assocP' {B = B} {p = p} {q = q} {r = r} P Q R k =
  compPathP' {B = B}
    (compPathP'-filler {B = B} P Q k)
    (compPathP'-filler' {B = B} Q R (~ k))

rCancelP' :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y : A} {p : x ≡ y}
  {x' : B x} {y' : B y}
  (P : PathP (λ i → B (p i)) x' y') →
  PathP (λ j → PathP (λ i → B (rCancel p j i)) x' x')
    (compPathP' {B = B} P (symP P)) refl
rCancelP' {B = B} {p = p} {x' = x'} P j i =
  comp (λ k → B (rCancel-filler p k j i))
    (λ k → λ
      { (i = i0) → x'
      ; (i = i1) → P (~ k ∧ ~ j)
      ; (j = i1) → x' })
    (P (i ∧ ~ j))

lCancelP' :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y : A} {p : x ≡ y}
  {x' : B x} {y' : B y}
  (P : PathP (λ i → B (p i)) x' y') →
  PathP (λ j → PathP (λ i → B (lCancel p j i)) y' y')
    (compPathP' {B = B} (symP P) P) refl
lCancelP' {B = B} {p = p} P = rCancelP' {B = B} {p = sym p} (symP P)

compPathl-cancelR : {A : Type ℓA} {x y z : A}
  (p : x ≡ y) (q : x ≡ z) → p ∙ (sym p ∙ q) ≡ q
compPathl-cancelR p q =
  assoc p (sym p) q
  ∙ cong (_∙ q) (rCancel p)
  ∙ sym (lUnit q)

compPathl-cancelL : {A : Type ℓA} {x y z : A}
  (p : x ≡ y) (q : y ≡ z) → sym p ∙ (p ∙ q) ≡ q
compPathl-cancelL p q =
  assoc (sym p) p q
  ∙ cong (_∙ q) (lCancel p)
  ∙ sym (lUnit q)

compPathP'-lCancel :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y z : A} {p : x ≡ y} {q : y ≡ z}
  {x' : B x} {y' : B y} {z' : B z}
  (P : PathP (λ i → B (p i)) x' y')
  (Q : PathP (λ i → B (q i)) y' z') →
  PathP (λ k → PathP (λ i → B (compPathl-cancelL p q k i)) y' z')
    (compPathP' {B = B} (symP P) (compPathP' {B = B} P Q))
    Q
compPathP'-lCancel {B = B} {y = y} {z = z} {p = p} {q = q} {y' = y'} {z' = z'} P Q =
  compPathP' {A = y ≡ z}
    {B = λ s → PathP (λ i → B (s i)) y' z'}
    {p = assoc (sym p) p q}
    {q = cong (_∙ q) (lCancel p) ∙ sym (lUnit q)}
    (assocP' {B = B} (symP P) P Q)
    (compPathP' {A = y ≡ z}
      {B = λ s → PathP (λ i → B (s i)) y' z'}
      {p = cong (_∙ q) (lCancel p)}
      {q = sym (lUnit q)}
      (λ j → compPathP' {B = B} {p = lCancel p j} {q = q}
        (lCancelP' {B = B} {p = p} P j) Q)
      (symP (lUnitP' B Q)))

compPathP'-rCancel :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y z : A} {p : x ≡ y} {q : x ≡ z}
  {x' : B x} {y' : B y} {z' : B z}
  (P : PathP (λ i → B (p i)) x' y')
  (Q : PathP (λ i → B (q i)) x' z') →
  PathP (λ k → PathP (λ i → B (compPathl-cancelR p q k i)) x' z')
    (compPathP' {B = B} P (compPathP' {B = B} (symP P) Q))
    Q
compPathP'-rCancel {B = B} {x = x} {z = z} {p = p} {q = q} {x' = x'} {z' = z'} P Q =
  compPathP' {A = x ≡ z}
    {B = λ s → PathP (λ i → B (s i)) x' z'}
    {p = assoc p (sym p) q}
    {q = cong (_∙ q) (rCancel p) ∙ sym (lUnit q)}
    (assocP' {B = B} P (symP P) Q)
    (compPathP' {A = x ≡ z}
      {B = λ s → PathP (λ i → B (s i)) x' z'}
      {p = cong (_∙ q) (rCancel p)}
      {q = sym (lUnit q)}
      (λ j → compPathP' {B = B} {p = rCancel p j} {q = q}
        (rCancelP' {B = B} {p = p} P j) Q)
      (symP (lUnitP' B Q)))

compPathlIso : {A : Type ℓA} {x y z : A}
  (p : x ≡ y) → Iso (y ≡ z) (x ≡ z)
compPathlIso p .Iso.fun = p ∙_
compPathlIso p .Iso.inv = sym p ∙_
compPathlIso p .Iso.rightInv = compPathl-cancelR p
compPathlIso p .Iso.leftInv = compPathl-cancelL p

compPathPIsoOver :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y z : A} {p : x ≡ y}
  {x' : B x} {y' : B y} {z' : B z}
  (P : PathP (λ i → B (p i)) x' y') →
  IsoOver (compPathlIso {z = z} p)
    (λ q → PathP (λ i → B (q i)) y' z')
    (λ q → PathP (λ i → B (q i)) x' z')
compPathPIsoOver {B = B} P .IsoOver.fun q Q =
  compPathP' {B = B} P Q
compPathPIsoOver {B = B} P .IsoOver.inv q Q =
  compPathP' {B = B} (symP P) Q
compPathPIsoOver P .IsoOver.rightInv q Q =
  compPathP'-rCancel P Q
compPathPIsoOver P .IsoOver.leftInv q Q =
  compPathP'-lCancel P Q

compPathlHAEquiv : {A : Type ℓA} {x y z : A}
  (p : x ≡ y) → HAEquiv (y ≡ z) (x ≡ z)
compPathlHAEquiv p = iso→HAEquiv (compPathlIso p)

compPathPHAEquivOver :
  {A : Type ℓA} {B : A → Type ℓB}
  {x y z : A} {p : x ≡ y}
  {x' : B x} {y' : B y} {z' : B z}
  (P : PathP (λ i → B (p i)) x' y') →
  isHAEquivOver (compPathlHAEquiv {z = z} p)
    (λ q → PathP (λ i → B (q i)) y' z')
    (λ q → PathP (λ i → B (q i)) x' z')
    (λ _ → compPathP' {B = B} P)
compPathPHAEquivOver P = IsoOver→HAEquivOver (compPathPIsoOver P)
