{-

David Wärn's version of the Higher Seifert-van Kampen Theorem

-}
{-# OPTIONS --safe --cubical --lossy-unification #-}
module HSvKT-warnd where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sum hiding (elim ; map)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Utils.Coherence


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓA ℓB ℓP ℓQ : Level


module WordConstruction
  (X : Type ℓ) (Y : Type ℓ')
  (R : X → Y → Type ℓ'')
  (a₀ : X ⊎ Y)
  where

  open Sequence

  {-

  data Code : X ⊎ Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    base : Code a₀
    app : {x : X} {y : Y} (r : R x y) → Code (inl x) → Code (inr y)
    linv : {x : X} {y : Y} (r : R x y) → Code (inr y) → Code (inl x)
    rinv : {x : X} {y : Y} (r : R x y) → Code (inr y) → Code (inl x)
    leq  : {x : X} {y : Y} (r : R x y) (u : Code (inl x)) → linv r (app r u) ≡ u
    req  : {x : X} {y : Y} (r : R x y) (v : Code (inr y)) → app r (rinv r v) ≡ v

  -}


  data Word : ℕ → X ⊎ Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    shift : {n : ℕ} {a : X ⊎ Y} → Word n a → Word (suc n) a
    base  : Word 0 a₀
    app : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → Word n (inl x) → Word n (inr y)
    inv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → Word n (inr y) → Word (suc n) (inl x)
    leq : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) → inv r (app r w) ≡ shift w
    req : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) → app r (inv r w) ≡ shift w

  comm-app : {n : ℕ} {x : X} {y : Y} (r : R x y) (w : Word n (inl x)) → shift (app r w) ≡ app r (shift w)
  comm-app r w = (λ i → req r (app r w) (~ i)) ∙ (λ i → app r (leq r w i))

  comm-inv : {n : ℕ} {x : X} {y : Y} (r : R x y) (w : Word n (inr y)) → shift (inv r w) ≡ inv r (shift w)
  comm-inv r w = (λ i → leq r (inv r w) (~ i)) ∙ (λ i → inv r (req r w i))

  homNatComp : {A : Type ℓA} {B : Type ℓB} {F G : A → B}
    (H : (a : A) → F a ≡ G a) {x y : A} (p : x ≡ y) →
      cong F p ∙ H y ≡ H x ∙ cong G p
  homNatComp H p = Square→compPath (λ i j → H (p i) j)

  doubleCancel : {A : Type ℓA} {a b c d : A}
    (p : a ≡ b) (q : b ≡ c) (r : a ≡ d) →
      (p ∙ q) ∙ (sym q ∙ (sym p ∙ r)) ≡ r
  doubleCancel p q r =
    (p ∙ q) ∙ (sym q ∙ (sym p ∙ r))
      ≡⟨ sym (assoc p q (sym q ∙ (sym p ∙ r))) ⟩
    p ∙ (q ∙ (sym q ∙ (sym p ∙ r)))
      ≡⟨ cong (p ∙_) (assoc q (sym q) (sym p ∙ r)) ⟩
    p ∙ ((q ∙ sym q) ∙ (sym p ∙ r))
      ≡⟨ cong (λ s → p ∙ (s ∙ (sym p ∙ r))) (rCancel q) ⟩
    p ∙ (refl ∙ (sym p ∙ r))
      ≡⟨ cong (p ∙_) (sym (lUnit (sym p ∙ r))) ⟩
    p ∙ (sym p ∙ r)
      ≡⟨ assoc p (sym p) r ⟩
    (p ∙ sym p) ∙ r
      ≡⟨ cong (_∙ r) (rCancel p) ⟩
    refl ∙ r
      ≡⟨ sym (lUnit r) ⟩
    r ∎

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

  comm-leq  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) →
        Square
          (comm-inv r (app r w) ∙ (λ i → inv r (comm-app r w i))) (refl)
          (cong shift (leq r w)) (leq r (shift w))
  comm-leq r w = compPath→Square (
    sym (rUnit (cong shift (leq r w))) ∙ sym lemma)
    where
    lemma :
      (comm-inv r (app r w) ∙ (λ i → inv r (comm-app r w i))) ∙ leq r (shift w)
        ≡ cong shift (leq r w)
    lemma =
      (comm-inv r (app r w) ∙ (λ i → inv r (comm-app r w i))) ∙ leq r (shift w)
        ≡⟨ sym (assoc (comm-inv r (app r w)) (λ i → inv r (comm-app r w i)) (leq r (shift w))) ⟩
      comm-inv r (app r w) ∙ ((λ i → inv r (comm-app r w i)) ∙ leq r (shift w))
        ≡⟨ cong (λ q → comm-inv r (app r w) ∙ (q ∙ leq r (shift w)))
             (congFunct (inv r) (sym (req r (app r w))) (λ i → app r (leq r w i))) ⟩
      comm-inv r (app r w) ∙
        (((λ i → inv r (req r (app r w) (~ i))) ∙
          (λ i → inv r (app r (leq r w i)))) ∙
          leq r (shift w))
        ≡⟨ cong (comm-inv r (app r w) ∙_)
             (sym (assoc (λ i → inv r (req r (app r w) (~ i)))
                         (λ i → inv r (app r (leq r w i)))
                         (leq r (shift w)))) ⟩
      comm-inv r (app r w) ∙
        ((λ i → inv r (req r (app r w) (~ i))) ∙
          ((λ i → inv r (app r (leq r w i))) ∙
            leq r (shift w)))
        ≡⟨ cong (λ q → comm-inv r (app r w) ∙
                    ((λ i → inv r (req r (app r w) (~ i))) ∙ q))
             (homNatComp (λ z → leq r z) (leq r w)) ⟩
      comm-inv r (app r w) ∙
        ((λ i → inv r (req r (app r w) (~ i))) ∙
          (leq r (inv r (app r w)) ∙ cong shift (leq r w)))
        ≡⟨ doubleCancel (sym (leq r (inv r (app r w))))
             (λ i → inv r (req r (app r w) i))
             (cong shift (leq r w)) ⟩
      cong shift (leq r w) ∎

  comm-req  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) →
        Square
          (comm-app r (inv r w) ∙ (λ i → app r (comm-inv r w i))) (refl)
          (cong shift (req r w)) (req r (shift w))
  comm-req r w = compPath→Square (
    sym (rUnit (cong shift (req r w))) ∙ sym lemma)
    where
    lemma :
      (comm-app r (inv r w) ∙ (λ i → app r (comm-inv r w i))) ∙ req r (shift w)
        ≡ cong shift (req r w)
    lemma =
      (comm-app r (inv r w) ∙ (λ i → app r (comm-inv r w i))) ∙ req r (shift w)
        ≡⟨ sym (assoc (comm-app r (inv r w)) (λ i → app r (comm-inv r w i)) (req r (shift w))) ⟩
      comm-app r (inv r w) ∙ ((λ i → app r (comm-inv r w i)) ∙ req r (shift w))
        ≡⟨ cong (λ q → comm-app r (inv r w) ∙ (q ∙ req r (shift w)))
             (congFunct (app r) (sym (leq r (inv r w))) (λ i → inv r (req r w i))) ⟩
      comm-app r (inv r w) ∙
        (((λ i → app r (leq r (inv r w) (~ i))) ∙
          (λ i → app r (inv r (req r w i)))) ∙
          req r (shift w))
        ≡⟨ cong (comm-app r (inv r w) ∙_)
             (sym (assoc (λ i → app r (leq r (inv r w) (~ i)))
                         (λ i → app r (inv r (req r w i)))
                         (req r (shift w)))) ⟩
      comm-app r (inv r w) ∙
        ((λ i → app r (leq r (inv r w) (~ i))) ∙
          ((λ i → app r (inv r (req r w i))) ∙
            req r (shift w)))
        ≡⟨ cong (λ q → comm-app r (inv r w) ∙
                    ((λ i → app r (leq r (inv r w) (~ i))) ∙ q))
             (homNatComp (λ z → req r z) (req r w)) ⟩
      comm-app r (inv r w) ∙
        ((λ i → app r (leq r (inv r w) (~ i))) ∙
          (req r (app r (inv r w)) ∙ cong shift (req r w)))
        ≡⟨ doubleCancel (sym (req r (app r (inv r w))))
             (λ i → app r (leq r (inv r w) i))
             (cong shift (req r w)) ⟩
      cong shift (req r w) ∎




  Word∙ : X ⊎ Y → Sequence (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Word∙ a .obj n = Word n a
  Word∙ _ .map   = shift

  Word∞ : X ⊎ Y → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Word∞ a = SeqColim (Word∙ a)

  open module CohR (a : X ⊎ Y) = Coh (Word∙ a)



  base∞ : Word∞ a₀
  base∞ = incl base


  pushCoh-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word∞ (inr y)
  pushCoh-app r w 𝓲 𝓳 =
    compPath-filler (push (app r w)) (λ j → incl (comm-app r w j)) 𝓳 𝓲

  pushCoh-app-top : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓳 : I) →
    pushCoh-app r w i1 𝓳 ≡ incl (comm-app r w 𝓳)
  pushCoh-app-top r w 𝓳 = refl

  pushCoh-inv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-inv r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (inv r w)
      ; (𝓲 = i1) → incl (comm-inv r w 𝓳) })
      (inS (push (inv r w) 𝓲))


  app∞ : {x : X} {y : Y} (r : R x y) → Word∞ (inl x) → Word∞ (inr y)
  app∞ r (incl w)   = incl (app r w)
  app∞ r (push w 𝓲) = pushCoh-app r w 𝓲 i1

  inv∞ : {x : X} {y : Y} (r : R x y) → Word∞ (inr y) → Word∞ (inl x)
  inv∞ r (incl w)   = incl (inv r w)
  inv∞ r (push w 𝓲) = pushCoh-inv r w 𝓲 i1


  comm-inv-app-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word (2 + n) (inl x)
  comm-inv-app-filler r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → shift (inv r (app r w))
      ; (𝓲 = i1) → inv r (comm-app r w 𝓳) })
      (inS (comm-inv r (app r w) 𝓲))

  comm-inv-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) → shift (inv r (app r w)) ≡ inv r (app r (shift w))
  comm-inv-app r w 𝓲 = comm-inv-app-filler r w 𝓲 i1

  pushCoh-inv-app-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 𝓴 : I) → Word∞ (inl x)
  pushCoh-inv-app-filler r w 𝓲 𝓳 =
    hfill (λ 𝓴 → λ
      { (𝓲 = i0) → incl (inv r (app r w))
      ; (𝓲 = i1) → incl (comm-inv-app-filler r w 𝓳 𝓴)
      ; (𝓳 = i0) → push (inv r (app r w)) 𝓲
      ; (𝓳 = i1) → inv∞ r (pushCoh-app r w 𝓲 𝓴) })
      (inS (pushCoh-inv r (app r w) 𝓲 𝓳))

  pushCoh-inv-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-inv-app r w 𝓲 𝓳 = pushCoh-inv-app-filler r w 𝓲 𝓳 i1


  comm-app-inv-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word (2 + n) (inr y)
  comm-app-inv-filler r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → shift (app r (inv r w))
      ; (𝓲 = i1) → app r (comm-inv r w 𝓳) })
      (inS (comm-app r (inv r w) 𝓲))

  comm-app-inv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) → shift (app r (inv r w)) ≡ app r (inv r (shift w))
  comm-app-inv r w 𝓲 = comm-app-inv-filler r w 𝓲 i1

  pushCoh-app-inv-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 𝓴 : I) → Word∞ (inr y)
  pushCoh-app-inv-filler r w 𝓲 𝓳 =
    fill (λ _ → Word∞ _) (λ 𝓴 → λ
      { (𝓲 = i0) → incl (app r (inv r w))
      ; (𝓲 = i1) → incl (comm-app-inv-filler r w 𝓳 𝓴)
      ; (𝓳 = i0) → push (app r (inv r w)) 𝓲
      ; (𝓳 = i1) → app∞ r (pushCoh-inv r w 𝓲 𝓴) })
      (inS (pushCoh-app r (inv r w) 𝓲 𝓳))

  pushCoh-app-inv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word∞ (inr y)
  pushCoh-app-inv r w 𝓲 𝓳 = pushCoh-app-inv-filler r w 𝓲 𝓳 i1



  pushCoh-leq : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (i : I) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-leq r w i 𝓲 =
    hfill (λ 𝓳 → λ
      { (i = i0) → pushCoh-inv-app r w 𝓲 𝓳
      ; (i = i1) → pushCoh-shift _ w 𝓲 𝓳
      -------------
      ; (𝓲 = i0) → incl (leq r w i)
      ; (𝓲 = i1) → incl (comm-leq r w i 𝓳) })
      (inS (push (leq r w i) 𝓲))

  pushCoh-req : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (i : I) (𝓲 𝓳 : I) → Word∞ (inr y)
  pushCoh-req r w i 𝓲 =
    hfill (λ 𝓳 → λ
      { (i = i0) → pushCoh-app-inv r w 𝓲 𝓳
      ; (i = i1) → pushCoh-shift _ w 𝓲 𝓳
      -------------
      ; (𝓲 = i0) → incl (req r w i)
      ; (𝓲 = i1) → incl (comm-req r w i 𝓳) })
      (inS (push (req r w i) 𝓲))

  leq∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inl x)) → inv∞ r (app∞ r w) ≡ shift∞ _ w
  leq∞ r (incl w)   i = incl (leq r w i)
  leq∞ r (push w 𝓲) i = pushCoh-leq r w i 𝓲 i1

  req∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inr y)) → app∞ r (inv∞ r w) ≡ shift∞ _ w
  req∞ r (incl w)   i = incl (req r w i)
  req∞ r (push w 𝓲) i = pushCoh-req r w i 𝓲 i1

  normCoh-leq : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inl x)) (i : I) (𝓲 : I) → Word∞ (inl x)
  normCoh-leq r w i 𝓲 = compPath-filler (leq∞ r w) (sym (push∞ _ w)) 𝓲 i

  norm-leq∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inl x)) → inv∞ r (app∞ r w) ≡ w
  norm-leq∞ r w i = normCoh-leq r w i i1

  normCoh-req : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inr y)) (i : I) (𝓲 : I) → Word∞ (inr y)
  normCoh-req r w i 𝓲 = compPath-filler (req∞ r w) (sym (push∞ _ w)) 𝓲 i

  norm-req∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inr y)) → app∞ r (inv∞ r w) ≡ w
  norm-req∞ r w i = normCoh-req r w i i1

  appIso : {x : X} {y : Y} (r : R x y) → Iso (Word∞ (inl x)) (Word∞ (inr y))
  appIso r .Iso.fun = app∞ r
  appIso r .Iso.inv = inv∞ r
  appIso r .Iso.rightInv = norm-req∞ r
  appIso r .Iso.leftInv  = norm-leq∞ r

  module ThickElim
    (P : {a : X ⊎ Y} → Word∞ a → Type ℓ''')
    (shiftP : {a : X ⊎ Y} (w : Word∞ a) → P w → P (shift∞ _ w))
    (pushP  : {a : X ⊎ Y} (w : Word∞ a) (p : P w)
      → PathP (λ i → P (push∞ _ w i)) p (shiftP _ p))
    (baseP : P base∞)
    (glueP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (app∞ r w))
    (equivP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → isEquiv (glueP r w))
    where

    open isHAEquiv

    hae : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → _
    hae r w = equiv→HAEquiv (_ , equivP r w) .snd

    qinvP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P (app∞ r w) → P (w)
    qinvP r w = hae r w .g

    invP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (inv∞ r w)
    invP r w p =
      qinvP r _ (subst P (sym (req∞ r w)) (shiftP _ p))

    reqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (req∞ r w i))
          (glueP r _ (invP r _ p)) (shiftP _ p)
    reqP r w p i =
      hcomp (λ j → λ
        { (i = i0) → hae r (inv∞ r w) .rinv
            (subst P (sym (req∞ r w)) (shiftP _ p)) (~ j)
        ; (i = i1) → shiftP _ p })
        (subst-filler P (sym (req∞ r w)) (shiftP _ p) (~ i))

    prePushCohP-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-app r w 𝓲 𝓳)
    prePushCohP-app r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-app r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (glueP _ _ p) 𝓲
        ; (𝓳 = i1) → glueP _ _ (pushP _ p 𝓲) })
        (inS (glueP _ _ p)) 𝓲

    commShiftP-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) →
      PathP (λ j → P (incl (comm-app r w j)))
        (shiftP _ (glueP r _ p))
        (glueP r _ (shiftP _ p))
    commShiftP-app r w p j = prePushCohP-app r w p i1 j

    leqP₀  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w))
      → PathP (λ i → P (incl (leq r w i)))
          (invP r _ (glueP r _ p)) (shiftP _ p)
    leqP₀ r w p =
      Iso.inv (congPathIso gluePathEquiv) desired
      where
      leqPath : incl (inv r (app r w)) ≡ incl (shift w)
      leqPath i = incl (leq r w i)

      reqPath : app r (inv r (app r w)) ≡ shift (app r w)
      reqPath = req r (app r w)

      appLeqPath : app r (inv r (app r w)) ≡ app r (shift w)
      appLeqPath i = app r (leq r w i)

      reqP₀ :
        PathP (λ i → P (incl (reqPath i)))
          (glueP r _ (invP r _ (glueP r _ p)))
          (shiftP _ (glueP r _ p))
      reqP₀ = reqP r _ (glueP r _ p)

      preHAE : HAEquiv (shift (app r w) ≡ app r (shift w))
        (app r (inv r (app r w)) ≡ app r (shift w))
      preHAE = iso→HAEquiv (compPathlIso reqPath)

      preHAEOver :
        isHAEquivOver preHAE
          (λ q → PathP (λ i → P (incl (q i)))
            (shiftP _ (glueP r _ p))
            (glueP r _ (shiftP _ p)))
          (λ q → PathP (λ i → P (incl (q i)))
            (glueP r _ (invP r _ (glueP r _ p)))
            (glueP r _ (shiftP _ p)))
          (λ _ → compPathP' {B = λ z → P (incl z)} reqP₀)
      preHAEOver = IsoOver→HAEquivOver (compPathPIsoOver reqP₀)

      gluePathEquiv : (i : I) →
        P (leqPath i) ≃ P (incl (appLeqPath i))
      gluePathEquiv i = glueP r _ , equivP r _

      desired :
        PathP (λ i → P (incl (appLeqPath i)))
          (glueP r _ (invP r _ (glueP r _ p)))
          (glueP r _ (shiftP _ p))
      desired =
        subst
          (λ q → PathP (λ i → P (incl (q i)))
            (glueP r _ (invP r _ (glueP r _ p)))
            (glueP r _ (shiftP _ p)))
          (isHAEquiv.rinv (preHAE .snd) appLeqPath)
          (compPathP' {B = λ z → P (incl z)} reqP₀
            (commShiftP-app r w p))

    commAppP₀ : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) →
      PathP (λ i → P (incl (comm-app r w i)))
        (shiftP _ (glueP r _ p))
        (glueP r _ (shiftP _ p))
    commAppP₀ r w p =
      compPathP' {B = λ z → P (incl z)} {p = reqBack} {q = appLeqPath}
        (symP (reqP r _ (glueP r _ p)))
        (λ i → glueP r _ (leqP₀ r w p i))
      where
      reqBack : shift (app r w) ≡ app r (inv r (app r w))
      reqBack i = req r (app r w) (~ i)

      appLeqPath : app r (inv r (app r w)) ≡ app r (shift w)
      appLeqPath i = app r (leq r w i)

    pushCohP-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-app r w 𝓲 𝓳)
    pushCohP-app = prePushCohP-app

    pushCohP-app-top : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) →
      PathP (λ j → P (incl (comm-app r w j)))
        (shiftP _ (glueP r _ p))
        (glueP r _ (shiftP _ p))
    pushCohP-app-top = commShiftP-app

    commAppP₀β : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) →
      commAppP₀ r w p ≡ pushCohP-app-top r w p
    commAppP₀β r w p =
      cong (compPathP' {B = λ z → P (incl z)} {p = reqBack} {q = appLeqPath}
              (symP (reqP r _ (glueP r _ p))))
        (Iso.rightInv (congPathIso gluePathEquiv) desired)
      ∙ cancelReqβ
      where
      reqPath : app r (inv r (app r w)) ≡ shift (app r w)
      reqPath = req r (app r w)

      reqP₀ :
        PathP (λ i → P (incl (reqPath i)))
          (glueP r _ (invP r _ (glueP r _ p)))
          (shiftP _ (glueP r _ p))
      reqP₀ = reqP r _ (glueP r _ p)

      appLeqPath∞ : app r (inv r (app r w)) ≡ app r (shift w)
      appLeqPath∞ i = app r (leq r w i)

      preHAE : HAEquiv (shift (app r w) ≡ app r (shift w))
        (app r (inv r (app r w)) ≡ app r (shift w))
      preHAE = iso→HAEquiv (compPathlIso reqPath)

      preHAEOver :
        isHAEquivOver preHAE
          (λ q → PathP (λ i → P (incl (q i)))
            (shiftP _ (glueP r _ p))
            (glueP r _ (shiftP _ p)))
          (λ q → PathP (λ i → P (incl (q i)))
            (glueP r _ (invP r _ (glueP r _ p)))
            (glueP r _ (shiftP _ p)))
          (λ _ → compPathP' {B = λ z → P (incl z)} reqP₀)
      preHAEOver = IsoOver→HAEquivOver (compPathPIsoOver reqP₀)

      gluePathEquiv : (i : I) →
        P (incl (leq r w i)) ≃ P (incl (appLeqPath∞ i))
      gluePathEquiv i = glueP r _ , equivP r _

      desired :
        PathP (λ i → P (incl (appLeqPath∞ i)))
          (glueP r _ (invP r _ (glueP r _ p)))
          (glueP r _ (shiftP _ p))
      desired =
        subst
          (λ q → PathP (λ i → P (incl (q i)))
            (glueP r _ (invP r _ (glueP r _ p)))
            (glueP r _ (shiftP _ p)))
          (isHAEquiv.rinv (preHAE .snd) appLeqPath∞)
          (compPathP' {B = λ z → P (incl z)} reqP₀
            (pushCohP-app-top r w p))

      reqBack : shift (app r w) ≡ app r (inv r (app r w))
      reqBack i = req r (app r w) (~ i)

      appLeqPath : app r (inv r (app r w)) ≡ app r (shift w)
      appLeqPath i = app r (leq r w i)

      cancelReqβ :
        compPathP' {B = λ z → P (incl z)} {p = reqBack} {q = appLeqPath}
          (symP (reqP r _ (glueP r _ p)))
          desired
        ≡ pushCohP-app-top r w p
      cancelReqβ =
        haeOverInv-rinv (preHAE .snd) preHAEOver
          appLeqPath∞ (pushCohP-app-top r w p)

    elim₀ : {a : X ⊎ Y} {n : ℕ} (w : Word n a) → P (incl w)
    elim₀ (shift w) = shiftP _ (elim₀ w)
    elim₀  base     = baseP
    elim₀ (app r w) = glueP r _ (elim₀ w)
    elim₀ (inv r w)   = invP r _ (elim₀ w)
    elim₀ (leq r w i) = leqP₀ r w (elim₀ w) i
    elim₀ (req r w i) = reqP r _ (elim₀ w) i

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim (incl w)   = elim₀ w
    elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲

    elimβ-app : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) → elim (app∞ r w) ≡ glueP r _ (elim w)
    elimβ-app r (incl w) = refl
    elimβ-app r (push w 𝓲) 𝓴 =
      comp (λ 𝓳 → P (pushCoh-app r w 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → glueP r _ (elim₀ w)
        ; (𝓲 = i1) → commAppP₀β r w (elim₀ w) 𝓴 𝓳
        ; (𝓴 = i0) → elim (pushCoh-app r w 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-app r w (elim₀ w) 𝓲 𝓳 })
        (elim (push (app r w) 𝓲))

  module ThinElim
    (P : {a : X ⊎ Y} → Word∞ a → Type ℓ''')
    (baseP : P base∞)
    (glueP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (app∞ r w))
    (invP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (inv∞ r w))
    (norm-leqP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (norm-leq∞ r w i)) (invP r _ (glueP r _ p)) p)
    (norm-reqP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (norm-req∞ r w i)) (glueP r _ (invP r _ p)) p)
    (equivP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → isEquiv (glueP r w))
    where

    transport-push∞ : {a : X ⊎ Y} (w : Word∞ a) (p : P w) (i : I) → P (push∞ _ w i)
    transport-push∞ w p i = transport-filler (λ i → P (push∞ _ w i)) p i

    shiftP : {a : X ⊎ Y} (w : Word∞ a) → P w → P (shift∞ _ w)
    shiftP w p = transport-push∞ w p i1

    pushP : {a : X ⊎ Y} (w : Word∞ a) (p : P w)
      → PathP (λ i → P (push∞ _ w i)) p (shiftP _ p)
    pushP w p i = transport-push∞ w p i

    open module CohPR (a : X ⊎ Y) = CohP a P shiftP pushP

    normCohP-leq : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) (p : P w) (i : I) (𝓲 : I) → P (normCoh-leq r w i 𝓲)
    normCohP-leq r w p i 𝓲 =
      fill (λ 𝓲 → P (normCoh-leq r w i (~ 𝓲))) (λ 𝓲 → λ
        { (i = i0) → invP r _ (glueP r _ p)
        ; (i = i1) → pushP _ p 𝓲 })
        (inS (norm-leqP r w p i)) (~ 𝓲)

    normCohP-req : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inr y)) (p : P w) (i : I) (𝓲 : I) → P (normCoh-req r w i 𝓲)
    normCohP-req r w p i 𝓲 =
      fill (λ 𝓲 → P (normCoh-req r w i (~ 𝓲))) (λ 𝓲 → λ
        { (i = i0) → glueP r _ (invP r _ p)
        ; (i = i1) → pushP _ p 𝓲 })
        (inS (norm-reqP r w p i)) (~ 𝓲)

    leqP : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) (p : P w)
      → PathP (λ i → P (leq∞ r w i)) (invP r _ (glueP r _ p)) (shiftP _ p)
    leqP r w p i = normCohP-leq r w p i i0

    reqP : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inr y)) (p : P w)
      → PathP (λ i → P (req∞ r w i)) (glueP r _ (invP r _ p)) (shiftP _ p)
    reqP r w p i = normCohP-req r w p i i0

    appIsoOver : {x : X} {y : Y} (r : R x y) →
      IsoOver (appIso r)
        (λ (w : Word∞ (inl x)) → P w)
        (λ (w : Word∞ (inr y)) → P w)
    appIsoOver r .IsoOver.fun = glueP r
    appIsoOver r .IsoOver.inv = invP r
    appIsoOver r .IsoOver.rightInv = norm-reqP r
    appIsoOver r .IsoOver.leftInv = norm-leqP r

    appHAEOver : {x : X} {y : Y} (r : R x y) →
      isHAEquivOver (iso→HAEquiv (appIso r))
        (λ (w : Word∞ (inl x)) → P w)
        (λ (w : Word∞ (inr y)) → P w)
        (glueP r)
    appHAEOver r = IsoOver→HAEquivOver (appIsoOver r)

    module Thick = ThickElim P shiftP pushP baseP glueP equivP

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim = Thick.elim

    elimβ-[] : elim base∞ ≡ baseP
    elimβ-[] = refl

    elimβ-app : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) → elim (app∞ r w) ≡ glueP r _ (elim w)
    elimβ-app = Thick.elimβ-app



  module KrausVonRaumerElim
    (P : {a : X ⊎ Y} → Word∞ a → Type ℓ''')
    (baseP : P base∞)
    (glueP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (app∞ r w))
    (equivP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → isEquiv (glueP r w))
    where

    transport-push∞ : {a : X ⊎ Y} (w : Word∞ a) (p : P w) (i : I) → P (push∞ _ w i)
    transport-push∞ w p i = transport-filler (λ i → P (push∞ _ w i)) p i

    shiftP : {a : X ⊎ Y} (w : Word∞ a) → P w → P (shift∞ _ w)
    shiftP w p = transport-push∞ w p i1

    pushP : {a : X ⊎ Y} (w : Word∞ a) (p : P w)
      → PathP (λ i → P (push∞ _ w i)) p (shiftP _ p)
    pushP w p i = transport-push∞ w p i

    appHAE : {x : X} {y : Y} (r : R x y) → HAEquiv (Word∞ (inl x)) (Word∞ (inr y))
    appHAE r = iso→HAEquiv (appIso r)

    glueIsoOver : {x : X} {y : Y} (r : R x y) →
      IsoOver (isHAEquiv→Iso (appHAE r .snd))
        (λ (w : Word∞ (inl x)) → P w)
        (λ (w : Word∞ (inr y)) → P w)
    glueIsoOver r =
      liftHAEToIsoOver (app∞ r) (appHAE r .snd)
        (λ w → equivToIso (glueP r w , equivP r w))

    module Thick = ThickElim P shiftP pushP baseP glueP equivP

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim = Thick.elim

    elimβ-[] : elim base∞ ≡ baseP
    elimβ-[] = refl

    elimβ-app : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) → elim (app∞ r w) ≡ glueP r _ (elim w)
    elimβ-app = Thick.elimβ-app
