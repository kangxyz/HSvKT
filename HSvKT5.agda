{-

The Higher Seifert-van Kampen Theorem

-}
{-# OPTIONS --safe --cubical --lossy-unification #-}
module HSvKT5 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sum hiding (elim ; map)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Utils.Coherence


private
  variable
    ℓ ℓ' ℓ'' ℓ''' ℓA ℓB : Level


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
  pushCoh-app r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (app r w)
      ; (𝓲 = i1) → incl (comm-app r w 𝓳) })
      (inS (push (app r w) 𝓲))

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

    pushCohP-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-app r w 𝓲 𝓳)
    pushCohP-app r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-app r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (glueP _ _ p) 𝓲
        ; (𝓳 = i1) → glueP _ _ (pushP _ p 𝓲) })
        (inS (glueP _ _ p)) 𝓲

    loopCancel : {A : Type ℓA} {a b c : A}
      (p : a ≡ b) (q : a ≡ c) →
      p ∙ ((sym p ∙ q) ∙ sym q) ≡ refl
    loopCancel p q =
      p ∙ ((sym p ∙ q) ∙ sym q)
        ≡⟨ cong (p ∙_) (sym (assoc (sym p) q (sym q))) ⟩
      p ∙ (sym p ∙ (q ∙ sym q))
        ≡⟨ cong (λ s → p ∙ (sym p ∙ s)) (rCancel q) ⟩
      p ∙ (sym p ∙ refl)
        ≡⟨ cong (p ∙_) (sym (rUnit (sym p))) ⟩
      p ∙ sym p
        ≡⟨ rCancel p ⟩
      refl ∎

    leqP₀  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w))
      → PathP (λ i → P (incl (leq r w i)))
          (invP r _ (glueP r _ p)) (shiftP _ p)
    leqP₀ r w p i =
      hcomp (λ j → λ
        { (i = i0) → qEq (~ j)
        ; (i = i1) → shiftP _ p })
        (subst-filler P (sym leqPath) (shiftP _ p) (~ i))
      where
      leqPath : incl (inv r (app r w)) ≡ incl (shift w)
      leqPath i = incl (leq r w i)

      reqPath : incl (app r (inv r (app r w))) ≡ incl (shift (app r w))
      reqPath i = incl (req r (app r w) i)

      appLeqPath : incl (app r (inv r (app r w))) ≡ incl (app r (shift w))
      appLeqPath i = incl (app r (leq r w i))

      commPath : incl (shift (app r w)) ≡ incl (app r (shift w))
      commPath i = incl (comm-app r w i)

      pulled : P (incl (app r (inv r (app r w))))
      pulled = subst P (sym reqPath) (shiftP _ (glueP r _ p))

      leqPulled : P (incl (inv r (app r w)))
      leqPulled = subst P (sym leqPath) (shiftP _ p)

      commSliceP :
        PathP (λ i → P (sym appLeqPath i))
          (glueP r _ (shiftP _ p))
          (glueP r _ leqPulled)
      commSliceP =
        toPathP (substCommSlice
          (λ z → P z)
          (λ z → P (app∞ r z))
          (λ z → glueP r z)
          (sym leqPath)
          (shiftP _ p))

      reqBack :
        PathP (λ i → P (reqPath i))
          pulled
          (shiftP _ (glueP r _ p))
      reqBack =
        symP (subst-filler P (sym reqPath) (shiftP _ (glueP r _ p)))

      pushThenComm :
        PathP (λ i → P ((commPath ∙ sym appLeqPath) i))
          (shiftP _ (glueP r _ p))
          (glueP r _ leqPulled)
      pushThenComm =
        compPathP' {B = λ z → P z} {p = commPath} {q = sym appLeqPath}
          (λ j → pushCohP-app r w p i1 j)
          commSliceP

      overLoop :
        PathP (λ i → P ((reqPath ∙ (commPath ∙ sym appLeqPath)) i))
          pulled
          (glueP r _ leqPulled)
      overLoop =
        compPathP' {B = λ z → P z} {p = reqPath} {q = commPath ∙ sym appLeqPath}
          reqBack
          pushThenComm

      commPath≡ : commPath ≡ sym reqPath ∙ appLeqPath
      commPath≡ = congFunct incl (sym (req r (app r w))) (λ i → app r (leq r w i))

      loop≡refl : reqPath ∙ (commPath ∙ sym appLeqPath) ≡ refl
      loop≡refl =
        cong (λ c → reqPath ∙ (c ∙ sym appLeqPath)) commPath≡
        ∙ loopCancel reqPath appLeqPath

      pulled≡glue :
        pulled ≡ glueP r _ leqPulled
      pulled≡glue =
        subst (λ l → PathP (λ i → P (l i)) pulled (glueP r _ leqPulled))
          loop≡refl overLoop

      qEq : invP r _ (glueP r _ p) ≡ leqPulled
      qEq =
        cong (qinvP r _) pulled≡glue
        ∙ hae r _ .linv leqPulled


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

    module Thick = ThickElim P shiftP pushP baseP glueP equivP

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim = Thick.elim

    elimβ-[] : elim base∞ ≡ baseP
    elimβ-[] = refl
