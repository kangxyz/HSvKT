{-

The Higher Seifert-van Kampen Theorem

-}
{-# OPTIONS --safe --cubical --lossy-unification #-}
module HSvKT5 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.HalfAdjoint
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sum hiding (elim ; map)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Utils.Coherence


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


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


  {- coh : {n : ℕ} {x : X} {y : Y} (r : R x y) (w : Word n (inl x)) → shift (
    leq r w) ≡ app r (shift w)
  coh = {! !} -}



  comm-app : {n : ℕ} {x : X} {y : Y} (r : R x y) (w : Word n (inl x)) → shift (app r w) ≡ app r (shift w)
  comm-app r w = (λ i → req r (app r w) (~ i)) ∙ (λ i → app r (leq r w i))

  comm-inv : {n : ℕ} {x : X} {y : Y} (r : R x y) (w : Word n (inr y)) → shift (inv r w) ≡ inv r (shift w)
  comm-inv r w = (λ i → leq r (inv r w) (~ i)) ∙ (λ i → inv r (req r w i))

  comm-leq  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) →
        Square
          (comm-inv r (app r w) ∙ (λ i → inv r (comm-app r w i))) (refl)
          (cong shift (leq r w)) (leq r (shift w))
  comm-leq = {! !}

  comm-req  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) →
        Square
          (comm-app r (inv r w) ∙ (λ i → app r (comm-inv r w i))) (refl)
          (cong shift (req r w)) (req r (shift w))
  comm-req = {! !}




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
    invP r w p = {! !}

    leqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (leq∞ r w i))
          (invP r _ (glueP r _ p)) (shiftP _ p)
    leqP = {! !}

    reqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (req∞ r w i))
          (glueP r _ (invP r _ p)) (shiftP _ p)
    reqP = {! !}


    {- elim₀ : {a : X ⊎ Y} {n : ℕ} (w : Word n a) → P (incl w)
    elim₀ (shift w) = shiftP _ (elim₀ w)
    elim₀  base     = baseP
    elim₀ (app r w) = glueP r _ (elim₀ w)
    elim₀ (inv r w)   = hae r _ .g (elim₀ w)
    elim₀ (leq r w i) = hae r _ .linv (elim₀ w) i
    elim₀ (req r w i) = hae r _ .rinv (elim₀ w) i

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim (incl w)   = elim₀ w
    elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲 -}



{-  inv-eq : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w) → linvP r w p ≡ rinvP r w p
    inv-eq = {! !}

    reqP-alt : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (req∞ r w i)) (glueP r _ (linvP r _ p)) (shiftP _ p)
    reqP-alt = {! !}

    pushCohP-app : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-app r w 𝓲 𝓳)
    pushCohP-app r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-app r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (glueP _ _ p) 𝓲
        ; (𝓳 = i1) → glueP _ _ (pushP _ p 𝓲) })
        (inS (glueP _ _ p)) 𝓲


    elim₀ : {a : X ⊎ Y} {n : ℕ} (w : Word n a) → P (incl w)
    elim₀ (shift w) = shiftP _ (elim₀ w)
    elim₀  base     = baseP
    elim₀ (app r w) = glueP r _ (elim₀ w)
    elim₀ (inv r w)   = linvP r _ (elim₀ w)
    elim₀ (leq r w i) = leqP r _ (elim₀ w) i
    elim₀ (req r w i) = reqP-alt r _ (elim₀ w) i

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim (incl w)   = elim₀ w
    elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲

    square2 : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) →
        SquareP (λ 𝓲 𝓴 → P (pushCoh-app r w 𝓲 i1))
          refl refl (λ 𝓲 → elim (pushCoh-app r w 𝓲 i1)) (λ 𝓲 → glueP _ _ (pushP _ (elim₀ w) 𝓲))
    square2 = {! !}

    elimβ-glue : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) → elim (app∞ r w) ≡ glueP r _ (elim w)
    elimβ-glue r (incl w)     = refl
    elimβ-glue r (push w 𝓲) 𝓴 = square2 r w 𝓲 𝓴
      {- comp (λ 𝓳 → P (pushCoh-app r w 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → elim₀ (app r w)
        ; (𝓲 = i1) → square r w 𝓳 𝓴 {- elim₀ (comm-app r w 𝓳) -}
        ; (𝓴 = i0) → elim (pushCoh-app r w 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-app r w (elim₀ w) 𝓲 𝓳 })
        (elim (push (app r w) 𝓲)) -}

 -}
