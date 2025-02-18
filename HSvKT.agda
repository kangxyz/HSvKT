{-

The Higher Seifert-van Kampen Theorem

-}
{-# OPTIONS --safe --cubical --lossy-unification #-}
module HSvKT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sum hiding (elim ; map)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Coherence


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


module _
  (X : Type ℓ) (Y : Type ℓ')
  (R : X → Y → Type ℓ'')
  (a₀ : X ⊎ Y)
  where

  open Sequence

  data Code : X ⊎ Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    base : Code a₀
    glue : {x : X} {y : Y} (r : R x y) → Code (inl x) → Code (inr y)
    linv : {x : X} {y : Y} (r : R x y) → Code (inr y) → Code (inl x)
    rinv : {x : X} {y : Y} (r : R x y) → Code (inr y) → Code (inl x)
    leq  : {x : X} {y : Y} (r : R x y) (u : Code (inl x)) → linv r (glue r u) ≡ u
    req  : {x : X} {y : Y} (r : R x y) (v : Code (inr y)) → glue r (rinv r v) ≡ v


  data Word : ℕ → X ⊎ Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    shift : {n : ℕ} {a : X ⊎ Y} → Word n a → Word (suc n) a
    base  : Word 0 a₀
    glue  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → Word n (inl x) → Word (suc n) (inr y)
    linv  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → Word n (inr y) → Word (suc n) (inl x)
    rinv  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → Word n (inr y) → Word (suc n) (inl x)
    leq   : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) → linv r (glue r w) ≡ shift (shift w)
    req   : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) → glue r (rinv r w) ≡ shift (shift w)
    comm-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) → shift (glue r w) ≡ glue r (shift w)
    comm-linv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) → shift (linv r w) ≡ linv r (shift w)
    comm-rinv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) → shift (rinv r w) ≡ rinv r (shift w)
    comm-leq  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) →
        Square
          (comm-linv r (glue r w) ∙ (λ i → linv r (comm-glue r w i))) (refl ∙ refl)
          (cong shift (leq r w)) (leq r (shift w))
    comm-req  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) →
        Square
          (comm-glue r (rinv r w) ∙ (λ i → glue r (comm-rinv r w i))) (refl ∙ refl)
          (cong shift (req r w)) (req r (shift w))



  Word∙ : X ⊎ Y → Sequence (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Word∙ a .obj n = Word n a
  Word∙ _ .map   = shift

  Word∞ : X ⊎ Y → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  Word∞ a = SeqColim (Word∙ a)

  open module CohR (a : X ⊎ Y) = Coh (Word∙ a)



  base∞ : Word∞ a₀
  base∞ = incl base


  pushCoh-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word∞ (inr y)
  pushCoh-glue r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (glue r w)
      ; (𝓲 = i1) → incl (comm-glue r w 𝓳) })
      (inS (push (glue r w) 𝓲))

  pushCoh-linv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-linv r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (linv r w)
      ; (𝓲 = i1) → incl (comm-linv r w 𝓳) })
      (inS (push (linv r w) 𝓲))

  pushCoh-rinv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-rinv r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → incl (rinv r w)
      ; (𝓲 = i1) → incl (comm-rinv r w 𝓳) })
      (inS (push (rinv r w) 𝓲))

  glue∞ : {x : X} {y : Y} (r : R x y) → Word∞ (inl x) → Word∞ (inr y)
  glue∞ r (incl w)   = incl (glue r w)
  glue∞ r (push w 𝓲) = pushCoh-glue r w 𝓲 i1

  linv∞ : {x : X} {y : Y} (r : R x y) → Word∞ (inr y) → Word∞ (inl x)
  linv∞ r (incl w)   = incl (linv r w)
  linv∞ r (push w 𝓲) = pushCoh-linv r w 𝓲 i1

  rinv∞ : {x : X} {y : Y} (r : R x y) → Word∞ (inr y) → Word∞ (inl x)
  rinv∞ r (incl w)   = incl (rinv r w)
  rinv∞ r (push w 𝓲) = pushCoh-rinv r w 𝓲 i1


  comm-linv-glue-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word (3 + n) (inl x)
  comm-linv-glue-filler r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → shift (linv r (glue r w))
      ; (𝓲 = i1) → linv r (comm-glue r w 𝓳) })
      (inS (comm-linv r (glue r w) 𝓲))

  comm-linv-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) → shift (linv r (glue r w)) ≡ linv r (glue r (shift w))
  comm-linv-glue r w 𝓲 = comm-linv-glue-filler r w 𝓲 i1

  pushCoh-linv-glue-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 𝓴 : I) → Word∞ (inl x)
  pushCoh-linv-glue-filler r w 𝓲 𝓳 =
    hfill (λ 𝓴 → λ
      { (𝓲 = i0) → incl (linv r (glue r w))
      ; (𝓲 = i1) → incl (comm-linv-glue-filler r w 𝓳 𝓴)
      ; (𝓳 = i0) → push (linv r (glue r w)) 𝓲
      ; (𝓳 = i1) → linv∞ r (pushCoh-glue r w 𝓲 𝓴) })
      (inS (pushCoh-linv r (glue r w) 𝓲 𝓳))

  pushCoh-linv-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-linv-glue r w 𝓲 𝓳 = pushCoh-linv-glue-filler r w 𝓲 𝓳 i1


  comm-glue-rinv-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word (3 + n) (inr y)
  comm-glue-rinv-filler r w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → shift (glue r (rinv r w))
      ; (𝓲 = i1) → glue r (comm-rinv r w 𝓳) })
      (inS (comm-glue r (rinv r w) 𝓲))

  comm-glue-rinv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) → shift (glue r (rinv r w)) ≡ glue r (rinv r (shift w))
  comm-glue-rinv r w 𝓲 = comm-glue-rinv-filler r w 𝓲 i1

  pushCoh-glue-rinv-filler : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 𝓴 : I) → Word∞ (inr y)
  pushCoh-glue-rinv-filler r w 𝓲 𝓳 =
    fill (λ _ → Word∞ _) (λ 𝓴 → λ
      { (𝓲 = i0) → incl (glue r (rinv r w))
      ; (𝓲 = i1) → incl (comm-glue-rinv-filler r w 𝓳 𝓴)
      ; (𝓳 = i0) → push (glue r (rinv r w)) 𝓲
      ; (𝓳 = i1) → glue∞ r (pushCoh-rinv r w 𝓲 𝓴) })
      (inS (pushCoh-glue r (rinv r w) 𝓲 𝓳))

  pushCoh-glue-rinv : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (𝓲 𝓳 : I) → Word∞ (inr y)
  pushCoh-glue-rinv r w 𝓲 𝓳 = pushCoh-glue-rinv-filler r w 𝓲 𝓳 i1


  pushCoh-leq : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inl x)) (i : I) (𝓲 𝓳 : I) → Word∞ (inl x)
  pushCoh-leq r w i 𝓲 =
    hfill (λ 𝓳 → λ
      { (i = i0) → pushCoh-linv-glue r w 𝓲 𝓳
      ; (i = i1) → pushCoh-shift-shift _ w 𝓲 𝓳
      -------------
      ; (𝓲 = i0) → incl (leq r w i)
      ; (𝓲 = i1) → incl (comm-leq r w i 𝓳) })
      (inS (push (leq r w i) 𝓲))

  pushCoh-req : {n : ℕ} {x : X} {y : Y} (r : R x y)
    (w : Word n (inr y)) (i : I) (𝓲 𝓳 : I) → Word∞ (inr y)
  pushCoh-req r w i 𝓲 =
    hfill (λ 𝓳 → λ
      { (i = i0) → pushCoh-glue-rinv r w 𝓲 𝓳
      ; (i = i1) → pushCoh-shift-shift _ w 𝓲 𝓳
      -------------
      ; (𝓲 = i0) → incl (req r w i)
      ; (𝓲 = i1) → incl (comm-req r w i 𝓳) })
      (inS (push (req r w i) 𝓲))


  leq∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inl x)) → linv∞ r (glue∞ r w) ≡ shift∞ _ (shift∞ _ w)
  leq∞ r (incl w)   i = incl (leq r w i)
  leq∞ r (push w 𝓲) i = pushCoh-leq r w i 𝓲 i1

  req∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inr y)) → glue∞ r (rinv∞ r w) ≡ shift∞ _ (shift∞ _ w)
  req∞ r (incl w)   i = incl (req r w i)
  req∞ r (push w 𝓲) i = pushCoh-req r w i 𝓲 i1




  module ThickElim
    (P : {a : X ⊎ Y} → Word∞ a → Type ℓ''')
    (shiftP : {a : X ⊎ Y} (w : Word∞ a) → P w → P (shift∞ _ w))
    (pushP  : {a : X ⊎ Y} (w : Word∞ a) (p : P w)
      → PathP (λ i → P (push∞ _ w i)) p (shiftP _ p))
    (baseP : P base∞)
    (glueP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (glue∞ r w))
    (linvP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (linv∞ r w))
    (rinvP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (rinv∞ r w))
    (leqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (leq∞ r w i))
          (linvP r _ (glueP r _ p)) (shiftP _ (shiftP _ p)))
    (reqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (req∞ r w i))
          (glueP r _ (rinvP r _ p)) (shiftP _ (shiftP _ p)))
    where

    open module CohRP (a : X ⊎ Y) = CohP a P shiftP pushP


    pushCohP-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-glue r w 𝓲 𝓳)
    pushCohP-glue r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-glue r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (glueP _ _ p) 𝓲
        ; (𝓳 = i1) → glueP _ _ (pushP _ p 𝓲) })
        (inS (glueP _ _ p)) 𝓲

    pushCohP-linv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-linv r w 𝓲 𝓳)
    pushCohP-linv r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-linv r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (linvP r _ p) 𝓲
        ; (𝓳 = i1) → linvP r _ (pushP _ p 𝓲) })
        (inS (linvP r _ p)) 𝓲

    pushCohP-rinv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-rinv r w 𝓲 𝓳)
    pushCohP-rinv r w p 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-rinv r w 𝓲 𝓳)) (λ 𝓲 → λ
        { (𝓳 = i0) → pushP _ (rinvP r _ p) 𝓲
        ; (𝓳 = i1) → rinvP r _ (pushP _ p 𝓲) })
        (inS (rinvP r _ p)) 𝓲

    pushCohP-linv-glue : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-linv-glue r w 𝓲 𝓳)
    pushCohP-linv-glue r w p 𝓲 𝓳 =
      comp (λ 𝓴 → P (pushCoh-linv-glue-filler r w 𝓲 𝓳 𝓴)) (λ 𝓴 → λ
        { (𝓲 = i0) → linvP r _ (glueP r _ p)
     -- ; (𝓲 = i1) → incl (compPath-filler _ _ 𝓴 𝓳)
        ; (𝓳 = i0) → pushP _ (linvP r _ (glueP r _ p)) 𝓲
        ; (𝓳 = i1) → linvP r _ (pushCohP-glue r w p 𝓲 𝓴) })
        (pushCohP-linv r _ (glueP r _ p) 𝓲 𝓳)

    pushCohP-glue-rinv : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) (p : P (incl w)) (𝓲 𝓳 : I) → P (pushCoh-glue-rinv r w 𝓲 𝓳)
    pushCohP-glue-rinv r w p 𝓲 𝓳 =
      comp (λ 𝓴 → P (pushCoh-glue-rinv-filler r w 𝓲 𝓳 𝓴)) (λ 𝓴 → λ
        { (𝓲 = i0) → glueP r _ (rinvP r _ p)
     -- ; (𝓲 = i1) → incl (compPath-filler _ _ 𝓴 𝓳)
        ; (𝓳 = i0) → pushP _ (glueP r _ (rinvP r _ p)) 𝓲
        ; (𝓳 = i1) → glueP r _ (pushCohP-rinv r w p 𝓲 𝓴) })
        (pushCohP-glue r _ (rinvP r _ p) 𝓲 𝓳)

    pushCohP-leq : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inl x)) (p : P (incl w)) (i : I) (𝓲 𝓳 : I) → P (pushCoh-leq r w i 𝓲 𝓳)
    pushCohP-leq r w p i 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-leq r w i 𝓲 𝓳)) (λ 𝓲 → λ
        { (i = i0) → pushCohP-linv-glue   r _ p 𝓲 𝓳
        ; (i = i1) → pushCohP-shift-shift _ _ p 𝓲 𝓳
        -------------
        ; (𝓳 = i0) → pushP _ (leqP r _ p i) 𝓲
        ; (𝓳 = i1) → leqP r _ (pushP _ p 𝓲) i })
        (inS (leqP r _ p i)) 𝓲

    pushCohP-req : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : Word n (inr y)) (p : P (incl w)) (i : I) (𝓲 𝓳 : I) → P (pushCoh-req r w i 𝓲 𝓳)
    pushCohP-req r w p i 𝓲 𝓳 =
      fill (λ 𝓲 → P (pushCoh-req r w i 𝓲 𝓳)) (λ 𝓲 → λ
        { (i = i0) → pushCohP-glue-rinv   r _ p 𝓲 𝓳
        ; (i = i1) → pushCohP-shift-shift _ _ p 𝓲 𝓳
        -------------
        ; (𝓳 = i0) → pushP _ (reqP r _ p i) 𝓲
        ; (𝓳 = i1) → reqP r _ (pushP _ p 𝓲) i })
        (inS (reqP r _ p i)) 𝓲


    elim₀ : {a : X ⊎ Y} {n : ℕ} (w : Word n a) → P (incl w)
    elim₀ (shift w) = shiftP _ (elim₀ w)
    elim₀  base     = baseP
    elim₀ (glue r w)  = glueP r _ (elim₀ w)
    elim₀ (linv r w)  = linvP r _ (elim₀ w)
    elim₀ (rinv r w)  = rinvP r _ (elim₀ w)
    elim₀ (leq r w i) = leqP  r _ (elim₀ w) i
    elim₀ (req r w i) = reqP  r _ (elim₀ w) i
    elim₀ (comm-glue r w 𝓳)   = pushCohP-glue r w (elim₀ w) i1 𝓳
    elim₀ (comm-linv r w 𝓳)   = pushCohP-linv r w (elim₀ w) i1 𝓳
    elim₀ (comm-rinv r w 𝓳)   = pushCohP-rinv r w (elim₀ w) i1 𝓳
    elim₀ (comm-leq  r w i 𝓳) = pushCohP-leq  r w (elim₀ w) i i1 𝓳
    elim₀ (comm-req  r w i 𝓳) = pushCohP-req  r w (elim₀ w) i i1 𝓳

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim (incl w)   = elim₀ w
    elim (push w 𝓲) = pushP _ (elim₀ w) 𝓲


    elimβ-glue : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) → elim (glue∞ r w) ≡ glueP r _ (elim w)
    elimβ-glue r (incl w)     = refl
    elimβ-glue r (push w 𝓲) 𝓴 =
      comp (λ 𝓳 → P (pushCoh-glue r w 𝓲 𝓳)) (λ 𝓳 → λ
        { (𝓲 = i0) → elim₀ (glue r w)
        ; (𝓲 = i1) → elim₀ (comm-glue r w 𝓳)
        ; (𝓴 = i0) → elim (pushCoh-glue r w 𝓲 𝓳)
        ; (𝓴 = i1) → pushCohP-glue r w (elim₀ w) 𝓲 𝓳 })
        (elim (push (glue r w) 𝓲))




  normCoh-leq : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inl x)) (i : I) (𝓲 : I) → Word∞ (inl x)
  normCoh-leq r w i 𝓲 = compPath-filler (leq∞ r w) (sym (push²∞ _ w)) 𝓲 i

  norm-leq∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inl x)) → linv∞ r (glue∞ r w) ≡ w
  norm-leq∞ r w i = normCoh-leq r w i i1

  normCoh-req : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inr y)) (i : I) (𝓲 : I) → Word∞ (inr y)
  normCoh-req r w i 𝓲 = compPath-filler (req∞ r w) (sym (push²∞ _ w)) 𝓲 i

  norm-req∞ : {x : X} {y : Y} (r : R x y)
    (w : Word∞ (inr y)) → glue∞ r (rinv∞ r w) ≡ w
  norm-req∞ r w i = normCoh-req r w i i1



  module ThinElim
    (P : {a : X ⊎ Y} → Word∞ a → Type ℓ''')
    (baseP : P base∞)
    (glueP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (glue∞ r w))
    (linvP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (linv∞ r w))
    (rinvP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (rinv∞ r w))
    (norm-leqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (norm-leq∞ r w i)) (linvP r _ (glueP r _ p)) p)
    (norm-reqP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) (p : P w)
      → PathP (λ i → P (norm-req∞ r w i)) (glueP r _ (rinvP r _ p)) p)
    where

    transport-push∞ : {a : X ⊎ Y} (w : Word∞ a) (p : P w) (i : I) → P (push∞ _ w i)
    transport-push∞ w p i = transport-filler (λ i → P (push∞ _ w i)) p i

    transport-push²∞ : {a : X ⊎ Y} (w : Word∞ a) (p : P w) (i : I) → P (push²∞ _ w i)
    transport-push²∞ w p i = transport-filler (λ i → P (push²∞ _ w i)) p i

    shiftP : {a : X ⊎ Y} (w : Word∞ a) → P w → P (shift∞ _ w)
    shiftP w p = transport-push∞ w p i1

    pushP : {a : X ⊎ Y} (w : Word∞ a) (p : P w) → PathP (λ i → P (push∞ _ w i)) p (shiftP _ p)
    pushP w p i = transport-push∞ w p i

    open module CohPR (a : X ⊎ Y) = CohP a P shiftP pushP

    normCohP-leq : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) (p : P w) (i : I) (𝓲 : I) → P (normCoh-leq r w i 𝓲)
    normCohP-leq r w p i 𝓲 =
      fill (λ 𝓲 → P (normCoh-leq r w i (~ 𝓲))) (λ 𝓲 → λ
        { (i = i0) → linvP r _ (glueP r _ p)
        ; (i = i1) → push²P _ w p 𝓲 })
        (inS (norm-leqP r w p i)) (~ 𝓲)

    normCohP-req : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inr y)) (p : P w) (i : I) (𝓲 : I) → P (normCoh-req r w i 𝓲)
    normCohP-req r w p i 𝓲 =
      fill (λ 𝓲 → P (normCoh-req r w i (~ 𝓲))) (λ 𝓲 → λ
        { (i = i0) → glueP r _ (rinvP r _ p)
        ; (i = i1) → push²P _ w p 𝓲 })
        (inS (norm-reqP r w p i)) (~ 𝓲)

    leqP : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inl x)) (p : P w)
      → PathP (λ i → P (leq∞ r w i)) (linvP r _ (glueP r _ p)) (shiftP _ (shiftP _ p))
    leqP r w p i = normCohP-leq r w p i i0

    reqP : {x : X} {y : Y} (r : R x y)
      (w : Word∞ (inr y)) (p : P w)
      → PathP (λ i → P (req∞ r w i)) (glueP r _ (rinvP r _ p)) (shiftP _ (shiftP _ p))
    reqP r w p i = normCohP-req r w p i i0

    module Thick = ThickElim P shiftP pushP baseP glueP linvP rinvP leqP reqP

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim = Thick.elim

    elimβ-[] : elim base∞ ≡ baseP
    elimβ-[] = refl

    elimβ-glue : {x : X} {y : Y} (r : R x y) (w : Word∞ (inl x)) → elim (glue∞ r w) ≡ glueP r _ (elim w)
    elimβ-glue = Thick.elimβ-glue



  module KrausVonRaumerElim
    (P : {a : X ⊎ Y} → Word∞ a → Type ℓ''')
    (baseP : P base∞)
    (glueP  : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → P w → P (glue∞ r w))
    (equivP : {x : X} {y : Y} (r : R x y) (w : Word∞ _) → isEquiv (glueP r w))
    where

    open import Cubical.Foundations.Equiv.BiInvertible
    open BiInvEquiv
    open BiInvOver

    glueBiInv : {x : X} {y : Y} (r : R x y) → BiInvEquiv (Word∞ (inl x)) (Word∞ (inr y))
    glueBiInv r = biInvEquiv (glue∞ r) (rinv∞ r) (norm-req∞ r) (linv∞ r) (norm-leq∞ r)

    glueBiInvOver : {x : X} {y : Y} (r : R x y) → BiInvOver (glueBiInv r) P P
    glueBiInvOver r = equivOver→BiInvOver (glueBiInv r) _ (equivP r)

    module Thin =
      ThinElim P baseP glueP
        (λ r → glueBiInvOver r .invl) (λ r → glueBiInvOver r .invr)
        (λ r → glueBiInvOver r .invl-leftInv) (λ r → glueBiInvOver r .invr-rightInv)

    elim : {a : X ⊎ Y} (w : Word∞ a) → P w
    elim = Thin.elim

    elimβ-[] : elim base∞ ≡ baseP
    elimβ-[] = refl

    elimβ-glue : {x : X} {y : Y} (r : R x y) (w : Word∞ (inl x)) → elim (glue∞ r w) ≡ glueP r _ (elim w)
    elimβ-glue = Thin.elimβ-glue
