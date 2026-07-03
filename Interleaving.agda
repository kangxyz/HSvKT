{-

The Higher Seifert-van Kampen Theorem

-}
{-# OPTIONS --safe --cubical --lossy-unification #-}
module Interleaving where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sum hiding (elim ; map)
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Utils.Coherence
open import HSvKT


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level


module _
  (X : Type ℓ) (Y : Type ℓ')
  (R : X → Y → Type ℓ'')
  (a₀ : X ⊎ Y)
  where

  open Sequence
  open WordConstruction X Y R a₀

  data WordRed : ℕ → X ⊎ Y → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    shift : {n : ℕ} {a : X ⊎ Y} → WordRed n a → WordRed (suc n) a
    base  : WordRed 0 a₀
    left  : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → WordRed n (inl x) → WordRed n (inr y)
    right : {n : ℕ} {x : X} {y : Y} (r : R x y)
      → WordRed n (inr y) → WordRed (suc n) (inl x)
    leq   : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : WordRed n (inl x)) → right r (left r w) ≡ shift w
    req   : {n : ℕ} {x : X} {y : Y} (r : R x y)
      (w : WordRed n (inr y)) → left r (right r w) ≡ shift w

  {- to : {n : ℕ} {a : X ⊎ Y} → Word n a → WordRed (suc n) a
  to (shift w) = shift (to w)
  to base = base
  to (glue r w) = shift (left r (to w))
  to (linv r w) = right r (to w)
  to (rinv r w) = right r (to w)
  to (leq r w i) = (cong shift (leq r (to w)) ∙ {! !}) i
  to (req r w i) = {! !} -}

  comm-left : {n : ℕ} {x : X} {y : Y} (w : WordRed n (inl x)) (r : R x y) → shift (left r w) ≡ left r (shift w)
  comm-left = {! !}

  comm-right : {n : ℕ} {x : X} {y : Y} (w : WordRed n (inr y)) (r : R x y) → shift (right r w) ≡ right r (shift w)
  comm-right = {! !}


  {- to : {n : ℕ} {a : X ⊎ Y} → Word n a → WordRed n a
  to (shift w) = shift (to w)
  to base = base
  to (glue r w) = shift (left r (to w))
  to (linv r w) = right r (to w)
  to (rinv r w) = right r (to w)
  to (leq r w i) = {! !}
  to (req r w i) = shift (req r (to w) i) -}

  from : {n : ℕ} {a : X ⊎ Y} → WordRed n a → Word n a
  from (shift w) = shift (from w)
  from base = base
  from (left r w) = glue (from w)


