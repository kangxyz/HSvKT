{-

The Coherence Machine

-}
{-# OPTIONS --safe --cubical --guardedness #-}
module Utils.Coherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Nat hiding (elim)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit hiding (elim)
open import Utils.ShiftAlgebra
  renaming (shift∞ to S-shift∞ ; push∞  to S-push∞
          ; elim₀  to S-elim₀  ; elim   to S-elim)

private
  variable
    ℓ ℓ' ℓA ℓB : Level

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


module Coh
  (X : Sequence ℓ)
  where

  open Sequence X


  module _ {n : ℕ} (x : obj n) where

    solve₀ : {m : ℕ} → Word m → obj (m + n)
    solve₀  base     = x
    solve₀ (shift w) = map (solve₀ w)

    solve : Word∞ → SeqColim X
    solve (incl w)   = incl (solve₀ w)
    solve (push w i) = push (solve₀ w) i


  shift∞ : SeqColim X → SeqColim X
  shift∞ (incl w)   = incl (map w)
  shift∞ (push w 𝓲) = push (map w) 𝓲

  push∞ : (w : SeqColim X) → w ≡ shift∞ w
  push∞ (incl w)     = push w
  push∞ (push w 𝓲) j = solve w (S-push∞ (push base 𝓲) j)

  pushCoh-shift : {n : ℕ} (x : obj n) (𝓲 𝓳 : I) → SeqColim X
  pushCoh-shift x 𝓲 𝓳 = push (map x) 𝓲

  pushCoh-shift-filler : {n : ℕ} (x : obj n) (𝓲 𝓳 𝓴 : I) → SeqColim X
  pushCoh-shift-filler x 𝓲 𝓳 𝓴 = pushCoh-shift x 𝓲 (𝓳 ∧ 𝓴)


  comm-shift : {n : ℕ} (w : obj n) → map (map w) ≡ map (map w)
  comm-shift w = refl

  comm-shift-shift-filler : {n : ℕ} (w : obj n) (𝓲 𝓳 : I) → obj (3 + n)
  comm-shift-shift-filler w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → map (map (map w))
      ; (𝓲 = i1) → map (comm-shift w 𝓳) })
      (inS (comm-shift (map w) 𝓲))


  comm-shift-filler : {n : ℕ} (w : obj n) (𝓲 𝓳 : I) → obj (2 + n)
  comm-shift-filler w 𝓲 =
    hfill (λ 𝓳 → λ
      { (𝓲 = i0) → map (map w)
      ; (𝓲 = i1) → comm-shift w 𝓳 })
      (inS (comm-shift w 𝓲))


  comm-shift-shift : {n : ℕ} (w : obj n) → map (map (map w)) ≡ map (map (map w))
  comm-shift-shift w 𝓲 = comm-shift-shift-filler w 𝓲 i1

  pushCoh-shift-shift-filler : {n : ℕ} (w : obj n) (𝓲 𝓳 𝓴 : I) → SeqColim X
  pushCoh-shift-shift-filler w 𝓲 𝓳 =
    fill (λ _ → SeqColim X) (λ 𝓴 → λ
      { (𝓲 = i0) → incl (map (map w))
      ; (𝓲 = i1) → incl (comm-shift-shift-filler w 𝓳 𝓴)
      ; (𝓳 = i0) → push (map (map w)) 𝓲
      ; (𝓳 = i1) → shift∞ (pushCoh-shift w 𝓲 𝓴) })
      (inS (pushCoh-shift (map w) 𝓲 𝓳))

  pushCoh-shift-shift : {n : ℕ} (w : obj n) (𝓲 𝓳 : I) → SeqColim X
  pushCoh-shift-shift w 𝓲 𝓳 = pushCoh-shift-shift-filler w 𝓲 𝓳 i1

  push²-filler : (w : SeqColim X) (i j : I) → SeqColim X
  push²-filler w i j = compPath-filler (push∞ w) (push∞ _) i j

  push²∞ : (w : SeqColim X) → w ≡ shift∞ (shift∞ w)
  push²∞ w i = push²-filler w i1 i


  module CohP
    (P : SeqColim X → Type ℓ')
    (shiftP : (x : SeqColim X) → P x → P (shift∞ x))
    (pushP  : (x : SeqColim X) (p : P x) → PathP (λ i → P (push∞ x i)) p (shiftP _ p))
    where


    module _ {n : ℕ} (x : obj n) (p : P (incl x)) where

      solveP : {w : Word∞} (q : WordP∞ w) → P (solve x w)
      solveP  base = p
      solveP (shift₀ _    q) = shiftP _ (solveP q)
      solveP (shift₁ _  i q) = shiftP _ (solveP q)
      solveP (push₀ _   q i) = pushP  _ (solveP q) i
      solveP (push₁ _ j q i) = pushP  _ (solveP q) i


    pushCohP-shift : {n : ℕ} (x : obj n) (p : P (incl x))
      → SquareP (λ 𝓲 𝓳 → P (pushCoh-shift x 𝓲 𝓳))
          refl refl (pushP _ (shiftP _ p)) (λ i → shiftP _ (pushP _ p i))
    pushCohP-shift x p i j = solveP x p (pushCohP-shift-square i j)

    push²P : (x : SeqColim X) (p : P x) → PathP (λ i → P (push²∞ x i)) p (shiftP _ (shiftP _ p))
    push²P x p i =
      comp (λ j → P (push²-filler x j i)) (λ j → λ
        { (i = i0) → p
        ; (i = i1) → pushP _ (shiftP _ p) j })
        (pushP _ p i)

    pushCohP-shift-shift-filler : {n : ℕ} (w : obj n) (p : P (incl w))
      (𝓲 𝓳 𝓴 : I) → P (pushCoh-shift-shift-filler w 𝓲 𝓳 𝓴)
    pushCohP-shift-shift-filler w p 𝓲 𝓳 =
      fill (λ 𝓴 → P (pushCoh-shift-shift-filler w 𝓲 𝓳 𝓴)) (λ 𝓴 → λ
        { (𝓲 = i0) → shiftP _ (shiftP _ p)
    --  ; (𝓲 = i1) → incl (compPath-filler _ _ 𝓴 𝓳)
        ; (𝓳 = i0) → pushP _ (shiftP _ (shiftP _ p)) 𝓲
        ; (𝓳 = i1) → shiftP _ (pushCohP-shift w p 𝓲 𝓴) })
        (inS (pushCohP-shift _ (shiftP _ p) 𝓲 𝓳))

    pushCohP-shift-shift : {n : ℕ} (w : obj n) (p : P (incl w))
      (𝓲 𝓳 : I) → P (pushCoh-shift-shift w 𝓲 𝓳)
    pushCohP-shift-shift w p 𝓲 𝓳 = pushCohP-shift-shift-filler w p 𝓲 𝓳 i1
