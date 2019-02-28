module ProcessCalculus where

open import Data.Nat  using (ℕ)
open import Data.List using (List; []; _∷_; [_]; _++_)



Label : Set
Label = ℕ

data Process : Set where

  -- termination
  ∅ : Process

  -- atomic action
  emit : Label → Process

  -- sequential composition (leave out for now)
  -- _∶_ : Process → Process → Process

  -- parallel composition
  _∣_ : Process → Process → Process

infixr 4 _∣_

-----------------------------------------------
-- 0. Simple

module Simple where

  infix  2 _—→⟦_⟧_
  infix  2 _—↠⟦_⟧_

  infix  1 begin_
  infixr 2 _—→⟦_⟧⟨_⟩_
  infix  3 _∎


  data _—→⟦_⟧_ : Process → List Label → Process → Set where

    [EMIT] : ∀ {l : Label}

        -----------------
      → emit l —→⟦ [ l ] ⟧ ∅

    [STEP_L] : ∀ {P P′ Q : Process} {ls : List Label}

      → P —→⟦ ls ⟧ P′
        ----------------------
      → P ∣ Q —→⟦ ls ⟧ P′ ∣ Q

    [STOP_L] : ∀ {Q : Process}

        -----------------
      → ∅ ∣ Q —→⟦ [] ⟧ Q

    [STEP_R] : ∀ {P Q Q′ : Process} {ls : List Label}

      → Q —→⟦ ls ⟧ Q′
        ----------------------
      → P ∣ Q —→⟦ ls ⟧ P ∣ Q′

    [STOP_R] : ∀ {P : Process}

        -----------------
      → P ∣ ∅ —→⟦ [] ⟧ P

  data _—↠⟦_⟧_ : Process → List Label → Process → Set where

    _∎ : ∀ (P : Process)

        -------------
      → P —↠⟦ [] ⟧ P

    _—→⟦_⟧⟨_⟩_ : ∀ {Q R : Process} {ls′ : List Label}
      → (P : Process)
      → (ls : List Label)
      → P —→⟦ ls  ⟧ Q
      → Q —↠⟦ ls′ ⟧ R
        --------------------
      → P —↠⟦ ls ++ ls′ ⟧ R

  begin_ : ∀ {P Q : Process} {ls : List Label}
    → P —↠⟦ ls ⟧ Q
      -------------
    → P —↠⟦ ls ⟧ Q
  begin P—↠Q = P—↠Q

  _ :  emit 1 ∣ emit 2
     —↠⟦ 1 ∷ 2 ∷ [] ⟧
       ∅
  _ = begin
        emit 1 ∣ emit 2
      —→⟦ [ 1 ] ⟧⟨ [STEP_L] [EMIT] ⟩
        ∅ ∣ emit 2
      —→⟦ [] ⟧⟨ [STOP_L] ⟩
        emit 2
      —→⟦ [ 2 ] ⟧⟨ [EMIT] ⟩
        ∅
      ∎

  _ :  emit 1 ∣ emit 2
     —↠⟦ 2 ∷ 1 ∷ [] ⟧
       ∅
  _ = begin
        emit 1 ∣ emit 2
      —→⟦ [ 2 ] ⟧⟨ [STEP_R] [EMIT] ⟩
        emit 1 ∣ ∅
      —→⟦ [] ⟧⟨ [STOP_R] ⟩
        emit 1
      —→⟦ [ 1 ] ⟧⟨ [EMIT] ⟩
        ∅
      ∎

  open import Function using (_$_)
  open import Data.Nat using (zero; suc; _+_)
  open import Data.List using (map; upTo; length; concat; concatMap)

  open import Relation.Binary.PropositionalEquality             using (_≡_; refl; setoid)
  open import Data.List.Membership.Setoid (setoid (List Label)) using (_∈_)
  open import Data.List.Relation.Permutation.Inductive          using (_↭_)

  insert : ∀ {A : Set} → A → List A → ℕ → List A
  insert y xs       zero    = y ∷ xs
  insert y []       (suc n) = [ y ]
  insert y (x ∷ xs) (suc n) = x ∷ insert y xs n

  insertNonDet : ∀ {A : Set} → A → List A → List (List A)
  insertNonDet x xs = map (insert x xs) (upTo $ length xs + 1)

  _ : insertNonDet 1 [] ≡ [ [ 1 ] ]
  _ = refl

  _ : insertNonDet 1 [ 2 ] ≡ (1 ∷ 2 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ []
  _ = refl

  interleave : ∀ {A : Set} → List A → List A → List (List A)
  interleave []       ys = [ ys ]
  interleave (x ∷ xs) ys = concatMap (insertNonDet x) (interleave xs ys)

  _ : interleave [ 1 ]  [ 2 ] ≡ (1 ∷ 2 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ []
  _ = refl

  _ : interleave [ 1 ]  (2 ∷ 3 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
                                     ∷ (2 ∷ 1 ∷ 3 ∷ [])
                                     ∷ (2 ∷ 3 ∷ 1 ∷ [])
                                     ∷ []
  _ = refl

  interleave′ : ∀ {A : Set} → List (List A) → List (List A) → List (List A)
  interleave′ xss yss =
    let t = map (λ ys → map (interleave ys) xss) yss -- ∈ List³ A
    in  concat $ concat t

  -- _ : interleave′ [] [ [ 1 ] ] ≡ [ [ 1 ] ]
  -- _ = refl

  -- _ : interleave′ ([ [ 1 ] ]) ([]) ≡ [ [ 1 ] ]
  -- _ = refl

  run : Process → List (List Label)
  run ∅        = [ [] ]
  run (emit x) = [ [ x ] ]
  run (P ∣ Q)  = interleave′ (run P) (run Q)

  _ : run (emit 1) ≡ [ [ 1 ] ]
  _ = refl

  -- _ : run (emit 1 ∣ emit 2) ≡ (1 ∷ 2 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ []
  -- _ = refl

  run-sound : ∀ {P : Process} {ls : List Label}
    → ls ∈ run P
      -------------
    → P —↠⟦ ls ⟧ ∅
  run-sound = {!!}

  run-complete : ∀ {P : Process} {ls : List Label}
    → P —↠⟦ ls ⟧ ∅
      -------------
    → ls ∈ run P
  run-complete = {!!}

  _≈_ : Process → Process → Set
  P ≈ Q = run P ↭ run Q

-----------------------------------------------
-- 1. Schedulers

module Schedulers where

-----------------------------------------------
-- 2. Canonical forms

module Canonical where

-----------------------------------------------
-- 3. Relational specification (list results)

module RelSpec where

-----------------------------------------------
-- 4. Weakening

module Weakening where
