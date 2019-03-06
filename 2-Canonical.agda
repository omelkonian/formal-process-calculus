--------------------------------------------------------------------------------
-- Express equivalence between non-deterministic process via canonical forms.

module 2-Canonical where

open import Function   using (_$_)
open import Data.Nat   using (ℕ; _≤?_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List  using (List; []; _∷_; [_]; _++_)

open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------
-- Processes

Label : Set
Label = ℕ

data Process : Set where

  -- termination
  ∅ : Process

  -- atomic action
  emit : Label → Process

  -- sequential composition (leave out for now)
  _∶_ : Process → Process → Process

  -- parallel composition
  _∣_ : Process → Process → Process

infixr 5 _∶_
infixr 4 _∣_

toCanonical : Process → List Label
toCanonical ∅        = []
toCanonical (emit l) = [ l ]
toCanonical (p ∶ q)  = toCanonical p ++ toCanonical q
toCanonical (p ∣ q)  = merge (toCanonical p) (toCanonical q)
  where
    -- merge two sorted lists
    merge : List Label → List Label → List Label
    merge []       ys       = ys
    merge xs       []       = xs
    merge (x ∷ xs) (y ∷ ys) with x ≤? y
    ... | yes _ = x ∷ merge xs (y ∷ ys)
    ... | no  _ = y ∷ merge (x ∷ xs) ys

--------------
-- Equivalence

_≈_ : Process → Process → Set
p ≈ q = toCanonical p ≡ toCanonical q

------------
-- Semantics

infix  3 _—→⟦_⟧_
infix  2 _—↠⟦_⟧_

infix  1 begin_
infixr 2 _—→⟦_⟧⟨_⟩_
infix  3 _∎

data _—→⟦_⟧_ : Process → Maybe Label → Process → Set where

  [EMIT] : ∀ {l}

      ---------------------
    → emit l —→⟦ just l ⟧ ∅

  [SEQ_L] : ∀ {P P′ Q l}

    → P —→⟦ l ⟧ P′
      --------------------
    → P ∶ Q —→⟦ l ⟧ P′ ∶ Q

  [SEQ_R] : ∀ {Q Q′ l}

    → Q —→⟦ l ⟧ Q′
      --------------------
    → ∅ ∶ Q —→⟦ l ⟧ ∅ ∶ Q′

  [STEP_L] : ∀ {P P′ Q l}

    → P —→⟦ l ⟧ P′
      --------------------
    → P ∣ Q —→⟦ l ⟧ P′ ∣ Q

  [STEP_R] : ∀ {P Q Q′ l}

    → Q —→⟦ l ⟧ Q′
      --------------------
    → P ∣ Q —→⟦ l ⟧ P ∣ Q′

  [EQUIV] : ∀ {P P′}

    → P ≈ P′
      ------------------
    → P —→⟦ nothing ⟧ P′


_∷ₘ_ : ∀ {A : Set} → Maybe A → List A → List A
nothing ∷ₘ xs = xs
just x  ∷ₘ xs = x ∷ xs

data _—↠⟦_⟧_ : Process → List Label → Process → Set where

  _∎ : ∀ (P : Process)
      -------------
    → P —↠⟦ [] ⟧ P

  _—→⟦_⟧⟨_⟩_ : ∀ {Q R ls}
    → (P : Process)
    → (l : Maybe Label)
    → P —→⟦ l  ⟧ Q
    → Q —↠⟦ ls ⟧ R
      -----------------
    → P —↠⟦ l ∷ₘ ls ⟧ R

begin_ : ∀ {P Q ls}
  → P —↠⟦ ls ⟧ Q
    -------------
  → P —↠⟦ ls ⟧ Q
begin P—↠Q = P—↠Q

_ : emit 1 ∣ emit 2 —↠⟦ 1 ∷ 2 ∷ [] ⟧ ∅
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ just 1 ⟧⟨ [STEP_L] [EMIT] ⟩
    ∅ ∣ emit 2
  —→⟦ just 2 ⟧⟨ [STEP_R] [EMIT] ⟩
    ∅ ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

_ : emit 1 ∣ emit 2 —↠⟦ 2 ∷ 1 ∷ [] ⟧ ∅
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ just 2 ⟧⟨ [STEP_R] [EMIT] ⟩
    emit 1 ∣ ∅
  —→⟦ just 1 ⟧⟨ [STEP_L] [EMIT] ⟩
    ∅ ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    emit 3
_ =
  begin
    (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 1 ⟧⟨ [STEP_L] $ [STEP_R] $ [STEP_R] $ [STEP_L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 2 ⟧⟨ [STEP_R] $ [STEP_L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    emit 3
  ∎

_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ 11 ∷ 12 ∷ 21 ∷ 22 ∷ 31 ∷ 32 ∷ [] ⟧
    ∅
_ =
  begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 11 ⟧⟨ [STEP_L] $ [SEQ_L] [EMIT] ⟩
      ∅       ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 12 ⟧⟨ [STEP_L] $ [SEQ_R] [EMIT] ⟩
      ∅       ∶ ∅
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 21 ⟧⟨ [STEP_R] $ [STEP_L] $ [SEQ_L] [EMIT] ⟩
      ∅       ∶ ∅
    ∣ ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 22 ⟧⟨ [STEP_R] $ [STEP_L] $ [SEQ_R] [EMIT] ⟩
      ∅       ∶ ∅
    ∣ ∅       ∶ ∅
    ∣ emit 31 ∶ emit 32
  —→⟦ just 31 ⟧⟨ [STEP_R] $ [STEP_R] $ [SEQ_L] [EMIT] ⟩
      ∅       ∶ ∅
    ∣ ∅       ∶ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ just 32 ⟧⟨ [STEP_R] $ [STEP_R] $ [SEQ_R] [EMIT] ⟩
      ∅       ∶ ∅
    ∣ ∅       ∶ ∅
    ∣ ∅       ∶ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎
