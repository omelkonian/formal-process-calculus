--------------------------------------------------------------------------------
-- Express equivalence between non-deterministic process via canonical forms.

module 2-Canonical where

open import Function   using (_$_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat   using (ℕ; _≤?_; _≤_; _≰_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List  using (List; []; _∷_; [_]; _++_)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------
-- Processes

Label : Set
Label = ℕ

data Process : Set where

  -- termination
  ∅ : Process

  -- atomic action
  emit : Label → Process

  -- sequential composition
  _∶_ : Process → Process → Process

  -- parallel composition
  _∣_ : Process → Process → Process

infixr 5 _∶_
infixr 4 _∣_

--------------
-- Equivalence

-- merge two sorted lists
merge : List Label → List Label → List Label
merge []       ys       = ys
merge xs       []       = xs
merge (x ∷ xs) (y ∷ ys) with x ≤? y
... | yes _ = x ∷ merge xs (y ∷ ys)
... | no  _ = y ∷ merge (x ∷ xs) ys

-- T0D0 thats wrong for nested things like ((_ | _) : (_ | _))
--   * maybe disallow these by having [Process] instead of _|_
toCanonical : Process → List Label
toCanonical ∅        = []
toCanonical (emit l) = [ l ]
toCanonical (p ∶ q)  = toCanonical p ++ toCanonical q
toCanonical (p ∣ q)  = merge (toCanonical p) (toCanonical q)

infix 3 _≈_
_≈_ : Process → Process → Set
p ≈ q = toCanonical p ≡ toCanonical q

-- Properties

x≰y∧y≰x : ∀ {x y} → x ≰ y → y ≰ x → ⊥
x≰y∧y≰x x≰y y≰x = {!!}

x≤y∧y≤x⇒x≡y : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
x≤y∧y≤x⇒x≡y x≤y y≤x = {!!}

merge-commutative : ∀ {xs ys} → merge xs ys ≡ merge ys xs
merge-commutative {[]}     {[]}     = refl
merge-commutative {[]}     {y ∷ ys} = refl
merge-commutative {x ∷ xs} {[]}     = refl
merge-commutative {x ∷ xs} {y ∷ ys}
    with x ≤? y | y ≤? x
... | yes x≤y | no ¬y≤x = cong (x ∷_) (merge-commutative {xs} {y ∷ ys})
... | no ¬x≤y | yes y≤x = cong (y ∷_) (merge-commutative {x ∷ xs} {ys})
... | no ¬x≤y | no ¬y≤x = ⊥-elim (x≰y∧y≰x ¬x≤y ¬y≤x)
... | yes x≤y | yes y≤x
    with x≤y∧y≤x⇒x≡y x≤y y≤x
... | refl = cong (x ∷_) {!!}


∣-commutative : ∀ {P Q} → P ∣ Q ≈ Q ∣ P
∣-commutative {P} {Q}
  rewrite merge-commutative {toCanonical P} {toCanonical Q}
        = refl

-- Equivalence I: Identity
_ : emit 1 ∣ emit 21 ∶ emit 22
  ≈ emit 1 ∣ emit 21 ∶ emit 22
_ = refl

-- Equivalence II: Prepend ∅
_ : emit 1 ∣ emit 21 ∶ emit 22
  ≈ ∅ ∣ emit 1 ∣ emit 21 ∶ emit 22
_ = refl

-- Equivalence III: Nest differently
_ : emit 11 ∶ emit 12 ∶ emit 13 ∣ emit 21 ∶ emit 22 ∶ emit 23 ∣ emit 31 ∶ emit 32 ∶ emit 33
  ≈ ((emit 11 ∶ emit 12) ∶ emit 13 ∣ (emit 21 ∶ emit 22) ∶ emit 23) ∣ (emit 31 ∶ emit 32) ∶ emit 33
_ = refl

-- Equivalence IV: Commute _∣_
_ : emit 11 ∶ emit 12 ∶ emit 13 ∣ emit 21 ∶ emit 22 ∶ emit 23 ∣ emit 31 ∶ emit 32 ∶ emit 33
  ≈ emit 31 ∶ emit 32 ∶ emit 33 ∣ emit 21 ∶ emit 22 ∶ emit 23 ∣ emit 11 ∶ emit 12 ∶ emit 13
_ = refl

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

  [SEQ-L] : ∀ {P P′ Q l}

    → P —→⟦ l ⟧ P′
      --------------------
    → P ∶ Q —→⟦ l ⟧ P′ ∶ Q

  [SEQ-R] : ∀ {Q Q′ l}

    → Q —→⟦ l ⟧ Q′
      --------------------
    → ∅ ∶ Q —→⟦ l ⟧ Q′

  [STEP-L] : ∀ {P P′ Q l}

    → P —→⟦ l ⟧ P′
      --------------------
    → P ∣ Q —→⟦ l ⟧ P′ ∣ Q

  [STEP-R] : ∀ {P Q Q′ l}

    → Q —→⟦ l ⟧ Q′
      --------------------
    → P ∣ Q —→⟦ l ⟧ P ∣ Q′

  [EQUIV] : ∀ {P P′}  -- Loses 'uniqueness' of derivations

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

-- Derivation I: Simple parallel (in-order)
_ : emit 1 ∣ emit 2
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    ∅
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ just 1 ⟧⟨ [STEP-L] [EMIT] ⟩
    ∅ ∣ emit 2
  —→⟦ just 2 ⟧⟨ [STEP-R] [EMIT] ⟩
    ∅ ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

-- Derivation I': Simple parallel (out-of-order)
_ : emit 1 ∣ emit 2 —↠⟦ 2 ∷ 1 ∷ [] ⟧ ∅
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ just 2 ⟧⟨ [STEP-R] [EMIT] ⟩
    emit 1 ∣ ∅
  —→⟦ just 1 ⟧⟨ [STEP-L] [EMIT] ⟩
    ∅ ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

-- Derivation II: Multiple parallel (in-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅
_ =
  begin
    (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 1 ⟧⟨ [STEP-L] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 2 ⟧⟨ [STEP-R] $ [STEP-L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 3 ⟧⟨ [STEP-R] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

-- Derivation II': Multiple parallel (out-of-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 2 ∷ 1 ∷ 3 ∷ [] ⟧
    ∅
_ =
  begin
    (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 2 ⟧⟨ [STEP-R] $ [STEP-L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 1 ⟧⟨ [STEP-L] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 3 ⟧⟨ [STEP-R] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

-- Derivation III: Simple sequential
_ : emit 1 ∶ emit 2
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    ∅
_ = begin
      emit 1 ∶ emit 2
    —→⟦ just 1 ⟧⟨ [SEQ-L] [EMIT] ⟩
      ∅ ∶ emit 2
    —→⟦ just 2 ⟧⟨ [SEQ-R] [EMIT] ⟩
      ∅
    ∎

-- Derivation IV: Multiple sequential
_ : (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
   —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅
_ = begin
      (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
      emit 1 ∶ emit 2 ∶ emit 3
    —→⟦ just 1 ⟧⟨ [SEQ-L] [EMIT] ⟩
      ∅ ∶ emit 2 ∶ emit 3
    —→⟦ just 2 ⟧⟨ [SEQ-R] $ [SEQ-L] [EMIT] ⟩
      ∅ ∶ emit 3
    —→⟦ just 3 ⟧⟨ [SEQ-R] [EMIT] ⟩
      ∅
    ∎

-- Derivation V: Simple sequential+parallel (in-order)
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
  —→⟦ just 11 ⟧⟨ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅       ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 12 ⟧⟨ [STEP-L] $ [SEQ-R] [EMIT] ⟩
      ∅
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 21 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅
    ∣ ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 22 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-R] [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ emit 31 ∶ emit 32
  —→⟦ just 31 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-L] [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ just 32 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-R] [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

-- Derivation V': Simple sequential+parallel (out-of-order)
_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ 21 ∷ 31 ∷ 22 ∷ 11 ∷ 12 ∷ 32 ∷ [] ⟧
    ∅
_ =
  begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 21 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      emit 11 ∶ emit 12
    ∣ ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 31 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-L] [EMIT] ⟩
      emit 11 ∶ emit 12
    ∣ ∅       ∶ emit 22
    ∣ ∅       ∶ emit 32
  —→⟦ just 22 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-R] [EMIT] ⟩
      emit 11 ∶ emit 12
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ just 11 ⟧⟨ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅       ∶ emit 12
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ just 12 ⟧⟨ [STEP-L] $ [SEQ-R] [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ just 32 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-R] [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅
  —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
    ∅
  ∎

-- Derivation VI: Complex sequential+parallel
_ : ( emit 1
    ∣ emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —↠⟦ 11 ∷ 1 ∷ 12 ∷ 21 ∷ 2 ∷ 22 ∷ [] ⟧
    ∅
_ = begin
      ( emit 1
      ∣ emit 11 ∶ emit 12 )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ just 11 ⟧⟨ [SEQ-L] $ [STEP-R] $ [SEQ-L] [EMIT] ⟩
      ( emit 1
      ∣ ∅ ∶ emit 12 )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ just 1 ⟧⟨ [SEQ-L] $ [STEP-L] [EMIT] ⟩
      ( ∅
      ∣ ∅ ∶ emit 12 )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ just 12 ⟧⟨ [SEQ-L] $ [STEP-R] $ [SEQ-R] [EMIT] ⟩
      ( ∅ ∣ ∅ )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
      emit 21 ∶ emit 22
    ∣ emit 2
    —→⟦ just 21 ⟧⟨ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅ ∶ emit 22
    ∣ emit 2
    —→⟦ just 2 ⟧⟨ [STEP-R] [EMIT] ⟩
      ∅ ∶ emit 22
    ∣ ∅
    —→⟦ just 22 ⟧⟨ [STEP-L] $ [SEQ-R] [EMIT] ⟩
      ∅ ∣ ∅
    —→⟦ nothing ⟧⟨ [EQUIV] refl ⟩
      ∅
    ∎
