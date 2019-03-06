--------------------------------------------------------------------------------
-- Straight-forward model, equivalence via permutation of lists.

module 0-Simple where

open import Function  using (_$_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; T; true; false; _∧_)
open import Data.Nat  using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.List using (List; []; _∷_; [_]; _++_)

------------
-- Processes

Label : Set
Label = ℕ

Trace : Set
Trace = List Label

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

hasTerminated : Process → Bool
hasTerminated ∅        = true
hasTerminated (emit _) = false
hasTerminated (P ∶ Q)  = hasTerminated P ∧ hasTerminated Q
hasTerminated (P ∣ Q)  = hasTerminated P ∧ hasTerminated Q

-----------------------
-- Small-step semantics

infix  2 _—→⟦_⟧_
infix  2 _—↠⟦_⟧_

infix  1 begin_
infixr 2 _—→⟦_⟧⟨_⟩_
infix  3 _∎


data _—→⟦_⟧_ : Process → Label → Process → Set where

  [EMIT] : ∀ {l}

      -----------------
    → emit l —→⟦ l ⟧ ∅

  [SEQ-L] : ∀ {P P′ Q l}

    → P —→⟦ l ⟧ P′
      --------------------
    → P ∶ Q —→⟦ l ⟧ P′ ∶ Q

  [SEQ-R] : ∀ {P Q Q′ l}
    → T (hasTerminated P)
    → Q —→⟦ l ⟧ Q′
      ----------------
    → P ∶ Q —→⟦ l ⟧ Q′

  [STEP-L] : ∀ {P P′ Q l}

    → P —→⟦ l ⟧ P′
      --------------------
    → P ∣ Q —→⟦ l ⟧ P′ ∣ Q

  [STEP-R] : ∀ {P Q Q′ l}

    → Q —→⟦ l ⟧ Q′
      --------------------
    → P ∣ Q —→⟦ l ⟧ P ∣ Q′

data _—↠⟦_⟧_ : Process → Trace → Process → Set where

  _∎ : ∀ (P : Process)

      -------------
    → P —↠⟦ [] ⟧ P

  _—→⟦_⟧⟨_⟩_ : ∀ {Q R ls}
    → (P : Process)
    → (l : Label)
    → P —→⟦ l  ⟧ Q
    → Q —↠⟦ ls ⟧ R
      --------------------
    → P —↠⟦ l ∷ ls ⟧ R

begin_ : ∀ {P Q : Process} {ls : Trace}
  → P —↠⟦ ls ⟧ Q
    -------------
  → P —↠⟦ ls ⟧ Q
begin P—↠Q = P—↠Q

-- Derivation I: Simple parallel
_ :  emit 1 ∣ emit 2
   —↠⟦ 1 ∷ 2 ∷ [] ⟧
     ∅ ∣ ∅
_ = begin
      emit 1 ∣ emit 2
    —→⟦ 1 ⟧⟨ [STEP-L] [EMIT] ⟩
      ∅ ∣ emit 2
    —→⟦ 2 ⟧⟨ [STEP-R] [EMIT] ⟩
      ∅ ∣ ∅
    ∎

-- Derivation II: Multiple parallel (in-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
_ = begin
      (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 1 ⟧⟨ [STEP-L] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 2 ⟧⟨ [STEP-R] $ [STEP-L] [EMIT] ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 3 ⟧⟨ [STEP-R] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
    ∎

-- Derivation II': Multiple parallel (out-of-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 2 ∷ 1 ∷ 3 ∷ [] ⟧
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
_ = begin
      (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 2 ⟧⟨ [STEP-R] $ [STEP-L] [EMIT] ⟩
      (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 1 ⟧⟨ [STEP-L] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 3 ⟧⟨ [STEP-R] $ [STEP-R] $ [STEP-R] $ [STEP-L] [EMIT] ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
    ∎

-- Derivation III: Simple sequential
_ : emit 1 ∶ emit 2
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    ∅
_ = begin
      emit 1 ∶ emit 2
    —→⟦ 1 ⟧⟨ [SEQ-L] [EMIT] ⟩
      ∅ ∶ emit 2
    —→⟦ 2 ⟧⟨ [SEQ-R] tt [EMIT] ⟩
      ∅
    ∎

-- Derivation IV: Multiple sequential
_ : (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
   —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅ ∶ ∅
_ = begin
      (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ 1 ⟧⟨ [SEQ-L] $ [SEQ-R] tt $ [SEQ-R] tt $ [SEQ-L] [EMIT] ⟩
      (∅ ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ 2 ⟧⟨ [SEQ-R] tt $ [SEQ-L] [EMIT] ⟩
      ∅ ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ 3 ⟧⟨ [SEQ-R] tt $ [SEQ-R] tt $ [SEQ-L] [EMIT] ⟩
      ∅ ∶ ∅
    ∎

-- Derivation V: Simple sequential+parallel (in-order)
_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ 11 ∷ 12 ∷ 21 ∷ 22 ∷ 31 ∷ 32 ∷ [] ⟧
    ∅
  ∣ ∅
  ∣ ∅
_ = begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
    —→⟦ 11 ⟧⟨ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅       ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
    —→⟦ 12 ⟧⟨ [STEP-L] $ [SEQ-R] tt [EMIT] ⟩
      ∅
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
    —→⟦ 21 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅
    ∣ ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
    —→⟦ 22 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-R] tt [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ emit 31 ∶ emit 32
    —→⟦ 31 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-L] [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅       ∶ emit 32
    —→⟦ 32 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-R] tt [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅
    ∎

-- Derivation V': Simple sequential+parallel (out-of-order)
_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ 21 ∷ 31 ∷ 22 ∷ 11 ∷ 12 ∷ 32 ∷ [] ⟧
    ∅
  ∣ ∅
  ∣ ∅
_ = begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
    —→⟦ 21 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      emit 11 ∶ emit 12
    ∣ ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
    —→⟦ 31 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-L] [EMIT] ⟩
      emit 11 ∶ emit 12
    ∣ ∅       ∶ emit 22
    ∣ ∅       ∶ emit 32
    —→⟦ 22 ⟧⟨ [STEP-R] $ [STEP-L] $ [SEQ-R] tt [EMIT] ⟩
      emit 11 ∶ emit 12
    ∣ ∅
    ∣ ∅       ∶ emit 32
    —→⟦ 11 ⟧⟨ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅       ∶ emit 12
    ∣ ∅
    ∣ ∅       ∶ emit 32
    —→⟦ 12 ⟧⟨ [STEP-L] $ [SEQ-R] tt [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅       ∶ emit 32
    —→⟦ 32 ⟧⟨ [STEP-R] $ [STEP-R] $ [SEQ-R] tt [EMIT] ⟩
      ∅
    ∣ ∅
    ∣ ∅
    ∎

-- Derivation VI: Complex sequential+parallel
_ : ( emit 1
    ∣ emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —↠⟦ 11 ∷ 1 ∷ 12 ∷ 21 ∷ 2 ∷ 22 ∷ [] ⟧
    ∅ ∣ ∅
_ = begin
      ( emit 1
      ∣ emit 11 ∶ emit 12 )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ 11 ⟧⟨ [SEQ-L] $ [STEP-R] $ [SEQ-L] [EMIT] ⟩
      ( emit 1
      ∣ ∅ ∶ emit 12 )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ 1 ⟧⟨ [SEQ-L] $ [STEP-L] [EMIT] ⟩
      ( ∅
      ∣ ∅ ∶ emit 12 )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ 12 ⟧⟨ [SEQ-L] $ [STEP-R] $ [SEQ-R] tt [EMIT] ⟩
      ( ∅ ∣ ∅ )
    ∶ ( emit 21 ∶ emit 22
      ∣ emit 2 )
    —→⟦ 21 ⟧⟨ [SEQ-R] tt $ [STEP-L] $ [SEQ-L] [EMIT] ⟩
      ∅ ∶ emit 22
    ∣ emit 2
    —→⟦ 2 ⟧⟨ [STEP-R] [EMIT] ⟩
      ∅ ∶ emit 22
    ∣ ∅
    —→⟦ 22 ⟧⟨ [STEP-L] $ [SEQ-R] tt [EMIT] ⟩
      ∅ ∣ ∅
    ∎

------------------------------------
-- Equivalence relation on processes

open import Function using (_$_)
open import Data.Nat using (zero; suc; _+_)
open import Data.List using (map; upTo; length; concat; concatMap)

open import Relation.Binary.PropositionalEquality      using (_≡_; refl; setoid)
open import Data.List.Membership.Setoid (setoid Trace) using (_∈_)
open import Data.List.Relation.Permutation.Inductive   using (_↭_)

insert : ∀ {A : Set} → A → List A → ℕ → List A
insert y xs       zero    = y ∷ xs
insert y []       (suc n) = [ y ]
insert y (x ∷ xs) (suc n) = x ∷ insert y xs n

insertNonDet : ∀ {A : Set} → A → List A → List (List A)
insertNonDet x xs = map (insert x xs) (upTo $ length xs + 1)

interleave : ∀ {A : Set} → List A → List A → List (List A)
interleave []       ys       = [ ys ]
interleave xs       []       = [ xs ]
interleave (x ∷ xs) (y ∷ ys) = map (x ∷_) (interleave xs (y ∷ ys))
                            ++ map (y ∷_) (interleave (x ∷ xs) ys)

run : Process → List Trace
run ∅        = [ [] ]
run (emit x) = [ [ x ] ]
run (P ∣ Q)  = concatMap (λ xs → concatMap (λ ys → interleave xs ys) (run Q)) (run P)
run (P ∶ Q)  = concatMap (λ xs → map (λ ys → xs ++ ys) (run Q)) (run P)

_ : run (emit 1) ≡ [ [ 1 ] ]
_ = refl

_ : run (emit 1 ∣ emit 2) ≡ (1 ∷ 2 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ []
_ = refl

_ : run (∅ ∣ emit 1 ∣ emit 2) ≡ (1 ∷ 2 ∷ []) ∷ (2 ∷ 1 ∷ []) ∷ []
_ = refl

_ : run ( emit 11 ∶ emit 12
        ∣ emit 21 ∶ emit 22 )
      ≡ (11 ∷ 12 ∷ 21 ∷ 22 ∷ [])
      ∷ (11 ∷ 21 ∷ 12 ∷ 22 ∷ [])
      ∷ (11 ∷ 21 ∷ 22 ∷ 12 ∷ [])
      ∷ (21 ∷ 11 ∷ 12 ∷ 22 ∷ [])
      ∷ (21 ∷ 11 ∷ 22 ∷ 12 ∷ [])
      ∷ (21 ∷ 22 ∷ 11 ∷ 12 ∷ [])
      ∷ []
_ = refl

run-sound : ∀ {P : Process} {ls : Trace}
  → ls ∈ run P
    -------------
  → P —↠⟦ ls ⟧ ∅
run-sound = {!!}

run-complete : ∀ {P : Process} {ls : Trace}
  → P —↠⟦ ls ⟧ ∅
    -------------
  → ls ∈ run P
run-complete = {!!}

infix 2 _≈_
_≈_ : Process → Process → Set
P ≈ Q = run P ↭ run Q

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness; True)
open import Relation.Binary  using (Decidable)

_≟_ : Decidable {A = Trace} _≡_
[] ≟ [] = yes refl
[] ≟ (x ∷ ys) = no (λ ())
(x ∷ xs) ≟ [] = no (λ ())
(x ∷ xs) ≟ (y ∷ ys) with x ≟ℕ y
... | no ¬p = no (λ{ refl → ¬p refl })
... | yes refl with xs ≟ ys
... | no ¬p = no (λ{ refl → ¬p refl })
... | yes refl = yes refl

open import Data.Set' _≟_ using (sound-↭)

-- Equivalence I: Identity
_ : emit 1 ∣ emit 21 ∶ emit 22
  ≈ emit 1 ∣ emit 21 ∶ emit 22
_ = sound-↭

-- Equivalence II: Prepend ∅
_ : emit 1 ∣ emit 21 ∶ emit 22
  ≈ ∅ ∣ emit 1 ∣ emit 21 ∶ emit 22
_ = sound-↭

-- Equivalence III: Nest differently
_ : emit 11 ∶ emit 12 ∶ emit 13 ∣ emit 21 ∶ emit 22 ∶ emit 23 ∣ emit 31 ∶ emit 32 ∶ emit 33
  ≈ ((emit 11 ∶ emit 12) ∶ emit 13 ∣ (emit 21 ∶ emit 22) ∶ emit 23) ∣ (emit 31 ∶ emit 32) ∶ emit 33
_ = sound-↭

-- Equivalence IV: Commute _∣_
_ : emit 11 ∶ emit 12 ∶ emit 13 ∣ emit 21 ∶ emit 22 ∶ emit 23 ∣ emit 31 ∶ emit 32 ∶ emit 33
  ≈ emit 31 ∶ emit 32 ∶ emit 33 ∣ emit 21 ∶ emit 22 ∶ emit 23 ∣ emit 11 ∶ emit 12 ∶ emit 13
_ = sound-↭
