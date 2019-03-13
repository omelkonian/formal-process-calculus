--------------------------------------------------------------------------------
-- Relational specification of step relation (list/set results).

module 3-RelSpec where

open import Function     using (_$_)
open import Data.Bool    using (T; Bool; true; false; not; _∧_)
open import Data.Nat     using (ℕ)
open import Data.Product using (_×_; _,_; map₂; ∃; ∃-syntax)
open import Data.List    using (List; []; _∷_; [_]; _++_; map)

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Any using (here; there)

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

hasTerminated : Process → Bool
hasTerminated ∅        = true
hasTerminated (emit _) = false
hasTerminated (P ∶ Q)  = hasTerminated P ∧ hasTerminated Q
hasTerminated (P ∣ Q)  = hasTerminated P ∧ hasTerminated Q

------------
-- Semantics

infix  3 _—→_
infix  2 _—↠⟦_⟧_

infix  1 begin_
infixr 2 _—→⟦_⟧⟨_∋_⟩_
infix  3 _∎

data _—→_ : Process → List (Label × Process) → Set where


  [EMPTY] : ∀ {P}

    → {pr : T (hasTerminated P)}
      -------------------
    → P —→ []


  [EMIT] : ∀ {l}

      -------------------
    → emit l —→ [ l , ∅ ]

  [SEQ-L] : ∀ {P Q Ps}

    → {pr : T (not $ hasTerminated P)}
    → P —→ Ps
      -----------------------------
    → P ∶ Q —→ map (map₂ (_∶ Q)) Ps

  [SEQ-R] : ∀ {P Q Qs}

    → {pr : T (hasTerminated P)}
    → Q —→ Qs
      -----------------------------
    → P ∶ Q —→ Qs

  [STEP] : ∀ {P Q : Process} {Ps Qs : List (Label × Process)}

    → P —→ Ps
    → Q —→ Qs
      ----------------------------------
    → P ∣ Q —→ (  map (map₂ (_∣ Q)) Ps
               ++ map (map₂ (P ∣_)) Qs )


_ : emit 1 ∣ emit 2 —→ (1 , ∅ ∣ emit 2)
                     ∷ (2 , emit 1 ∣ ∅)
                     ∷ []
_ = [STEP] [EMIT] [EMIT]


_ : emit 1 ∶ emit 2 —→ [ (1 , ∅ ∶ emit 2) ]
_ = [SEQ-L] [EMIT]

_ : ∅ ∶ emit 2 —→ [ (2 , ∅) ]
_ = [SEQ-R] [EMIT]

_ : ∅ ∶ ∅ ∶ emit 2 —→ [ (2 , ∅) ]
_ = [SEQ-R] $ [SEQ-R] [EMIT]

{-
unique-step : ∀ {P Ps Ps′}
  → P —→ Ps
  → P —→ Ps′
    --------
  → Ps ≡ Ps′
unique-step {∅}      [EMPTY]    [EMPTY]    = refl
unique-step {emit x} [EMIT]         [EMIT]         = refl
unique-step {P ∶ Q} S₁ S₂
  with hasTerminated P | hasTerminated Q | S₁ | S₂
unique-step {P ∶ Q} S₁ S₂ | true | true | [EMPTY] | [EMPTY] = refl
unique-step {P ∶ Q} S₁ S₂ | true | true | [EMPTY] | [SEQ-L] {pr = p} S2 = {!!}
unique-step {P ∶ Q} S₁ S₂ | true | true | [EMPTY] {pr = pr} | [SEQ-R] S2 = {!!}
unique-step {P ∶ Q} S₁ S₂ | true | true | [SEQ-L] {pr} S1 | S2 = {!!}
unique-step {P ∶ Q} S₁ S₂ | true | true | [SEQ-R] {pr} S1 | S2 = {!!}
... | true  | false | S1 | S2 = {!!}
... | false | true  | S1 | S2 = {!qt!}
... | false | false | S1 | S2 = {!qt!}
-- ([SEQ] S₁)     ([SEQ] S₂)     rewrite (unique-step S₁ S₂) = refl
unique-step {P ∣ Q}  ([STEP] S₁ S₃) ([STEP] S₂ S₄) = aux (unique-step S₁ S₂) (unique-step S₃ S₄)
  where
    aux : ∀ {P Q : Process} {Ps Ps′ Qs Qs′ : List (Label × Process)}
      → Ps ≡ Ps′
      → Qs ≡ Qs′
        ----------------------------------------------
      → map (map₂ (_∣ Q)) Ps  ++ map (map₂ (P ∣_)) Qs
      ≡ map (map₂ (_∣ Q)) Ps′ ++ map (map₂ (P ∣_)) Qs′
    aux refl refl = refl
-}

data _—↠⟦_⟧_ : Process → List Label → Process → Set where

  _∎ : ∀ (P : Process)
      -------------
    → P —↠⟦ [] ⟧ P

  _—→⟦_⟧⟨_∋_⟩_ : ∀ {Ps P′ Q ls}
    → (P : Process)
    → (l : Label)
    → P —→ Ps
    → (l , P′) ∈ Ps
    → P′ —↠⟦ ls ⟧ Q
      ------------------------
    → P —↠⟦ l ∷ ls ⟧ Q

begin_ : ∀ {P Q ls}
  → P —↠⟦ ls ⟧ Q
    -------------
  → P —↠⟦ ls ⟧ Q
begin P—↠Q = P—↠Q

-- Derivation I: Simple parallel (in-order)
_ : emit 1 ∣ emit 2
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    ∅ ∣ ∅
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ 1 ⟧⟨ [STEP] [EMIT] [EMIT] ∋ here refl ⟩
    ∅ ∣ emit 2
  —→⟦ 2 ⟧⟨ [STEP] [EMPTY] [EMIT] ∋ here refl ⟩
    ∅ ∣ ∅
  ∎

-- Derivation I': Simple parallel (out-of-order)
_ : emit 1 ∣ emit 2
  —↠⟦ 2 ∷ 1 ∷ [] ⟧
    ∅ ∣ ∅
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ 2 ⟧⟨ [STEP] [EMIT] [EMIT] ∋ there (here refl) ⟩
    emit 1 ∣ ∅
  —→⟦ 1 ⟧⟨ [STEP] [EMIT] [EMPTY] ∋ here refl ⟩
    ∅ ∣ ∅
  ∎

-- Derivation II: Multiple parallel (in-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
_ = begin
      (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 1 ⟧⟨ [STEP] ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
                    ([STEP] [EMIT]  $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
             ∋ here refl ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 2 ⟧⟨ [STEP] ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMPTY] [EMPTY])
                    ([STEP] [EMIT]  $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
             ∋ here refl ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 3 ⟧⟨ [STEP] ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMPTY] [EMPTY])
                    ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
             ∋ here refl ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
    ∎

-- Derivation II': Multiple parallel (out-of-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 2 ∷ 1 ∷ 3 ∷ [] ⟧
    (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
_ = begin
      (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 2 ⟧⟨ [STEP] ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
                    ([STEP] [EMIT]  $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
             ∋ there (here refl) ⟩
      (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 1 ⟧⟨ [STEP] ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
                    ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
             ∋ here refl ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ emit 3 ∣ ∅
    —→⟦ 3 ⟧⟨ [STEP] ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMPTY] [EMPTY])
                    ([STEP] [EMPTY] $ [STEP] [EMPTY] $ [STEP] [EMIT] [EMPTY])
             ∋ here refl ⟩
      (∅ ∣ ∅ ∣ ∅ ∣ ∅) ∣ ∅ ∣ ∅ ∣ ∅ ∣ ∅
    ∎

-- Derivation III: Simple sequential
_ : emit 1 ∶ emit 2
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    ∅
_ = begin
      emit 1 ∶ emit 2
    —→⟦ 1 ⟧⟨ [SEQ-L] [EMIT] ∋ here refl ⟩
      ∅ ∶ emit 2
    —→⟦ 2 ⟧⟨ [SEQ-R] [EMIT] ∋ here refl ⟩
      ∅
    ∎

-- Derivation IV: Multiple sequential
_ : (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
   —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅ ∶ ∅
_ = begin
      (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ 1 ⟧⟨ [SEQ-L] $ [SEQ-R] $ [SEQ-R] $ [SEQ-L] [EMIT] ∋ here refl ⟩
      (∅ ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ 2 ⟧⟨ [SEQ-R] $ [SEQ-L] [EMIT] ∋ here refl ⟩
      ∅ ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ 3 ⟧⟨ [SEQ-R] $ [SEQ-R] $ [SEQ-L] [EMIT] ∋ here refl ⟩
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
_ =
  begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ 11 ⟧⟨ [STEP] ([SEQ-L] [EMIT]) ([STEP] ([SEQ-L] [EMIT]) ([SEQ-L] [EMIT])) ∋ here refl ⟩
      ∅       ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ 12 ⟧⟨ [STEP] ([SEQ-R] [EMIT]) ([STEP] ([SEQ-L] [EMIT]) ([SEQ-L] [EMIT])) ∋ here refl ⟩
      ∅
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ 21 ⟧⟨ [STEP] [EMPTY] ([STEP] ([SEQ-L] [EMIT]) ([SEQ-L] [EMIT])) ∋ here refl ⟩
      ∅
    ∣ ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ 22 ⟧⟨ [STEP] [EMPTY] ([STEP] ([SEQ-R] [EMIT]) ([SEQ-L] [EMIT])) ∋ here refl ⟩
      ∅
    ∣ ∅
    ∣ emit 31 ∶ emit 32
  —→⟦ 31 ⟧⟨ [STEP] [EMPTY] ([STEP] [EMPTY] ([SEQ-L] [EMIT])) ∋ here refl ⟩
      ∅
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ 32 ⟧⟨ [STEP] [EMPTY] ([STEP] [EMPTY] ([SEQ-R] [EMIT])) ∋ here refl ⟩
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
_ =
  begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ 21 ⟧⟨ [STEP] ([SEQ-L] [EMIT]) ([STEP] ([SEQ-L] [EMIT]) ([SEQ-L] [EMIT])) ∋ there (here refl) ⟩
      emit 11 ∶ emit 12
    ∣ ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ 31 ⟧⟨ [STEP] ([SEQ-L] [EMIT]) ([STEP] ([SEQ-R] [EMIT]) ([SEQ-L] [EMIT])) ∋ there (there (here refl)) ⟩
      emit 11 ∶ emit 12
    ∣ ∅       ∶ emit 22
    ∣ ∅       ∶ emit 32
  —→⟦ 22 ⟧⟨ [STEP] ([SEQ-L] [EMIT]) ([STEP] ([SEQ-R] [EMIT]) ([SEQ-R] [EMIT])) ∋ there (here refl) ⟩
      emit 11 ∶ emit 12
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ 11 ⟧⟨ [STEP] ([SEQ-L] [EMIT]) ([STEP] [EMPTY] ([SEQ-R] [EMIT])) ∋ here refl ⟩
      ∅       ∶ emit 12
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ 12 ⟧⟨ [STEP] ([SEQ-R] [EMIT]) ([STEP] [EMPTY] ([SEQ-R] [EMIT])) ∋ here refl ⟩
      ∅
    ∣ ∅
    ∣ ∅       ∶ emit 32
  —→⟦ 32 ⟧⟨ [STEP] [EMPTY] ([STEP] [EMPTY] ([SEQ-R] [EMIT])) ∋ here refl ⟩
      ∅
    ∣ ∅
    ∣ ∅
  ∎

--------------
-- Equivalence

infix 3 _≈_
_≈_ : Process → Process → Set
P ≈ Q = ∀ {Ps} → P —→ Ps → Q —→ Ps  -- one-way is sufficient, due to `unique-step`

_ : emit 1 ≈ emit 1
_ = λ z → z

ex-≈ : emit 1 ∣ emit 2 ≈ emit 2 ∣ emit 1
ex-≈ {Ps} z = {!!}
