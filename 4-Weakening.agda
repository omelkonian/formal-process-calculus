--------------------------------------------------------------------------------
-- Using a weakening hypothesis to model the non-deterministic step relation.

module 4-Weakening where

open import Function     using (case_of_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Nat     using (ℕ)
open import Data.List    using (List; []; _∷_; [_])

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------
-- Processes

data Label : Set where

  emitL : ℕ → Label

Trace : Set
Trace = List Label

data Action : Set where

  Auth-Emit : ℕ → Action

  Emit : ℕ → Action

data Process : Set where

  -- termination
  ∅ : Process

  -- atomic action
  action : Action → Process

  -- sequential composition
  -- _∶_ : Process → Process → Process

  -- parallel composition
  _∣_ : Process → Process → Process

pattern emit      n = action (Emit      n)
pattern auth-emit n = action (Auth-Emit n)

------------
-- Semantics

infixr 4 _∣_
infix  3 _≈_#_
infix  3 _—→⟦_⟧_
infix  2 _—↠⟦_⟧_

infix  1 begin_
infixr 2 _—→⟦_⟧⟨_⟩_
infix  3 _∎


-- T0D0 remove spurious ∅ somehow
data _≈_#_ : Process → Process → Process → Set where

  #-stopL : ∀ {x}

      -----------------------
    → action x ≈ action x # ∅

  #-stopLR : ∀ {P Q}

      -------------
    → P ∣ Q ≈ P # Q

  #-swap : ∀ {Γ L R}

    → Γ ≈ L # R
      -----------
    → Γ ≈ R # L

  #-merge : ∀ {Γ L R}

    → Γ ≈ L # R
      -------------
    → Γ ≈ L ∣ R # ∅

  #-step₁ : ∀ {Γ L R LL LR}

    → Γ ≈ L # R
    → L ≈ LL # LR
      ---------------
    → Γ ≈ LL # LR ∣ R

  #-step₂ : ∀ {Γ L R LL LR}

    → Γ ≈ L # R
    → L ≈ LL # LR
      ---------------
    → Γ ≈ LR # LL ∣ R

  #-step₃ : ∀ {Γ L R LL LR}

    → Γ ≈ L # R
    → L ≈ LL # LR
      ---------------
    → Γ ≈ R # LR ∣ LL

-- 1 sub-process
_ : emit 0 ≈ emit 0 # ∅
_ = #-stopL

-- 2 sub-processes
_ : emit 1 ∣ emit 2 ≈ emit 1 ∣ emit 2 # ∅
_ = #-merge #-stopLR

_ : emit 1 ∣ emit 2 ≈ emit 2 ∣ emit 1 # ∅
_ = #-merge (#-swap #-stopLR)

_ : emit 1 ∣ emit 2 ≈ emit 1 # emit 2
_ = #-stopLR

_ : emit 1 ∣ emit 2 ≈ emit 2 # emit 1
_ = #-swap #-stopLR

-- 3 sub-processes
_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 1 ∣ emit 2 ∣ emit 3 # ∅
_ = #-merge #-stopLR

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 1 ∣ emit 2 # emit 3
_ = {!!}

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 2 ∣ emit 1 # emit 3
_ = #-swap (#-step₂ (#-swap #-stopLR) #-stopLR)

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 1 ∣ emit 3 # emit 2
_ = {!!}

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 3 ∣ emit 1 # emit 2
_ = #-swap (#-step₁ (#-swap #-stopLR) #-stopLR)

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 2 ∣ emit 3 # emit 1
_ = #-swap #-stopLR

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 3 ∣ emit 2 # emit 1
_ = #-swap (#-step₃ (#-swap #-stopLR) #-stopLR)

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 1 # emit 2 ∣ emit 3
_ = #-stopLR

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 1 # emit 3 ∣ emit 2
_ = #-step₃ (#-swap #-stopLR) #-stopLR

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 2 # emit 1 ∣ emit 3
_ = {!!}

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 2 # emit 3 ∣ emit 1
_ = #-step₁ (#-swap #-stopLR) #-stopLR

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 3 # emit 1 ∣ emit 2
_ = {!!}

_ : emit 1 ∣ emit 2 ∣ emit 3 ≈ emit 3 # emit 2 ∣ emit 1
_ = #-step₂ (#-swap #-stopLR) #-stopLR

-- 4 sub-processes
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 # ∅
_ = #-merge #-stopLR
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 2 ∣ emit 4 ∣ emit 3 # ∅
_ = {!-t 10!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 3 ∣ emit 2 ∣ emit 4 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 3 ∣ emit 4 ∣ emit 2 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 4 ∣ emit 2 ∣ emit 3 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 4 ∣ emit 3 ∣ emit 2 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 2 ∣ emit 1 ∣ emit 3 ∣ emit 4 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 2 ∣ emit 1 ∣ emit 4 ∣ emit 3 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 2 ∣ emit 3 ∣ emit 1 ∣ emit 4 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 2 ∣ emit 3 ∣ emit 4 ∣ emit 1 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 2 ∣ emit 4 ∣ emit 1 ∣ emit 3 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 2 ∣ emit 4 ∣ emit 3 ∣ emit 1 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 3 ∣ emit 1 ∣ emit 2 ∣ emit 4 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 3 ∣ emit 1 ∣ emit 4 ∣ emit 2 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 3 ∣ emit 2 ∣ emit 1 ∣ emit 4 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 3 ∣ emit 2 ∣ emit 4 ∣ emit 1 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 3 ∣ emit 4 ∣ emit 1 ∣ emit 2 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 3 ∣ emit 4 ∣ emit 2 ∣ emit 1 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 4 ∣ emit 1 ∣ emit 2 ∣ emit 3 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 4 ∣ emit 1 ∣ emit 3 ∣ emit 2 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 4 ∣ emit 2 ∣ emit 1 ∣ emit 3 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 4 ∣ emit 2 ∣ emit 3 ∣ emit 1 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 4 ∣ emit 3 ∣ emit 1 ∣ emit 2 # ∅
_ = {!!}
_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 4 ∣ emit 3 ∣ emit 2 ∣ emit 1 # ∅
_ = {!!}


_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 2 ∣ emit 3 # emit 4
_ = {!!}

_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 2 ∣ emit 4 # emit 3
_ = {!!}

_ : emit 1 ∣ emit 2 ∣ emit 3 ∣ emit 4 ≈ emit 1 ∣ emit 2 ∣ emit 4 # emit 3
_ = {!!}

data _—→⟦_⟧_ : Process → Label → Process → Set where

  [EMIT] : ∀ {n}

      ------------------------------------
    → auth-emit n ∣ emit n —→⟦ emitL n ⟧ ∅

  [STEP] : ∀ {x x′ Γ Γ′ l}

    → x —→⟦ l ⟧ x′
    → Γ ≈ x # Γ′
      -----------------
    → Γ —→⟦ l ⟧ x′ ∣ Γ′

data _—↠⟦_⟧_ : Process → Trace → Process → Set where

  _∎ : ∀ (P : Process)
      -------------
    → P —↠⟦ [] ⟧ P

  _—→⟦_⟧⟨_⟩_ : ∀ {Q R ls}
    → (P : Process)
    → (l : Label)
    → P —→⟦ l  ⟧ Q
    → Q —↠⟦ ls ⟧ R
      -----------------
    → P —↠⟦ l ∷ ls ⟧ R

begin_ : ∀ {P Q ls}
  → P —↠⟦ ls ⟧ Q
    -------------
  → P —↠⟦ ls ⟧ Q
begin P—↠Q = P—↠Q

_ : auth-emit 1 ∣ emit 1
  —↠⟦ [ emitL 1 ] ⟧
    ∅
_ = begin
      auth-emit 1 ∣ emit 1
    —→⟦ emitL 1 ⟧⟨ [EMIT] ⟩
      ∅
    ∎

_ : emit 1 ∣ auth-emit 1
  —↠⟦ [ emitL 1 ] ⟧
    ∅ ∣ ∅
_ = begin
      emit 1 ∣ auth-emit 1
    —→⟦ emitL 1 ⟧⟨ [STEP] [EMIT] (#-merge (#-swap #-stopLR)) ⟩
      ∅ ∣ ∅
    ∎

_ : (auth-emit 1 ∣ auth-emit 2) ∣ (emit 2 ∣ emit 1)
  —↠⟦ emitL 1 ∷ emitL 2 ∷ [] ⟧
    ∅ ∣ ∅
_ = begin
      (auth-emit 1 ∣ auth-emit 2) ∣ (emit 2 ∣ emit 1)
    —→⟦ emitL 1 ⟧⟨ [STEP] [EMIT] {!!} ⟩
      ∅ ∣ auth-emit 2 ∣ emit 2
    —→⟦ emitL 2 ⟧⟨ [STEP] [EMIT] {!!} ⟩
      ∅ ∣ ∅
    ∎

_ : (auth-emit 1 ∣ auth-emit 2) ∣ (emit 2 ∣ emit 1)
  —↠⟦ emitL 2 ∷ emitL 1 ∷ [] ⟧
    ∅ ∣ ∅
_ = begin
      (auth-emit 1 ∣ auth-emit 2) ∣ (emit 2 ∣ emit 1)
    —→⟦ emitL 2 ⟧⟨ [STEP] [EMIT] {!!} ⟩
      ∅ ∣ auth-emit 1 ∣ emit 1
    —→⟦ emitL 1 ⟧⟨ [STEP] [EMIT] {!!} ⟩
      ∅ ∣ ∅
    ∎

-- Bisimilarity


-- equal up to ∅
_~_ : Process → Process → Set
p ~ q = removeEmpties p ≡ removeEmpties q
  where
    removeEmpties : Process → Process
    removeEmpties (∅ ∣ q) = q
    removeEmpties (p ∣ ∅) = p
    removeEmpties (p ∣ q) = removeEmpties p ∣ removeEmpties q
    removeEmpties p       = p


sim : Process → Process → Set
sim p q = ∀ {l r}

  → p —→⟦ l ⟧ r
    -----------------------
  → ∃[ r′ ] ( r ~ r′
            × q —→⟦ l ⟧ r′
            )

bisim : Process → Process → Set
bisim p q = sim p q × sim q p


ex-sim : sim (auth-emit 1 ∣ emit 1) (emit 1 ∣ auth-emit 1)
ex-sim {.(emitL 1)} {.∅}       [EMIT]          = (∅ ∣ ∅) , refl , [STEP] [EMIT] (#-merge (#-swap #-stopLR))
ex-sim {l}          {.(_ ∣ _)} ([STEP] p→r x₁) = {!!}
