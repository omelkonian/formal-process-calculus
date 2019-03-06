--------------------------------------------------------------------------------
-- Factor out the non-deterministic part by parametrizing over a scheduler.

module 1a-SchedulersSimple where

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ)
open import Data.List    using (List; []; _∷_; [_])

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

  -- sequential composition
  _∶_ : Process → Process → Process

  -- parallel composition
  _∣_ : Process → Process → Process

infixr 5 _∶_
infixr 4 _∣_

------------
-- Semantics
infix  2 _—→⟦_⟧_,_
infix  2 _—↠⟦_⟧_,_

infix  1 begin_
infixr 2 _—→⟦_⟧⟨_⟩_
infix  3 _∎

-- T0D0 vary scheduler (i.e. return a new scheduler)
Scheduler : Set
Scheduler = Process         -- cannot schedule a process without subprocesses
          → Maybe Label × Process -- ... and the rest


always-first : Scheduler
always-first ∅        = nothing , ∅
always-first (emit x) = just x , ∅
always-first (p ∶ q) with always-first p
... | (nothing , _)  = always-first q
... | (just l  , ∅)  = just l , q
... | (just l  , p′) = just l , p′ ∶ q
always-first (p ∣ q) with always-first p
... | (nothing , _)  = always-first q
... | (just l  , ∅)  = just l , q
... | (just l  , p′) = just l , p′ ∣ q

-- T0D0 define well-behavedness of schedulers

_∷ₘ_ : ∀ {A : Set} → Maybe A → List A → List A
nothing ∷ₘ xs = xs
just x  ∷ₘ xs = x ∷ xs

data _—→⟦_⟧_,_ : Process
               → Maybe Label
               → Process
               → Scheduler
               → Set where

  [SCHEDULE] : ∀ {P P′ l σ}

    → σ P ≡ (l , P′)
      ----------------
    → P —→⟦ l ⟧ P′ , σ

data _—↠⟦_⟧_,_ : Process
               → List Label
               → Process
               → Scheduler
               → Set where

  _∎ : ∀ {σ : Scheduler}
    → (P : Process)
      ----------------
    → P —↠⟦ [] ⟧ P , σ

  _—→⟦_⟧⟨_⟩_ : ∀ {Q R ls σ}
    → (P : Process)
    → (l : Maybe Label)
    → P —→⟦ l  ⟧ Q , σ
    → Q —↠⟦ ls ⟧ R , σ
      --------------------
    → P —↠⟦ l ∷ₘ ls ⟧ R , σ

begin_ : ∀ {P Q ls σ}
  → P —↠⟦ ls ⟧ Q , σ
    ---------------------
  → P —↠⟦ ls ⟧ Q , σ
begin P—↠Q = P—↠Q

-- Derivation I: Simple parallel
_ : emit 1 ∣ emit 2
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    ∅
  , always-first
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ just 1 ⟧⟨ [SCHEDULE] refl ⟩
    emit 2
  —→⟦ just 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

-- Derivation II: Multiple parallel (in-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅
  , always-first
_ =
  begin
    (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 1 ⟧⟨ [SCHEDULE] refl ⟩
    emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅ ∣ emit 3 ∣ ∅
  —→⟦ just 3 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

-- Derivation II': Multiple parallel (out-of-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 2 ∷ 1 ∷ 3 ∷ [] ⟧
    ∅
  , {!!} -- T0D0 define trampoline (left/right) scheduler
_ = {!!}

-- Derivation III: Simple sequential
_ : emit 1 ∶ emit 2
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    ∅
  , always-first
_ =
  begin
    emit 1 ∶ emit 2
  —→⟦ just 1 ⟧⟨ [SCHEDULE] refl ⟩
    emit 2
  —→⟦ just 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

-- Derivation IV: Multiple sequential
_ : (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
   —↠⟦ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅
   , always-first
_ = begin
      (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ just 1 ⟧⟨ [SCHEDULE] refl ⟩
      emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ just 2 ⟧⟨ [SCHEDULE] refl ⟩
      ∅ ∶ emit 3 ∶ ∅
    —→⟦ just 3 ⟧⟨ [SCHEDULE] refl ⟩
      ∅
    ∎

-- Derivation V: Simple sequential+parallel (in-order)
_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ 11 ∷ 12 ∷ 21 ∷ 22 ∷ 31 ∷ 32 ∷ [] ⟧
    ∅
  , always-first
_ = begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 11 ⟧⟨ [SCHEDULE] refl ⟩
      emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 12 ⟧⟨ [SCHEDULE] refl ⟩
      emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 21 ⟧⟨ [SCHEDULE] refl ⟩
      emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ just 22 ⟧⟨ [SCHEDULE] refl ⟩
    emit 31 ∶ emit 32
  —→⟦ just 31 ⟧⟨ [SCHEDULE] refl ⟩
    emit 32
  —→⟦ just 32 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

-- Derivation V': Simple sequential+parallel (out-of-order)
_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ 21 ∷ 31 ∷ 22 ∷ 11 ∷ 12 ∷ 32 ∷ [] ⟧
    ∅
  , {!!} -- T0D0 define ad-hoc scheduler
_ = {!!}

-- Derivation VI: Complex sequential+parallel
_ : ( emit 1
    ∣ emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —↠⟦ 1 ∷ 11 ∷ 12 ∷ 21 ∷ 22 ∷ 2 ∷ [] ⟧
    ∅
  , always-first
_ = begin
    ( emit 1
    ∣ emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —→⟦ just 1 ⟧⟨ [SCHEDULE] refl ⟩
    ( emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —→⟦ just 11 ⟧⟨ [SCHEDULE] refl ⟩
    emit 12
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —→⟦ just 12 ⟧⟨ [SCHEDULE] refl ⟩
    emit 21 ∶ emit 22
  ∣ emit 2
  —→⟦ just 21 ⟧⟨ [SCHEDULE] refl ⟩
    emit 22
  ∣ emit 2
  —→⟦ just 22 ⟧⟨ [SCHEDULE] refl ⟩
    emit 2
  —→⟦ just 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

---------------
-- Equivalence

-- _≈_ : Process → Process → Set
-- P ≈ Q = ∀ {} → (P —→⟦ l  ⟧ R , σ) <-> (Q —→⟦ l  ⟧ R , σ)

infix 2 _≈_
data _≈_ : Process → Process → Set where

  ≈stop : ∀ {P}

      -----
    → P ≈ P

  ≈step : ∀ {P P′ Q Q′ l}
    → (∀ (σ : Scheduler) → Q —→⟦ l ⟧ P′ , σ
                         → P —→⟦ l ⟧ P′ , σ
                         → P′ ≈ Q′)
      --------------------------------------
    → P ≈ Q

-- Equivalence I: Identity
_ : emit 1 ∣ emit 21 ∶ emit 22
  ≈ emit 1 ∣ emit 21 ∶ emit 22
_ = ≈stop

-- Equivalence II: Prepend ∅
_ : emit 1 ∣ emit 21 ∶ emit 22
  ≈ ∅ ∣ emit 1 ∣ emit 21 ∶ emit 22
_ = ≈step {{!!}} {{!!}} {{!!}} {{!!}} {{!!}} (λ σ P→P′ Q→Q′ → {!!})
  -- depends on scheduler...
  -- maybe we need some notion of well-behaved scheduler
