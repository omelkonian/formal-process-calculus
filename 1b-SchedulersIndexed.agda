--------------------------------------------------------------------------------
-- Factor out the non-deterministic part by parametrizing over a scheduler.

module 1b-SchedulersIndexed where

open import Function     using (_∋_; _∘_; _$_; case_of_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax; map₁; map₂)
open import Data.Empty   using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≟_)
open import Data.Nat.Properties using (suc-injective; i+j≡0⇒j≡0)

open import Data.Vec using (Vec; []; _∷_; [_]; _++_; map)
open import Data.Vec.Any using (here; there)
open import Data.Vec.Membership.Propositional using (_∈_)
open import Data.Vec.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

------------
-- Processes

data Action : Set where

  EMIT : ℕ → Action

Trace : ℕ → Set
Trace k = Vec Action k

data Process : ℕ -- number of actions
             → Set where

  -- termination
  ∅ : Process 0

  -- atomic action
  action : Action → Process 1

  -- sequential composition
  _∶_⊣_ : ∀ {n m k} → Process n → Process m → n + m ≡ k → Process k
    -- NB : can disallow ∅ operands by using (suc n)

  -- parallel composition
  _∣_⊣_ : ∀ {n m k} → Process n → Process m → n + m ≡ k → Process k
    -- NB : can disallow ∅ operands by using (suc n)

pattern emit x = action (EMIT x)

infixr 5 _∶_
-- _∶_ : ∀ {n m} → Process n → Process m → Process (n + m)
pattern _∶_ {n} {m} p q = _∶_⊣_ {n} {m} p q refl

infixr 4 _∣_
-- _∣_ : ∀ {n m} → Process n → Process m → Process (n + m)
pattern _∣_ {n} {m} p q = _∣_⊣_ {n} {m} p q refl


toActions : ∀ {n} → Process n → Vec Action n
toActions ∅              = []
toActions (emit x)       = [ EMIT x ]
toActions (p ∶ q ⊣ refl) = toActions p ++ toActions q
toActions (p ∣ q ⊣ refl) = toActions p ++ toActions q

------------
-- Semantics
infix  2 _—→⟦_⟧_,_
infix  2 _—↠⟦_⟧_,_⊣_

infix  1 begin_
infixr 2 _—→⟦_⟧⟨_⟩_
infix  3 _∎

-- T0D0 vary scheduler (i.e. return a new scheduler)
Scheduler : Set
Scheduler = ∀ {n}
          → (ps : Process (suc n))    -- cannot schedule a process without subprocesses
          → Σ[ x ∈ Action ] Process n

--   x ∈ toActions ps -- return an atomic sub-process
-- × Process n        -- ... and the rest

always-first : Scheduler
always-first (emit x)                 =  EMIT x , ∅
always-first (_∣_⊣_ {zero}  p q refl) = always-first q
always-first (_∣_⊣_ {suc _} p q pr)   = map₂ (_∣ q ⊣ suc-injective pr) (always-first p)
always-first (_∶_⊣_ {zero}  p q refl) = always-first q
always-first (_∶_⊣_ {suc _} p q pr)   = map₂ (_∶ q ⊣ suc-injective pr) (always-first p)

data _—→⟦_⟧_,_ : ∀ {n : ℕ}
               → Process (suc n)
               → Action
               → Process n
               → Scheduler
               → Set where

  [SCHEDULE] : ∀ {n} {σ : Scheduler} {P : Process (suc n)} {P′ : Process n} {x : Action}

    → σ P ≡ ( x , P′)
      --------------------------
    → P —→⟦ x ⟧ P′ , σ

data _—↠⟦_⟧_,_⊣_ : ∀ {n m k : ℕ}
                 → Process n
                 → Trace k
                 → Process m
                 → Scheduler
                 → n ≡ k + m
                 → Set where

  _∎ : ∀ {n} {σ : Scheduler}
    → (P : Process n)
      ------------------------------
    → P —↠⟦ [] ⟧ P , σ ⊣ refl

  _—→⟦_⟧⟨_⟩_ : ∀ {n m k : ℕ} {Q : Process n} {R : Process m} {ls : Trace k} {σ : Scheduler} {pr : n ≡ k + m}
    → (P : Process (suc n))
    → (l : Action)
    → P —→⟦ l  ⟧ Q , σ
    → Q —↠⟦ ls ⟧ R , σ ⊣ pr
      ------------------------
    → P —↠⟦ l ∷ ls ⟧ R , σ ⊣ cong suc pr

begin_ : ∀ {n m k : ℕ} {P : Process n} {Q : Process m} {ls : Trace k} {σ : Scheduler} {pr}
  → P —↠⟦ ls ⟧ Q , σ ⊣ pr
    ---------------------
  → P —↠⟦ ls ⟧ Q , σ ⊣ pr
begin P—↠Q = P—↠Q

-- Derivation I: Simple parallel
_ : emit 1 ∣ emit 2
  —↠⟦ map EMIT $ 1 ∷ 2 ∷ [] ⟧
    ∅
  , always-first
  ⊣ refl
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ EMIT 1 ⟧⟨ [SCHEDULE] refl ⟩
    ∅ ∣ emit 2
  —→⟦ EMIT 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

-- Derivation II: Multiple parallel (in-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ map EMIT $ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅ ∣ ∅
  , always-first
  ⊣ refl
_ =
  begin
    (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ EMIT 1 ⟧⟨ [SCHEDULE] refl ⟩
    (∅ ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ EMIT 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅ ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ EMIT 3 ⟧⟨ [SCHEDULE] refl ⟩
    ∅ ∣ ∅
  ∎

-- Derivation II': Multiple parallel (out-of-order)
_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ map EMIT $ 2 ∷ 1 ∷ 3 ∷ [] ⟧
    ∅
  , {!!} -- T0D0 define trampoline (left/right) scheduler
  ⊣ refl
_ = {!!}

-- Derivation III: Simple sequential
_ : emit 1 ∶ emit 2
  —↠⟦ map EMIT $ 1 ∷ 2 ∷ [] ⟧
    ∅
  , always-first
  ⊣ refl
_ =
  begin
    emit 1 ∶ emit 2
  —→⟦ EMIT 1 ⟧⟨ [SCHEDULE] refl ⟩
    ∅ ∶ emit 2
  —→⟦ EMIT 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

-- Derivation IV: Multiple sequential
_ : (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
   —↠⟦ map EMIT $ 1 ∷ 2 ∷ 3 ∷ [] ⟧
    ∅ ∶ ∅
   , always-first
  ⊣ refl
_ = begin
      (∅ ∶ ∅ ∶ emit 1 ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ EMIT 1 ⟧⟨ [SCHEDULE] refl ⟩
      (∅ ∶ ∅) ∶ emit 2 ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ EMIT 2 ⟧⟨ [SCHEDULE] refl ⟩
      ∅ ∶ ∅ ∶ emit 3 ∶ ∅
    —→⟦ EMIT 3 ⟧⟨ [SCHEDULE] refl ⟩
      ∅ ∶ ∅
     ∎

-- Derivation V: Simple sequential+parallel (in-order)
_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ map EMIT $ 11 ∷ 12 ∷ 21 ∷ 22 ∷ 31 ∷ 32 ∷ [] ⟧
    ∅
  , always-first
  ⊣ refl
_ = begin
      emit 11 ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ EMIT 11 ⟧⟨ [SCHEDULE] refl ⟩
      ∅       ∶ emit 12
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ EMIT 12 ⟧⟨ [SCHEDULE] refl ⟩
      ∅
    ∣ emit 21 ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ EMIT 21 ⟧⟨ [SCHEDULE] refl ⟩
      ∅       ∶ emit 22
    ∣ emit 31 ∶ emit 32
  —→⟦ EMIT 22 ⟧⟨ [SCHEDULE] refl ⟩
      ∅
    ∣ emit 31 ∶ emit 32
  —→⟦ EMIT 31 ⟧⟨ [SCHEDULE] refl ⟩
    ∅ ∶ emit 32
  —→⟦ EMIT 32 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

-- Derivation V': Simple sequential+parallel (out-of-order)
_ : emit 11 ∶ emit 12
  ∣ emit 21 ∶ emit 22
  ∣ emit 31 ∶ emit 32
  —↠⟦ map EMIT $ 21 ∷ 31 ∷ 22 ∷ 11 ∷ 12 ∷ 32 ∷ [] ⟧
    ∅
  , {!!} -- T0D0 define ad-hoc scheduler
  ⊣ refl
_ = {!!}

-- Derivation VI: Complex sequential+parallel
_ : ( emit 1
    ∣ emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —↠⟦ map EMIT $ 1 ∷ 11 ∷ 12 ∷ 21 ∷ 22 ∷ 2 ∷ [] ⟧
    ∅
  , always-first
  ⊣ refl
_ = begin
    ( emit 1
    ∣ emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —→⟦ EMIT 1 ⟧⟨ [SCHEDULE] refl ⟩
    ( ∅
    ∣ emit 11 ∶ emit 12 )
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —→⟦ EMIT 11 ⟧⟨ [SCHEDULE] refl ⟩
    (∅ ∶ emit 12)
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —→⟦ EMIT 12 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∶ ( emit 21 ∶ emit 22
    ∣ emit 2 )
  —→⟦ EMIT 21 ⟧⟨ [SCHEDULE] refl ⟩
    ∅ ∶ emit 22
  ∣ emit 2
  —→⟦ EMIT 22 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∣ emit 2
  —→⟦ EMIT 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

---------------
-- Equivalence

-- _≈_ : Process → Process → Set
-- P ≈ Q = ∀ {} → (P —→⟦ l  ⟧ P , σ) <-> (P —→⟦ l  ⟧ Q , σ)
