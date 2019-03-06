--------------------------------------------------------------------------------
-- Factor out the non-deterministic part by parametrizing over a scheduler.

module 1b-SchedulersIndexed where

open import Function     using (_∋_)
open import Data.Product using (_×_; _,_; Σ; Σ-syntax)
open import Data.Empty   using (⊥; ⊥-elim)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
open import Data.Nat.Properties using (i+j≡0⇒j≡0)

open import Data.Vec using (Vec; []; _∷_; [_]; _++_; map)
open import Data.Vec.Any using (here; there)
open import Data.Vec.Membership.Propositional using (_∈_)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

------------
-- Processes

Label : Set
Label = ℕ

data Process : ℕ -- number of sequential sub-processes
             → Set where

  -- termination
  ∅ : Process 0

  -- atomic action
  emit : Label → Process 1

  -- sequential composition (leave out for now)
  -- _∶_ : Process → Process → Process

  -- parallel composition
  _∣_⊣_ : ∀ {n m k} → Process n → Process m → n + m ≡ k → Process k

infixr 4 _∣_
_∣_ : ∀ {n m} → Process n → Process m → Process (n + m)
_∣_ {n} {m} p q = p ∣ q ⊣ refl

toSubprocesses : ∀ {n} → Process n → Vec (Process 1) n
toSubprocesses ∅              = []
toSubprocesses (emit x)       = [ emit x ]
toSubprocesses (p ∣ q ⊣ refl) = toSubprocesses p ++ toSubprocesses q

fromSubprocesses : ∀ {n} → Vec (Process 1) n → Process n
fromSubprocesses []       = ∅
fromSubprocesses (p ∷ ps) with fromSubprocesses ps
... | ∅   = p
... | ps′ = p ∣ ps′

getLabel : Process 1 → Label
getLabel (emit l)                                     = l
getLabel (_∣_⊣_ {zero}        {zero}   {.1} p q ())
getLabel (_∣_⊣_ {zero}        {suc .0} {.1} p q refl) = getLabel q
getLabel (_∣_⊣_ {suc zero}    {zero}   {.1} p q refl) = getLabel p
getLabel (_∣_⊣_ {suc (suc n)} {zero}   {.1} p q ())
getLabel (_∣_⊣_ {suc n}       {suc m}  {.1} p q pr)   = ⊥-elim (aux pr)
  where
    aux : ∀ {n m} → suc (n + suc m) ≢ 1
    aux {zero}  {m} ()
    aux {suc n} {m} ()

getLabels : ∀ {n} → Process n → Vec Label n
getLabels p = map (getLabel) (toSubprocesses p)

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
          → (ps : Process (suc n))                   -- cannot schedule a process without subprocesses
          → Σ[ p ∈ Process 1 ] p ∈ toSubprocesses ps -- return an atomic sub-process
                             × Process n             -- ... and the rest

always-first : Scheduler
always-first {n} ps with toSubprocesses ps
... | x ∷ xs = x , here refl , fromSubprocesses xs

data _—→⟦_⟧_,_ : ∀ {n : ℕ}
               → Process (suc n)
               → Label
               → Process n
               → Scheduler
               → Set where

  -- [EMIT] : ∀ {l : Label} {σ : Scheduler}

  --     ---------------------
  --   → emit l —→⟦ l ⟧ ∅ , σ

  [SCHEDULE] : ∀ {n} {σ : Scheduler} {P : Process (suc n)} {P′ : Process n} {x : Process 1} {x∈P}

    → σ P ≡ ( x , x∈P , P′)
      --------------------------
    → P —→⟦ getLabel x ⟧ P′ , σ

data _—↠⟦_⟧_,_⊣_ : ∀ {n m k : ℕ}
                 → Process n
                 → Vec Label k
                 → Process m
                 → Scheduler
                 → n ≡ k + m
                 → Set where

  _∎ : ∀ {n} {σ : Scheduler}
    → (P : Process n)
      ------------------------------
    → P —↠⟦ [] ⟧ P , σ ⊣ refl

  _—→⟦_⟧⟨_⟩_ : ∀ {n m k : ℕ} {Q : Process n} {R : Process m} {ls : Vec Label k} {σ : Scheduler} {pr : n ≡ k + m}
    → (P : Process (suc n))
    → (l : Label)
    → P —→⟦ l  ⟧ Q , σ
    → Q —↠⟦ ls ⟧ R , σ ⊣ pr
      ------------------------
    → P —↠⟦ l ∷ ls ⟧ R , σ ⊣ cong suc pr

begin_ : ∀ {n m k : ℕ} {P : Process n} {Q : Process m} {ls : Vec Label k} {σ : Scheduler} {pr}
  → P —↠⟦ ls ⟧ Q , σ ⊣ pr
    ---------------------
  → P —↠⟦ ls ⟧ Q , σ ⊣ pr
begin P—↠Q = P—↠Q

_ : emit 1 ∣ emit 2 —↠⟦ 1 ∷ 2 ∷ [] ⟧ ∅ , always-first ⊣ refl
_ =
  begin
    emit 1 ∣ emit 2
  —→⟦ 1 ⟧⟨ [SCHEDULE] refl ⟩
    emit 2
  —→⟦ 2 ⟧⟨ [SCHEDULE] refl ⟩
    ∅
  ∎

_ : emit 1 ∣ emit 2 ∣ emit 3
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    emit 3
  , always-first
  ⊣ refl
_ =
  begin
    emit 1 ∣ emit 2 ∣ emit 3
  —→⟦ 1 ⟧⟨ [SCHEDULE] refl ⟩
    emit 2 ∣ emit 3
  —→⟦ 2 ⟧⟨ [SCHEDULE] refl ⟩
    emit 3
  ∎

_ : (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —↠⟦ 1 ∷ 2 ∷ [] ⟧
    emit 3
  , always-first
  ⊣ refl
_ =
  begin
    (∅ ∣ ∅ ∣ emit 1 ∣ ∅) ∣ emit 2 ∣ ∅ ∣ emit 3 ∣ ∅
  —→⟦ 1 ⟧⟨ [SCHEDULE] refl ⟩
    emit 2 ∣ emit 3
  —→⟦ 2 ⟧⟨ [SCHEDULE] refl ⟩
    emit 3
  ∎

---------------
-- Equivalence

-- _≈_ : Process → Process → Set
-- P ≈ Q = ∀ {} → (P —→⟦ l  ⟧ P , σ) <-> (P —→⟦ l  ⟧ Q , σ)

