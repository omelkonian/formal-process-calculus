------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Utilities.Lists where

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_)
open import Data.List     using (List; []; [_]; _∷_; _++_; map; sum; length)
open import Data.Nat      using (ℕ; _<?_)
open import Data.Fin      using (Fin)
  renaming (zero to fzero; suc to fsuc)

open import Relation.Nullary.Decidable            using (True)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

------------------------------------------------------------------------
-- Indexed operations.

Index : ∀ {A : Set} → (xs : List A) → Set
Index xs = Fin (length xs)

infix 3 _‼_
_‼_ : ∀ {A : Set} → (vs : List A) → Index vs → A
[]     ‼ ()
x ∷ _  ‼ fzero    = x
_ ∷ vs ‼ (fsuc f) = vs ‼ f

remove : ∀ {A : Set} → (vs : List A) → Index vs → List A
remove []       ()
remove (_ ∷ xs) fzero    = xs
remove (x ∷ vs) (fsuc f) = x ∷ remove vs f

_at_⟨_⟩ : ∀ {A : Set} → (vs : List A) → Index vs → A → List A
[]       at ()       ⟨ _ ⟩
(_ ∷ xs) at fzero    ⟨ x ⟩ = x ∷ xs
(y ∷ vs) at (fsuc f) ⟨ x ⟩ = y ∷ (vs at f ⟨ x ⟩)

_at_⟨_⟩remove_ : ∀ {A : Set} → (vs : List A) → Index vs → A → Index vs → List A
[] at () ⟨ _ ⟩remove ()
(_ ∷ vs) at fzero  ⟨ _  ⟩remove fzero  = vs
(_ ∷ vs) at fzero  ⟨ xv ⟩remove fsuc y = xv ∷ remove vs y
(_ ∷ vs) at fsuc x ⟨ xv ⟩remove fzero  = vs at x ⟨ xv ⟩
(v ∷ vs) at fsuc x ⟨ xv ⟩remove fsuc y = v ∷ vs at x ⟨ xv ⟩remove y

------------------------------------------------------------------------
-- Inductive relations on lists.

-- Less-than relation for lists (on lengths).
infix 3 _≾_
data _≾_ {ℓ} {A : Set ℓ} : List A → List A → Set where

  base-≾ : ∀ {xs : List A}

    → -------
      [] ≾ xs

  step-≾ : ∀ {x y : A} {xs ys : List A}

    → xs ≾ ys
      ---------------
    → x ∷ xs ≾ y ∷ ys

infix 3 _≾?_
_≾?_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set
[]     ≾? _      = ⊤
_ ∷ _  ≾? []     = ⊥
_ ∷ xs ≾? _ ∷ ys = xs ≾? ys

sound-≾ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → {p : xs ≾? ys} → xs ≾ ys
sound-≾ {_} {_} {[]}     {ys}     {tt} = base-≾
sound-≾ {_} {_} {x ∷ xs} {[]}     {()}
sound-≾ {_} {_} {_ ∷ xs} {_ ∷ ys} {pp} = step-≾ (sound-≾ {p = pp})

_ : ([ 1 ]) ≾? (1 ∷ 2 ∷ 3 ∷ [])
_ = tt

_ : ∀ {v} → True (length [ v ] <? length (1 ∷ [ v ]))
_ = tt


-- Partition relation.
data Partition {ℓ} {A : Set ℓ} : List A → (List A × List A) → Set where

  Partition-[] :

      ----------------------
      Partition [] ([] , [])


  Partition-L  : ∀ {x xs ys zs}

    → Partition xs (ys , zs)
      --------------------------------
    → Partition (x ∷ xs) (x ∷ ys , zs)


  Partition-R  : ∀ {x xs ys zs}

    → Partition xs (ys , xs)
      --------------------------------
    → Partition (x ∷ xs) (ys , x ∷ zs)

partition-[]ˡ : ∀ {ℓ} {A : Set ℓ} (xs : List A) → Partition xs ([] , xs)
partition-[]ˡ []       = Partition-[]
partition-[]ˡ (x ∷ xs) = Partition-R (partition-[]ˡ xs)

------------------------------------------------------------------------
-- List properties.

++-idʳ : ∀ {A : Set} {xs : List A}
       → xs ≡ xs ++ []
++-idʳ {_} {[]}     = refl
++-idʳ {_} {x ∷ xs} = cong (x ∷_) ++-idʳ
