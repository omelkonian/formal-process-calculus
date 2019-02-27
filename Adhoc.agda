{-# OPTIONS --rewriting #-}
module Adhoc where

open import Level        using (0ℓ; _⊔_)
  renaming (suc to lsuc)
open import Function     using (_∘_)
open import Data.Product using (Σ; Σ-syntax; ∃; ∃-syntax; _×_; _,_)
open import Data.Nat     using (ℕ; _+_; _∸_)
open import Data.Fin     using (Fin)
  renaming (zero to 0ᶠ; suc to sucᶠ)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------------------------
-- Finite multisets (from "Definable Quotients in Type Theory")

-- open import Function.Bijection using (Bijective)
Injective : ∀ {A B : Set} → (A → B) → Set
Injective {A} f = ∀ {x y : A} → f x ≡ f y → x ≡ y

Surjective : ∀ {A B : Set} → (A → B) → Set
Surjective f = {!!}

Bijective : ∀ {A B : Set} → (A → B) → Set
Bijective f = Injective f × Surjective f

ListF : Set → Set
ListF A = ∃[ n ] (Fin n → A)

_~_ : ∀ {A} → ListF A → ListF A → Set
(m , f) ~ (n , g) =
  Σ[ φ ∈ (Fin m → Fin n) ] ( Bijective φ
                           × (g ∘ φ ≡ f)
                           )


-- list1 := [0, 1, 2, 3, 4]
list₁ : ListF ℕ
list₁ = 5 , λ { 0ᶠ → 0
              ; (sucᶠ 0ᶠ) → 1
              ; (sucᶠ (sucᶠ 0ᶠ)) → 2
              ; (sucᶠ (sucᶠ (sucᶠ 0ᶠ))) → 3
              ; (sucᶠ (sucᶠ (sucᶠ (sucᶠ 0ᶠ)))) → 4
              ; (sucᶠ (sucᶠ (sucᶠ (sucᶠ (sucᶠ ())))))
              }

-- list2 := [3, 1, 2, 4, 0]
list₂ : ListF ℕ
list₂ = 5 , λ { 0ᶠ → 3
              ; (sucᶠ 0ᶠ) → 1
              ; (sucᶠ (sucᶠ 0ᶠ)) → 2
              ; (sucᶠ (sucᶠ (sucᶠ 0ᶠ))) → 4
              ; (sucᶠ (sucᶠ (sucᶠ (sucᶠ 0ᶠ)))) → 0
              ; (sucᶠ (sucᶠ (sucᶠ (sucᶠ (sucᶠ ())))))
              }

_ : list₁ ~ list₂
_ = φ , ({!!} , {!!})
  where
    φ : Fin 5 → Fin 5
    φ 0ᶠ = sucᶠ (sucᶠ (sucᶠ 0ᶠ))
    φ (sucᶠ 0ᶠ) = sucᶠ 0ᶠ
    φ (sucᶠ (sucᶠ 0ᶠ)) = sucᶠ (sucᶠ 0ᶠ)
    φ (sucᶠ (sucᶠ (sucᶠ 0ᶠ))) = sucᶠ (sucᶠ (sucᶠ (sucᶠ 0ᶠ)))
    φ (sucᶠ (sucᶠ (sucᶠ (sucᶠ 0ᶠ)))) = 0ᶠ
    φ (sucᶠ (sucᶠ (sucᶠ (sucᶠ (sucᶠ ())))))

postulate
  transport : ∀ {A} {l₁ l₂ : ListF A}
            → l₁ ~ l₂
              -------
            → l₁ ≡ l₂

{-
Cannot use REWRITE :(

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE transport #-}

ERROR
> transport  is not a legal rewrite rule, since the left-hand side is neither a defined symbol nor a constructor
> when checking the pragma REWRITE transport

-}


--------------------------------------------------------------------------------------------------
-- Finite multisets (hacker's approach)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Permutation.Inductive using (_↭_; ↭-setoid)

open import Relation.Binary.HeterogeneousEquality.Quotients using (Quotient; Quotients)

module QuotientLists (quot : Quotients 0ℓ 0ℓ) where

  QList : ∀ {A : Set} → Quotient (↭-setoid {A = A})
  QList = quot _

  -- Example for lists of natural numbers.
  open Quotient (QList {A = ℕ}) renaming (Q to Listℕ)

--------------------------------------------------------------------------------------------------

-- _\\_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
-- _\\_ = _×_

-- _,,_ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → A → B → A \\ B
-- _,,_ = _,_

-- QuotientSet : ∀ {ℓ} {A : Set ℓ} → Set ?
-- QuotientSet {_} {A} = List A \\ _↭_

-- postulate
--   transport′ : ∀ {ℓ} {A : Set ℓ} {x y : List A}
--              → x ↭ y
--                -------------------
--              → (x ,, _↭_) ≡ (y ,, _↭_)

--------------------------------------------------------------------------------------------------

-- infixr 5 _∪_ _∩_
-- postulate
--   _∪_ : ∀ {A : Set} → List A → List A → List A
--   _∩_ : ∀ {A : Set} → List A → List A → List A

-- postulate dumb : ∀ {A : Set} {x y : List A} → x ≈ y → x ∩ y ≡ y ∩ x
-- {-# BUILTIN REWRITE _≡_ #-}
-- {-# REWRITE dumb #-}


--------------------------------------------------------------------------------------------------
-- Finite sets

-- The homotopical approach could be done with hard work
-- in Cubical Agda...

-- Apparently, someone in Nijmegen is now trying it out:
-- https://twitter.com/fixpint/status/1094948274241458176


--------------------------------------------------------------------------------------------------
-- Papers

-- * Definable Quotients in Type Theory

-- * Finite Sets in Homotopy Type Theory

-- * Constructing Quotient Inductive-Inductive Types

-- * Type Theory in Type Theory using Quotient Inductive Types


--------------------------------------------------------------------------------------------------
-- Code

-- https://github.com/agda/agda-stdlib/blob/f3d4f26b64cacb273eb72fc5399c0233045b86e6/src/Relation/Binary/HeterogeneousEquality/Quotients.agda

-- https://github.com/agda/agda-stdlib/blob/f3d4f26b64cacb273eb72fc5399c0233045b86e6/src/Relation/Binary/HeterogeneousEquality/Quotients/Examples.agda#L8

-- https://github.com/agda/agda-stdlib/blob/master/src/Data/List/Relation/Binary/BagAndSetEquality.agda

-- https://github.com/agda/agda-stdlib/blob/f3d4f26b64/src/Relation/Binary/HeterogeneousEquality.agda

-- https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Lists.List.html

-- https://www.hedonisticlearning.com/posts/quotient-types-for-programmers.html

-- https://plfa.github.io/Bisimulation/

-- https://github.com/Saizan/cubical-demo/blob/master/examples/Cubical/Examples/Circle.agda
