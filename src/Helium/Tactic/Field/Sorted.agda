------------------------------------------------------------------------
-- Agda Helium
--
-- Sorted lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Helium.Tactic.Field.Sorted
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂) where

open StrictTotalOrder strictTotalOrder renaming (Carrier to A)

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Linked as Linked using (Linked)
open import Level using (_⊔_)
open import Relation.Unary as U using (Pred; _⊆_)
open import Relation.Binary as B
open import Relation.Binary.Construct.StrictToNonStrict _≈_ _<_

-----------------------------------------------------------------------
-- Definition

Sorted : Pred (List A) (a ⊔ ℓ₂)
Sorted xs = Linked _<_ xs

------------------------------------------------------------------------
-- Operations

module _ {x y xs} where

  head : Sorted (x ∷ y ∷ xs) → x < y
  head = Linked.head

  tail : Sorted (x ∷ xs) → Sorted xs
  tail = Linked.tail

------------------------------------------------------------------------
-- Properties of predicates preserved by Sorted

sorted? : U.Decidable Sorted
sorted? = Linked.linked? _<?_

irrelevant : B.Irrelevant _<_ → U.Irrelevant Sorted
irrelevant = Linked.irrelevant

satisfiable : U.Satisfiable Sorted
satisfiable = Linked.satisfiable
