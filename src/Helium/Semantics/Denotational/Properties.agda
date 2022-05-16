------------------------------------------------------------------------
-- Agda Helium
--
-- Properties of the denotational semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (Pseudocode)

module Helium.Semantics.Denotational.Properties
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

import Data.Bool as Bool
import Data.Integer as 𝕀
open import Data.Fin as Fin using (suc; punchIn)
open import Data.Fin.Patterns using (0F)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂; uncurry)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; insert; map; zipWith)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function
open import Function.Nary.NonDependent using (congₙ)
open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
open import Helium.Data.Pseudocode.Core
open import Level using (Level; _⊔_; lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does; yes; no)

open import Helium.Semantics.Axiomatic pseudocode
import Helium.Semantics.Core.Properties pseudocode
  as Coreₚ
open import Helium.Semantics.Denotational.Core rawPseudocode
  renaming (module Semantics to Semantics′)

private
  variable
    o k m n : ℕ
    Σ Γ Δ Σ′ Γ′ Δ′ ts : Vec Type n
    t t′ : Type

  module Semantics = Semantics′ proof-2≉0

!-homo-⟦⟧ : ∀ (r : Reference Σ Γ t) σ,γ → Semantics.expr (! r) σ,γ ≡ Semantics.ref r σ,γ
!-homo-⟦⟧ (state i)          σ,γ = refl
!-homo-⟦⟧ (var i)            σ,γ = refl
!-homo-⟦⟧ [ r ]              σ,γ = cong (_∷ []) (!-homo-⟦⟧ r σ,γ)
!-homo-⟦⟧ (unbox r)          σ,γ = cong Vec.head (!-homo-⟦⟧ r σ,γ)
!-homo-⟦⟧ (slice r e)        σ,γ = cong (flip Core.sliceVec (lower (Semantics.expr e σ,γ))) (!-homo-⟦⟧ r σ,γ)
!-homo-⟦⟧ (cut r e)          σ,γ = cong (flip Core.cutVec (lower (Semantics.expr e σ,γ))) (!-homo-⟦⟧ r σ,γ)
!-homo-⟦⟧ (cast eq r)        σ,γ = cong (Core.castVec eq) (!-homo-⟦⟧ r σ,γ)
!-homo-⟦⟧ (head {ts = ts} r) σ,γ = cong (Core.head′ ts) (!-homo-⟦⟧ r σ,γ)
!-homo-⟦⟧ (tail {ts = ts} r) σ,γ = cong (Core.tail′ ts) (!-homo-⟦⟧ r σ,γ)
