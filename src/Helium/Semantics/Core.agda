------------------------------------------------------------------------
-- Agda Helium
--
-- Shared definitions between semantic systems
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Types using (RawPseudocode)

module Helium.Semantics.Core
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

private
  open module C = RawPseudocode rawPseudocode

open import Data.Bool using (Bool)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Helium.Data.Pseudocode.Core
open import Level hiding (zero; suc)

⟦_⟧ₗ : Type → Level
⟦ bool ⟧ₗ       = 0ℓ
⟦ int ⟧ₗ        = i₁
⟦ fin n ⟧ₗ      = 0ℓ
⟦ real ⟧ₗ       = r₁
⟦ bits n ⟧ₗ     = b₁
⟦ tuple n ts ⟧ₗ = helper ts
  where
  helper : ∀ {n} → Vec Type n → Level
  helper []       = 0ℓ
  helper (t ∷ ts) = ⟦ t ⟧ₗ ⊔ helper ts
⟦ array t n ⟧ₗ  = ⟦ t ⟧ₗ

⟦_⟧ₜ : ∀ t → Set ⟦ t ⟧ₗ
⟦_⟧ₜ′ : ∀ {n} ts → Set ⟦ tuple n ts ⟧ₗ

⟦ bool ⟧ₜ       = Bool
⟦ int ⟧ₜ        = ℤ
⟦ fin n ⟧ₜ      = Fin n
⟦ real ⟧ₜ       = ℝ
⟦ bits n ⟧ₜ     = Bits n
⟦ tuple n ts ⟧ₜ = ⟦ ts ⟧ₜ′
⟦ array t n ⟧ₜ  = Vec ⟦ t ⟧ₜ n

⟦ [] ⟧ₜ′          = ⊤
⟦ t ∷ [] ⟧ₜ′      = ⟦ t ⟧ₜ
⟦ t ∷ t′ ∷ ts ⟧ₜ′ = ⟦ t ⟧ₜ × ⟦ t′ ∷ ts ⟧ₜ′

⟦_⟧ₜˡ : Type → Set (b₁ ⊔ i₁ ⊔ r₁)
⟦_⟧ₜˡ′ : ∀ {n} → Vec Type n → Set (b₁ ⊔ i₁ ⊔ r₁)

⟦ bool ⟧ₜˡ       = Lift (b₁ ⊔ i₁ ⊔ r₁) Bool
⟦ int ⟧ₜˡ        = Lift (b₁ ⊔ r₁) ℤ
⟦ fin n ⟧ₜˡ      = Lift (b₁ ⊔ i₁ ⊔ r₁) (Fin n)
⟦ real ⟧ₜˡ       = Lift (b₁ ⊔ i₁) ℝ
⟦ bits n ⟧ₜˡ     = Lift (i₁ ⊔ r₁) (Bits n)
⟦ tuple n ts ⟧ₜˡ = ⟦ ts ⟧ₜˡ′ 
⟦ array t n ⟧ₜˡ  = Vec ⟦ t ⟧ₜˡ n

⟦ [] ⟧ₜˡ′          = Lift (b₁ ⊔ i₁ ⊔ r₁) ⊤
⟦ t ∷ [] ⟧ₜˡ′      = ⟦ t ⟧ₜˡ
⟦ t ∷ t′ ∷ ts ⟧ₜˡ′ = ⟦ t ⟧ₜˡ × ⟦ t′ ∷ ts ⟧ₜˡ′

fetch : ∀ {n} ts → ⟦ tuple n ts ⟧ₜ → ∀ i → ⟦ lookup ts i ⟧ₜ
fetch (_ ∷ [])     x        zero    = x
fetch (_ ∷ _ ∷ _)  (x , xs) zero    = x
fetch (_ ∷ t ∷ ts) (x , xs) (suc i) = fetch (t ∷ ts) xs i

fetchˡ : ∀ {n} ts → ⟦ tuple n ts ⟧ₜˡ → ∀ i → ⟦ lookup ts i ⟧ₜˡ
fetchˡ (_ ∷ [])     x        zero    = x
fetchˡ (_ ∷ _ ∷ _)  (x , xs) zero    = x
fetchˡ (_ ∷ t ∷ ts) (x , xs) (suc i) = fetchˡ (t ∷ ts) xs i

consˡ : ∀ {n t} ts → ⟦ t ⟧ₜˡ → ⟦ tuple n ts ⟧ₜˡ → ⟦ t ∷ ts ⟧ₜˡ′
consˡ []      x xs = x
consˡ (_ ∷ _) x xs = x , xs
