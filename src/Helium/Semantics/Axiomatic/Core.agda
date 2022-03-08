------------------------------------------------------------------------
-- Agda Helium
--
-- Base definitions for the axiomatic semantics
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Types using (RawPseudocode)

module Helium.Semantics.Axiomatic.Core
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

private
  open module C = RawPseudocode rawPseudocode

open import Data.Bool as Bool using (Bool)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Induction as Natᵢ
import Data.Nat.Properties as ℕₚ
open import Data.Product as × using (_×_; _,_; uncurry)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function using (_on_)
open import Helium.Data.Pseudocode.Core
open import Helium.Data.Pseudocode.Properties
import Induction.WellFounded as Wf
open import Level using (_⊔_; Lift; lift)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; does; yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness; map′)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary using (_⊆_)

private
  variable
    t t′     : Type
    m n      : ℕ
    Γ Δ Σ ts : Vec Type m

⟦_⟧ₜ  : Type → Set (b₁ ⊔ i₁ ⊔ r₁)
⟦_⟧ₜ′ : Vec Type n → Set (b₁ ⊔ i₁ ⊔ r₁)

⟦ bool ⟧ₜ       = Lift (b₁ ⊔ i₁ ⊔ r₁) Bool
⟦ int ⟧ₜ        = Lift (b₁ ⊔ r₁) ℤ
⟦ fin n ⟧ₜ      = Lift (b₁ ⊔ i₁ ⊔ r₁) (Fin n)
⟦ real ⟧ₜ       = Lift (b₁ ⊔ i₁) ℝ
⟦ bit ⟧ₜ        = Lift (i₁ ⊔ r₁) Bit
⟦ bits n ⟧ₜ     = Vec ⟦ bit ⟧ₜ n
⟦ tuple n ts ⟧ₜ = ⟦ ts ⟧ₜ′ 
⟦ array t n ⟧ₜ  = Vec ⟦ t ⟧ₜ n

⟦ [] ⟧ₜ′     = Lift (b₁ ⊔ i₁ ⊔ r₁) ⊤
⟦ t ∷ ts ⟧ₜ′ = ⟦ t ⟧ₜ × ⟦ ts ⟧ₜ′

fetch : ∀ i → ⟦ Γ ⟧ₜ′ → ⟦ lookup Γ i ⟧ₜ
fetch {Γ = _ ∷ _} 0F      (x , _)  = x
fetch {Γ = _ ∷ _} (suc i) (_ , xs) = fetch i xs

Transform : Vec Type m → Type → Set (b₁ ⊔ i₁ ⊔ r₁)
Transform ts t = ⟦ ts ⟧ₜ′ → ⟦ t ⟧ₜ

Predicate : Vec Type m → Set (b₁ ⊔ i₁ ⊔ r₁)
Predicate ts =  ⟦ ts ⟧ₜ′ → Bool
