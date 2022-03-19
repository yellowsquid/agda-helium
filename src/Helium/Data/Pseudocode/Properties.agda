------------------------------------------------------------------------
-- Agda Helium
--
-- Basic properties of the pseudocode data types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Helium.Data.Pseudocode.Properties where

import Data.Nat as ℕ
open import Data.Product using (_,_; uncurry)
open import Data.Vec using ([]; _∷_)
open import Function using (_∋_)
open import Helium.Data.Pseudocode.Core
import Relation.Binary.Consequences as Consequences
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (map′)
open import Relation.Nullary.Product using (_×-dec_)

infixl 4 _≟ᵗ_ _≟ˢ_

_≟ᵗ_ : ∀ (t t′ : Type) → Dec (t ≡ t′)
bool ≟ᵗ bool = yes refl
bool ≟ᵗ int = no (λ ())
bool ≟ᵗ fin n = no (λ ())
bool ≟ᵗ real = no (λ ())
bool ≟ᵗ bit = no (λ ())
bool ≟ᵗ bits n = no (λ ())
bool ≟ᵗ tuple n x = no (λ ())
bool ≟ᵗ array t′ n = no (λ ())
int ≟ᵗ bool = no (λ ())
int ≟ᵗ int = yes refl
int ≟ᵗ fin n = no (λ ())
int ≟ᵗ real = no (λ ())
int ≟ᵗ bit = no (λ ())
int ≟ᵗ bits n = no (λ ())
int ≟ᵗ tuple n x = no (λ ())
int ≟ᵗ array t′ n = no (λ ())
fin n ≟ᵗ bool = no (λ ())
fin n ≟ᵗ int = no (λ ())
fin m ≟ᵗ fin n = map′ (cong fin) (λ { refl → refl }) (m ℕ.≟ n)
fin n ≟ᵗ real = no (λ ())
fin n ≟ᵗ bit = no (λ ())
fin n ≟ᵗ bits n₁ = no (λ ())
fin n ≟ᵗ tuple n₁ x = no (λ ())
fin n ≟ᵗ array t′ n₁ = no (λ ())
real ≟ᵗ bool = no (λ ())
real ≟ᵗ int = no (λ ())
real ≟ᵗ fin n = no (λ ())
real ≟ᵗ real = yes refl
real ≟ᵗ bit = no (λ ())
real ≟ᵗ bits n = no (λ ())
real ≟ᵗ tuple n x = no (λ ())
real ≟ᵗ array t′ n = no (λ ())
bit ≟ᵗ bool = no (λ ())
bit ≟ᵗ int = no (λ ())
bit ≟ᵗ fin n = no (λ ())
bit ≟ᵗ real = no (λ ())
bit ≟ᵗ bit = yes refl
bit ≟ᵗ bits n = no (λ ())
bit ≟ᵗ tuple n x = no (λ ())
bit ≟ᵗ array t n = no (λ ())
bits n ≟ᵗ bool = no (λ ())
bits n ≟ᵗ int = no (λ ())
bits n ≟ᵗ fin n₁ = no (λ ())
bits n ≟ᵗ real = no (λ ())
bits m ≟ᵗ bit = no (λ ())
bits m ≟ᵗ bits n = map′ (cong bits) (λ { refl → refl }) (m ℕ.≟ n)
bits n ≟ᵗ tuple n₁ x = no (λ ())
bits n ≟ᵗ array t′ n₁ = no (λ ())
tuple n x ≟ᵗ bool = no (λ ())
tuple n x ≟ᵗ int = no (λ ())
tuple n x ≟ᵗ fin n₁ = no (λ ())
tuple n x ≟ᵗ real = no (λ ())
tuple n x ≟ᵗ bit = no (λ ())
tuple n x ≟ᵗ bits n₁ = no (λ ())
tuple _ [] ≟ᵗ tuple _ [] = yes refl
tuple _ [] ≟ᵗ tuple _ (y ∷ ys) = no (λ ())
tuple _ (x ∷ xs) ≟ᵗ tuple _ [] = no (λ ())
tuple _ (x ∷ xs) ≟ᵗ tuple _ (y ∷ ys) = map′ (λ { (refl , refl) → refl }) (λ { refl → refl , refl }) (x ≟ᵗ y ×-dec tuple _ xs ≟ᵗ tuple _ ys)
tuple n x ≟ᵗ array t′ n₁ = no (λ ())
array t n ≟ᵗ bool = no (λ ())
array t n ≟ᵗ int = no (λ ())
array t n ≟ᵗ fin n₁ = no (λ ())
array t n ≟ᵗ real = no (λ ())
array t n ≟ᵗ bit = no (λ ())
array t n ≟ᵗ bits n₁ = no (λ ())
array t n ≟ᵗ tuple n₁ x = no (λ ())
array t m ≟ᵗ array t′ n = map′ (uncurry (cong₂ array)) (λ { refl → refl , refl }) (t ≟ᵗ t′ ×-dec m ℕ.≟ n)

_≟ˢ_ : ∀ (t t′ : Sliced) → Dec (t ≡ t′)
bits ≟ˢ bits = yes refl
bits ≟ˢ array x = no (λ ())
array x ≟ˢ bits = no (λ ())
array x ≟ˢ array y = map′ (cong array) (λ { refl → refl }) (x ≟ᵗ y)

bits-injective : ∀ {m n} → (Type ∋ bits m) ≡ bits n → m ≡ n
bits-injective refl = refl

array-injective₁ : ∀ {t t′ m n} → (Type ∋ array t m) ≡ array t′ n → t ≡ t′
array-injective₁ refl = refl

array-injective₂ : ∀ {t t′ m n} → (Type ∋ array t m) ≡ array t′ n → m ≡ n
array-injective₂ refl = refl

typeEqRecomp : ∀ {t t′} → .(eq : t ≡ t′) → t ≡ t′
typeEqRecomp = Consequences.dec⇒recomputable _≟ᵗ_
