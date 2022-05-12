--------------------------------------------------------------------------------
-- Agda Helium
--
-- Properties of core semantic components.
--------------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Semantics.Core.Properties
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Helium.Data.Pseudocode.Algebra.Properties pseudocode

open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (suc; punchIn)
open import Data.Fin.Patterns using (0F)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup; insert; map; zipWith)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Binary.Pointwise.Extensional using (ext)
open import Function using (_∘_; flip)
open import Helium.Data.Pseudocode.Core
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality

open import Helium.Semantics.Core rawPseudocode

private
  variable
    m n : ℕ
    t : Type

open ≡-Reasoning

head′-cons′ : ∀ (ts : Vec Type n) (v : ⟦ t ⟧ₜ) vs → head′ {t = t} ts (cons′ ts v vs) ≡ v
head′-cons′ []       v vs        = refl
head′-cons′ (_ ∷ ts) v vs        = refl

tail′-cons′ : ∀ (ts : Vec Type n) (v : ⟦ t ⟧ₜ) vs → tail′ {t = t} ts (cons′ ts v vs) ≡ vs
tail′-cons′ []       v vs        = refl
tail′-cons′ (_ ∷ ts) v vs        = refl

cons′-head′-tail′ : ∀ (ts : Vec Type n) (vs : ⟦ t ∷ ts ⟧ₜₛ) → cons′ ts (head′ ts vs) (tail′ ts vs) ≡ vs
cons′-head′-tail′ []       vs = refl
cons′-head′-tail′ (_ ∷ ts) vs = refl

append-cons′ : ∀ (ts : Vec Type m) (ts₁ : Vec Type n) (xs : ⟦ ts ⟧ₜₛ) (ys : ⟦ ts₁ ⟧ₜₛ) (z : ⟦ t ⟧ₜ) →
               append (t ∷ ts) ts₁ (cons′ ts z xs) ys ≡ cons′ (ts ++ ts₁) z (append ts ts₁ xs ys)
append-cons′ ts ts₁ xs ys z = cong₂ (λ x y → cons′ (ts ++ ts₁) x (append ts ts₁ y ys)) (head′-cons′ ts z xs) (tail′-cons′ ts z xs)

fetch-punchIn : ∀ (ts : Vec Type n) i t j vs v →
                subst ⟦_⟧ₜ
                  (Vecₚ.insert-punchIn ts i t j)
                  (fetch (punchIn i j) (insert ts i t) (insert′ i ts vs v)) ≡
                fetch j ts vs
fetch-punchIn ts       0F      t j       vs v = cong (fetch j ts) (tail′-cons′ ts v vs)
fetch-punchIn (x ∷ ts) (suc i) t 0F      vs v = head′-cons′ (insert ts i t) (head′ ts vs) (insert′ i ts (tail′ ts vs) v)
fetch-punchIn (x ∷ ts) (suc i) t (suc j) vs v = begin
  subst ⟦_⟧ₜ (Vecₚ.insert-punchIn ts i t j) (fetch (punchIn i j) (insert ts i t) (tail′ (insert ts i t) (cons′ (insert ts i t) (head′ ts vs) (insert′ i ts (tail′ ts vs) v))))
    ≡⟨ cong (subst ⟦_⟧ₜ (Vecₚ.insert-punchIn ts i t j) ∘ fetch (punchIn i j) (insert ts i t)) (tail′-cons′ (insert ts i t) (head′ ts vs) (insert′ i ts (tail′ ts vs) v)) ⟩
  subst ⟦_⟧ₜ (Vecₚ.insert-punchIn ts i t j) (fetch (punchIn i j) (insert ts i t) (insert′ i ts (tail′ ts vs) v))
    ≡⟨ fetch-punchIn ts i t j (tail′ ts vs) v ⟩
  fetch j ts (tail′ ts vs)
    ∎

fetch-updateAt-≡ : ∀ i (ts : Vec Type n) v vs → fetch i ts (updateAt i ts v vs) ≡ v
fetch-updateAt-≡ 0F      (_ ∷ ts) v vs = head′-cons′ ts v (tail′ ts vs)
fetch-updateAt-≡ (suc i) (_ ∷ ts) v vs = begin
  fetch (suc i) (_ ∷ ts) (updateAt (suc i) (_ ∷ ts) v vs)
    ≡⟨ cong (fetch i ts) (tail′-cons′ ts (head′ ts vs) (updateAt i ts v (tail′ ts vs))) ⟩
  fetch i ts (updateAt i ts v (tail′ ts vs))
    ≡⟨ fetch-updateAt-≡ i ts v (tail′ ts vs) ⟩
  v
    ∎

fetch-updateAt-≢ : ∀ {i j} → i ≢ j → ∀ (ts : Vec Type n) v vs → fetch j ts (updateAt i ts v vs) ≡ fetch j ts vs
fetch-updateAt-≢ {i = 0F}    {j = 0F}    i≢j ts       v vs = ⊥-elim (i≢j refl)
fetch-updateAt-≢ {i = 0F}    {j = suc j} i≢j (_ ∷ ts) v vs = cong (fetch j ts) (tail′-cons′ ts v (tail′ ts vs))
fetch-updateAt-≢ {i = suc i} {j = 0F}    i≢j (_ ∷ ts) v vs = head′-cons′ ts (head′ ts vs) (updateAt i ts v (tail′ ts vs))
fetch-updateAt-≢ {i = suc i} {j = suc j} i≢j (_ ∷ ts) v vs = begin
  fetch j ts (tail′ ts (cons′ ts (head′ ts vs) (updateAt i ts v (tail′ ts vs))))
    ≡⟨ cong (fetch j ts) (tail′-cons′ ts (head′ ts vs) (updateAt i ts v (tail′ ts vs))) ⟩
  fetch j ts (updateAt i ts v (tail′ ts vs))
    ≡⟨ fetch-updateAt-≢ (i≢j ∘ cong suc) ts v (tail′ ts vs) ⟩
  fetch j ts (tail′ ts vs) ∎

≈-reflexive : ⦃ hasEq : HasEquality t ⦄ → ∀ (x y : ⟦ t ⟧ₜ) → x ≡ y → x ≈ y
≈-reflexive ⦃ hasEq = bool ⦄  x y eq = lift (cong lower eq)
≈-reflexive ⦃ hasEq = int ⦄   x y eq = lift (ℤ.Eq.reflexive (cong lower eq))
≈-reflexive ⦃ hasEq = fin ⦄   x y eq = lift (cong lower eq)
≈-reflexive ⦃ hasEq = real ⦄  x y eq = lift (ℝ.Eq.reflexive (cong lower eq))
≈-reflexive ⦃ hasEq = array ⦄ x y eq = ext λ i → ≈-reflexive (lookup x i) (lookup y i) (cong (flip lookup i) eq)
