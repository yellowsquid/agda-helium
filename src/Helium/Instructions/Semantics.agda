------------------------------------------------------------------------
-- Agda Helium
--
-- TODO: write some words
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Instructions.Semantics
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

import Data.Bool as Bool
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_)
open import Data.Vec using (Vec; []; _∷_; _++_; replicate)
open import Data.Vec.Relation.Unary.All as All using ([]; _∷_)
open import Function using (_∘_; id)

open import Data.Fin as Fin using (Fin; suc; fromℕ; inject₁)
open import Data.Fin.Patterns
open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
open import Helium.Data.Pseudocode.Core
open import Helium.Instructions.Base
open import Helium.Semantics.Axiomatic pseudocode
-- import Helium.Semantics.Axiomatic.Properties pseudocode as Axₚ
open import Level using (lift; lower)

private
  variable
    o k m n : ℕ
    Σ Γ Δ : Vec Type n
    t t′ : Type

_IndependentFrom_ : ⦃ HasEquality t ⦄ → Term Σ Γ Δ t → Reference Σ Γ t′ → Set _
e IndependentFrom ref = ∀ val σ γ δ → Term.Semantics.⟦ e ⟧ σ γ δ ≈ Term.Semantics.⟦ Term.subst e ref val ⟧ σ γ δ

copyMasked-mask-true : ∀ {i v beat mask} {P : Assertion State Γ Δ} {Q : Assertion State Γ Δ} →
                    P ⊆ equal (↓ mask) (lit (replicate (lift Bool.true))) →
                    P ⊆ Assertion.subst Q Q[ i , beat ] (↓ v) →
                    P ⊢ invoke copyMasked (i ∷ v ∷ beat ∷ mask ∷ []) ⊢ Q
copyMasked-mask-true {Γ = Γ} {Δ = Δ} {i = i} {v} {beat} {mask} {P} {Q} P⊆mask≡true P⊆Q[i,beat]≔v =
  invoke
    (for
      {!!}
      -- (I ∧ Assertion.subst Q′ Q[ var 0F , var 2F ] {!!})
      {!!}
      (if
        (assign {!!})
        {!!})
      {!!})

-- invoke
--   (for
--     (I ∧ Assertion.subst P′ Q[ var 0F , var 2F ] (merge (merge (select 0F) (select 1F) (↓ lit 0F)) (merge (select 2F) (select 3F) (↓ lit 0F)) (↓ lit 0F)))
--     {!!}
--     (if
--       (assign
--         {!!})
--       {!!})
--     {!!})
  where
  I : Assertion State (fin 8 ∷ bits 32 ∷ fin 4 ∷ elmtMask ∷ []) (fin 5 ∷ Γ ++ Δ)
  I = equal (var 3F) (lit (replicate (lift Bool.true)))

  Q′ = {!!} -- Assertion.Meta.weaken 0F (Assertion.Var.elimAll Q (All.map (Term.Meta.inject Δ) (All.tabulate meta)))

--   select : Fin 4 → Term State (fin 8 ∷ bits 32 ∷ fin 4 ∷ elmtMask ∷ []) (fin 5 ∷ Γ ++ Δ) (array bit 8)
--   select i = slice (if ↓ lit (inject₁ i) <? meta 0F then var 1F else ↓ ! Q[ var 0F , var 2F ]) (↓ fin (reindex {n = 8}) (tup (lit i ∷ [])))
--     where
--     reindex : ∀ {m n} → Fin (suc m) → Fin (suc (m ℕ.* n))
--     reindex {m}     {n} 0F      = Fin.inject+ (m ℕ.* n) 0F
--     reindex {suc m} {n} (suc i) = Fin.cast (ℕₚ.+-suc n (m ℕ.* n)) (Fin.raise n (reindex i))

--   -- lemma₁ : _ ⊆ _
--   -- implies lemma₁ σ γ δ (eq , p) = eq , {!!}
--   -- -- implies (Axₚ.Var.Weaken-Elim.assertion⇒ P (↓ i ∷ ↓ v ∷ ↓ beat ∷ ↓ mask ∷ [])) σ γ δ p

--   -- lemma₂ : _ ⊆ _
--   -- implies lemma₂ σ (i , v , beat , mask) δ (eq , p) = eq , {!!}

--   -- lemma₃ : _ ⊆ _
--   -- implies lemma₃ σ (e , i , v , beat , mask) δ (eq , p) = {!γ!} , {!!}

--   -- lemma₄ : _ ⊆ _
--   -- implies lemma₄ σ (e , i , v , beat , mask) δ (eq , p) = {!γ!} , {!!}

--   -- lemma₅ : _ ⊆ _
--   -- implies lemma₅ σ (i , v , beat , mask) δ (eq , p) = eq , {!!}

--   -- lemma₆ : _ ⊆ _
--   -- implies lemma₆ σ γ δ (eq , p) = {!!} , {!!}
