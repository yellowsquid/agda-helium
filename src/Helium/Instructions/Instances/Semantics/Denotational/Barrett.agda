------------------------------------------------------------------------
-- Agda Helium
--
-- Implementation of Barrett reduction.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Instructions.Instances.Semantics.Denotational.Barrett
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Helium.Data.Pseudocode.Algebra.Properties pseudocode

open import Data.Fin.Patterns
import Data.Integer as 𝕀
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.DivMod as ℕ′
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; _∷_; []; replicate)
open import Helium.Data.Pseudocode.Core
open import Helium.Instructions.Base
open import Helium.Instructions.Core
open import Helium.Instructions.Instances.Barrett
open import Helium.Semantics.Core rawPseudocode
open import Helium.Semantics.Denotational.Core rawPseudocode as Sem
open import Level using (lift; lower)
import Relation.Binary.PropositionalEquality as P

proof-2≉0 : 2≉0
proof-2≉0 = {!!}

private
  variable
    n : ℕ
    Γ : Vec Type n


open Sem.Semantics proof-2≉0

copyMasked-no-vpt : ∀ σ i v beat masked →
                    _≈′_ {t = tuple State}
                    (proj₁ (assign {Γ = _ ∷ _ ∷ []} Q[ var 0F , var 1F ] v (σ , i , beat) (σ , i , beat)))
                    (proc copyMasked (σ , i , v , beat , masked))
copyMasked-no-vpt (S , R , _ , _ , _ , _ , _) i v beat masked = {!!} , {!!} , {!!} , {!!} , lift {!P.refl!} , lift {!P.refl!} , lift {!State!}

-- barrettCorrect : ∀ (σ : ⟦ State ⟧ₜ′) (l n : ℕ) (t z : VecReg) (im : GenReg) →
--                  ref (VPR-P0 {Γ = []}) (σ , _) ≈ replicate (lift 0𝔹) →
--                  ref (VPR-mask {Γ = []}) (σ , _) ≈ replicate (lift 0𝔹) →
--                  let m = 2 ℕ.^ l ℕ′./ suc n in
--                  -- let σ′ = proc (barret (sliceⁱ 0 (lit (𝕀.+ m))) (sliceⁱ 0 (lit 𝕀.-[1+ n ])) t z im) (σ , _) in
--                  let σ′ = proc (barret ? ? t z im) (σ , _) in
--                  let Q[z,_] = λ beat → sint {Γ = []} (! Q[ lit z , lit beat ]) in
--                  ∀ beat → ∃ λ a → n ℤ.× a ℤ.+ lower (expr Q[z, beat ] (σ′ , _)) ℤ.≈ lower (expr Q[z, beat ] (σ , _))
--                  -- ∀ beat → ∃ λ q → ∃ λ r → proj₂ (⟦ index Q (lit (z ′f)))
-- barrettCorrect σ l n t z im VPR-P0≡0 VPR-mask≡0 beat = a , (begin-equality
--   n ℤ.× a ℤ.+ lower (expr Q[z, beat ] (? , _)) ≈⟨ {!!} ⟩
--   {!!} ∎)
--   where
--   open ℤ.Reasoning
--   a = {!!}
--   m = 2 ℕ.^ l ℕ′./ suc n
--   σ′ = ?
--   Q[z,_] = λ beat → sint {Γ = []} (! Q[ lit z , lit beat ])

--   -- σ′ = ⟦ barret (sliceⁱ 0 (lit (m ′i))) (sliceⁱ 0 (- lit (suc n ′i))) t z im ⟧ᵖ σ _
