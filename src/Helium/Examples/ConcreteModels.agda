{-# OPTIONS --without-K #-}

module Helium.Examples.ConcreteModels where

open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (suc; toℕ)
open import Data.Fin.Patterns using (0F)
import Data.Fin.Properties as Finₚ
open import Data.Integer as ℤ hiding (suc)
import Data.Integer.Properties as ℤₚ
import Data.Integer.DivMod as ℤDM
import Data.Nat as ℕ
import Data.Nat.DivMod as ℕDM
import Data.Nat.Properties as ℕₚ
open import Data.Integer.Solver
open import Data.Product using (_,_)
open import Data.Rational as ℚⁿ using (toℚᵘ; fromℚᵘ) renaming (↥_ to ↥ⁿ_; ↧ₙ_ to ↧ⁿₙ_; ↧_ to ↧ⁿ_)
import Data.Rational.Properties as ℚⁿₚ
open import Data.Rational.Unnormalised as ℚ
import Data.Rational.Unnormalised.Properties as ℚₚ
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function
open import Helium.Algebra.Core
open import Helium.Algebra.Definitions
open import Helium.Algebra.Ordered.StrictTotal.Bundles
open import Helium.Data.Pseudocode.Algebra using (Pseudocode)
open import Level using (0ℓ)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

integerRing : CommutativeRing 0ℓ 0ℓ 0ℓ
integerRing = record
  { isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isStrictTotalOrder = ℤₚ.<-isStrictTotalOrder
                ; ∙-cong = cong₂ ℤ._+_
                ; ∙-invariant = (λ z → ℤₚ.+-monoʳ-< z) , (λ z → ℤₚ.+-monoˡ-< z)
                }
              ; assoc = ℤₚ.+-assoc
              }
            ; identity = ℤₚ.+-identity
            }
          ; inverse = ℤₚ.+-inverse
          ; ⁻¹-cong = cong (ℤ.-_)
          }
        ; comm = ℤₚ.+-comm
        }
      ; *-isMonoid = ℤₚ.*-1-isMonoid
      ; distrib = ℤₚ.*-distrib-+
      ; zero = ℤₚ.*-zero
      ; 0<a+0<b⇒0<ab = λ 0<x 0<y → ℤₚ.positive⁻¹ (+x∧+y⇒+x*y (ℤ.positive 0<x) (ℤ.positive 0<y))
      }
    ; *-comm = ℤₚ.*-comm
    }
  }
  where
  +x∧+y⇒+x*y : ∀ {x y} → ℤ.Positive x → ℤ.Positive y → ℤ.Positive (x ℤ.* y)
  +x∧+y⇒+x*y {+[1+ x ]} {+[1+ y ]} _ _ = _

infix 7 _⁻¹
_⁻¹ : AlmostOp₁ _≃_ 0ℚᵘ
_⁻¹ {x @ (mkℚᵘ +[1+ n ] d)} x≄0 = 1/ x
_⁻¹ {x @ (mkℚᵘ +0 d)}       x≄0 = contradiction (*≡* refl) x≄0
_⁻¹ {x @ (mkℚᵘ -[1+ n ] d)} x≄0 = 1/ x

⁻¹-inverseˡ : AlmostLeftInverse _≃_ 1ℚᵘ _⁻¹ ℚ._*_
⁻¹-inverseˡ {x @ (mkℚᵘ +[1+ n ] d)} x≄0 = *≡* (solve 2 (λ d n → (d :* n) :* con 1ℤ := con 1ℤ :* (n :* d)) refl +[1+ d ] +[1+ n ])
  where open +-*-Solver
⁻¹-inverseˡ {x @ (mkℚᵘ +0       d)} x≄0 = contradiction (*≡* refl) x≄0
⁻¹-inverseˡ {x @ (mkℚᵘ -[1+ n ] d)} x≄0 = *≡* (solve 2 (λ d n → (d :* n) :* con 1ℤ := con 1ℤ :* (n :* d)) refl +[1+ d ] +[1+ n ])
  where open +-*-Solver

⁻¹-inverseʳ : AlmostRightInverse _≃_ 1ℚᵘ _⁻¹ ℚ._*_
⁻¹-inverseʳ {x @ (mkℚᵘ +[1+ n ] d)} x≄0 = *≡* (solve 2 (λ d n → (n :* d) :* con 1ℤ := con 1ℤ :* (d :* n)) refl +[1+ d ] +[1+ n ])
  where open +-*-Solver
⁻¹-inverseʳ {x @ (mkℚᵘ +0       d)} x≄0 = contradiction (*≡* refl) x≄0
⁻¹-inverseʳ {x @ (mkℚᵘ -[1+ n ] d)} x≄0 = *≡* (solve 2 (λ d n → (n :* d) :* con 1ℤ := con 1ℤ :* (d :* n)) refl +[1+ d ] +[1+ n ])
  where open +-*-Solver

⁻¹-cong : AlmostCongruent₁ _≃_ _⁻¹
⁻¹-cong {mkℚᵘ +[1+ n ] d} {mkℚᵘ +[1+ n₁ ] d₁} {x≄0} {y≄0} (*≡* x≡y) = *≡* (begin
  +[1+ d ] ℤ.* +[1+ n₁ ] ≡⟨ ℤₚ.*-comm +[1+ d ] +[1+ n₁ ] ⟩
  +[1+ n₁ ] ℤ.* +[1+ d ] ≡˘⟨ x≡y ⟩
  +[1+ n ] ℤ.* +[1+ d₁ ] ≡⟨ ℤₚ.*-comm +[1+ n ] +[1+ d₁ ] ⟩
  +[1+ d₁ ] ℤ.* +[1+ n ] ∎)
  where open ≡-Reasoning
⁻¹-cong {mkℚᵘ +[1+ n ] d} {mkℚᵘ +0 d₁}        {x≄0} {y≄0} x≃y = contradiction (*≡* refl) y≄0
⁻¹-cong {mkℚᵘ +[1+ n ] d} {mkℚᵘ -[1+ n₁ ] d₁} {x≄0} {y≄0} (*≡* x≡y) = *≡* (begin
  +[1+ d ] ℤ.* +[1+ n₁ ] ≡⟨ ℤₚ.*-comm +[1+ d ] +[1+ n₁ ] ⟩
  +[1+ n₁ ] ℤ.* +[1+ d ] ≡˘⟨ cong (ℤ.-_) x≡y ⟩
  +[1+ n ] ℤ.* -[1+ d₁ ] ≡⟨ ℤₚ.*-comm +[1+ n ] -[1+ d₁ ] ⟩
  -[1+ d₁ ] ℤ.* +[1+ n ] ∎)
  where open ≡-Reasoning
⁻¹-cong {mkℚᵘ +0 d} {mkℚᵘ n₁ d₁} {x≄0} {y≄0} x≃y = contradiction (*≡* refl) x≄0
⁻¹-cong {mkℚᵘ -[1+ n ] d} {mkℚᵘ +[1+ n₁ ] d₁} {x≄0} {y≄0} (*≡* x≡y) = *≡* (begin
  -[1+ d ] ℤ.* +[1+ n₁ ] ≡⟨ ℤₚ.*-comm -[1+ d ] +[1+ n₁ ] ⟩
  +[1+ n₁ ] ℤ.* -[1+ d ] ≡˘⟨ cong (ℤ.-_) x≡y ⟩
  +[1+ n ] ℤ.* +[1+ d₁ ] ≡⟨ ℤₚ.*-comm +[1+ n ] +[1+ d₁ ] ⟩
  +[1+ d₁ ] ℤ.* +[1+ n ] ∎)
  where open ≡-Reasoning
⁻¹-cong {mkℚᵘ -[1+ n ] d} {mkℚᵘ +0 d₁}        {x≄0} {y≄0} x≃y = contradiction (*≡* refl) y≄0
⁻¹-cong {mkℚᵘ -[1+ n ] d} {mkℚᵘ -[1+ n₁ ] d₁} {x≄0} {y≄0} (*≡* x≡y) = *≡* (begin
  -[1+ d ] ℤ.* +[1+ n₁ ] ≡⟨ ℤₚ.*-comm -[1+ d ] +[1+ n₁ ] ⟩
  +[1+ n₁ ] ℤ.* -[1+ d ] ≡˘⟨ x≡y ⟩
  +[1+ n ] ℤ.* -[1+ d₁ ] ≡⟨ ℤₚ.*-comm +[1+ n ] -[1+ d₁ ] ⟩
  -[1+ d₁ ] ℤ.* +[1+ n ] ∎)
  where open ≡-Reasoning

rationalField : Field 0ℓ 0ℓ 0ℓ
rationalField = record
  { isField = record
    { isDivisionRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isStrictTotalOrder = ℚₚ.<-isStrictTotalOrder
                ; ∙-cong = ℚₚ.+-cong
                ; ∙-invariant = (λ z → ℚₚ.+-monoʳ-< z) , (λ z → ℚₚ.+-monoˡ-< z)
                }
              ; assoc = ℚₚ.+-assoc
              }
            ; identity = ℚₚ.+-identity
            }
          ; inverse = ℚₚ.+-inverse
          ; ⁻¹-cong = ℚₚ.-‿cong
          }
        ; comm = ℚₚ.+-comm
        }
      ; *-isAlmostGroup = record
        { isMonoid = ℚₚ.*-1-isMonoid
        ; inverse = ⁻¹-inverseˡ , ⁻¹-inverseʳ
        ; ⁻¹-cong = ⁻¹-cong
        }
      ; distrib = ℚₚ.*-distrib-+
      ; zero = ℚₚ.*-zero
      ; 0<a+0<b⇒0<ab = λ {x} {y} 0<x 0<y → ℚₚ.positive⁻¹ (+x∧+y⇒+x*y {x} {y} (ℚ.positive 0<x) (ℚ.positive 0<y))
      }
    ; *-comm = ℚₚ.*-comm
    }
  }
  where
  +x∧+y⇒+x*y : ∀ {x y} → ℚ.Positive x → ℚ.Positive y → ℚ.Positive (x ℚ.* y)
  +x∧+y⇒+x*y {mkℚᵘ +[1+ x ] d} {mkℚᵘ +[1+ y ] d₁} _ _ = _

floor : ℚᵘ → ℤ
floor x = ↥ⁿ (fromℚᵘ x) ℤDM.div ↧ⁿ (fromℚᵘ x)

floor-cong : ∀ {x y} → x ≃ y → floor x ≡ floor y
floor-cong x≃y = cong (λ z → (↥ⁿ z) ℤDM.div (↧ⁿ z)) (ℚⁿₚ.fromℚᵘ-cong x≃y)

postulate
  floor-mono : ∀ {x y} → x ℚ.≤ y → floor x ℤ.≤ floor y
  floor-floor : ∀ x y → x ℚ.< mkℚᵘ y 0 → floor x ℤ.< y
  floor[x/1]≡x : ∀ x → floor (mkℚᵘ x 0) ≡ x

-- floor-mono : ∀ {x y} → x ℚ.≤ y → floor x ℤ.≤ floor y
-- floor-mono {x} {y} x≤y = begin
--   ↥ⁿ xⁿ ℤDM.div ↧ⁿ xⁿ                            ≡⟨  ℤDM.div-pos-is-divℕ (↥ⁿ xⁿ) (↧ⁿₙ xⁿ) ⟩
--   ↥ⁿ xⁿ ℤDM.divℕ ↧ⁿₙ xⁿ                          ≡⟨  {!!} ⟩
--   (↥ⁿ xⁿ ℤ.* ↧ⁿ yⁿ) ℤDM.divℕ (↧ⁿₙ xⁿ ℕ.* ↧ⁿₙ yⁿ) ≤⟨  {!ℚⁿₚ.drop-*≤* xⁿ≤yⁿ!} ⟩
--   (↥ⁿ yⁿ ℤ.* ↧ⁿ xⁿ) ℤDM.divℕ (↧ⁿₙ xⁿ ℕ.* ↧ⁿₙ yⁿ) ≡⟨  {!!} ⟩
--   (↥ⁿ yⁿ ℤ.* ↧ⁿ xⁿ) ℤDM.divℕ (↧ⁿₙ yⁿ ℕ.* ↧ⁿₙ xⁿ) ≡˘⟨ {!!} ⟩
--   ↥ⁿ yⁿ ℤDM.divℕ ↧ⁿₙ yⁿ                          ≡˘⟨ ℤDM.div-pos-is-divℕ (↥ⁿ yⁿ) (↧ⁿₙ yⁿ) ⟩
--   ↥ⁿ yⁿ ℤDM.div ↧ⁿ yⁿ                            ∎
--   where
--   xⁿ = fromℚᵘ x
--   yⁿ = fromℚᵘ y

--   xⁿ≤yⁿ : xⁿ ℚⁿ.≤ yⁿ
--   xⁿ≤yⁿ = ℚⁿₚ.toℚᵘ-cancel-≤ (begin
--     toℚᵘ xⁿ ≈⟨  ℚⁿₚ.toℚᵘ-fromℚᵘ x ⟩
--     x       ≤⟨  x≤y ⟩
--     y       ≈˘⟨ ℚⁿₚ.toℚᵘ-fromℚᵘ y ⟩
--     toℚᵘ yⁿ ∎)
--     where open ℚₚ.≤-Reasoning

--   n*m/o*m≡n/o : ∀ m n o → n ℤ.* +[1+ m ] ℤDM.divℕ (ℕ.suc o ℕ.* ℕ.suc m) ≡ n ℤDM.divℕ (ℕ.suc o)
--   n*m/o*m≡n/o m (+ n)    o = begin-equality
--     (+ n ℤ.* +[1+ m ]) ℤDM.divℕ (ℕ.suc o ℕ.* ℕ.suc m) ≡⟨ cong (ℤDM._divℕ _) (ℤₚ.pos-distrib-* n (ℕ.suc m)) ⟩
--     + ((n ℕ.* ℕ.suc m) ℕDM./ (ℕ.suc o ℕ.* ℕ.suc m))   ≡⟨ cong +_ (ℕDM./-congʳ {m = n ℕ.* ℕ.suc m} (ℕₚ.*-comm (ℕ.suc o) (ℕ.suc m))) ⟩
--     + ((n ℕ.* ℕ.suc m) ℕDM./ (ℕ.suc m ℕ.* ℕ.suc o))   ≡⟨ cong +_ (ℕDM./-congˡ (ℕₚ.*-comm n (ℕ.suc m))) ⟩
--     + ((ℕ.suc m ℕ.* n) ℕDM./ (ℕ.suc m ℕ.* ℕ.suc o))   ≡⟨ cong +_ (ℕDM.m*n/m*o≡n/o (ℕ.suc m) n (ℕ.suc o)) ⟩
--     + (n ℕDM./ ℕ.suc o)                               ∎
--     where open ℤₚ.≤-Reasoning
--   n*m/o*m≡n/o m -[1+ n ] o with ℕ.suc n ℕDM.divMod ℕ.suc o | (ℕ.suc n ℕ.* ℕ.suc m) ℕDM.divMod (ℕ.suc o ℕ.* ℕ.suc m)
--   ... | ℕDM.result q r eq | ℕDM.result q₁ r₁ eq₁ = {!!}
--     where
--     divMod-scale : ∀ m n o {o≢0} {o*1+m≢0} → ((n ℕ.* ℕ.suc m) ℕDM.mod (o ℕ.* ℕ.suc m)) {o*1+m≢0} ≡ Fin.combine ((n ℕDM.mod o) {o≢0}) 0F
--     divMod-scale 0         n o = {!!}
--     divMod-scale (ℕ.suc m) n o = {!!}

-- floor[x/1]≡x : ∀ x → floor (mkℚᵘ x 0) ≡ x
-- floor[x/1]≡x (+ n)    = {!!}
-- floor[x/1]≡x -[1+ n ] = {!!}

≤⇒<⊎≡ : ∀ {x y} → x ℤ.≤ y → x ℤ.< y ⊎ x ≡ y
≤⇒<⊎≡ {x} {y} x≤y with ℤₚ.<-cmp x y
... | tri< x<y _ _ = inj₁ x<y
... | tri≈ _ x≡y _ = inj₂ x≡y
... | tri> _ _ x>y = contradiction x>y (ℤₚ.≤⇒≯ x≤y)

discrete : ∀ x y → (y ℤ.< x ⊎ y ≡ x) ⊎ (x ℤ.+ 1ℤ ℤ.< y ⊎ x ℤ.+ 1ℤ ≡ y)
discrete x y with ℤₚ.<-cmp x y
... | tri< x<y _ _ = inj₂ (≤⇒<⊎≡ (ℤₚ.≤-trans (ℤₚ.≤-reflexive (ℤₚ.+-comm x 1ℤ)) (ℤₚ.i<j⇒suc[i]≤j x<y)))
... | tri≈ _ x≡y _ = inj₁ (inj₂ (sym x≡y))
... | tri> _ _ x>y = inj₁ (inj₁ x>y)

pseudocode : Pseudocode 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ 0ℓ
pseudocode = record
  { integerRing = integerRing
  ; realField = rationalField
  ; integerDiscrete = discrete
  ; 1≉0 = λ ()
  ; _/1 = flip mkℚᵘ 0
  ; ⌊_⌋ = floor
  ; /1-isHomo = record
    { +-isGroupHomomorphism = record
      { isMonoidHomomorphism = record
        { isMagmaHomomorphism = record
          { isOrderHomomorphism = record
            { cong = ℚₚ.≃-reflexive ∘ cong (flip mkℚᵘ 0)
            ; mono = *<* ∘ ℤₚ.*-monoʳ-<-pos 0
            }
          ; homo = λ x y → *≡* (solve 2 (λ x y → ((x :+ y) :* con 1ℤ) := (((x :* con 1ℤ) :+ (y :* con 1ℤ)) :* con 1ℤ)) refl x y)
          }
        ; ε-homo = *≡* refl
        }
      ; ⁻¹-homo = λ x → *≡* refl
      }
    ; *-homo = λ x y → *≡* refl
    ; 1#-homo = *≡* refl
    }
  ; ⌊⌋-isHomo = record
    { cong = floor-cong
    ; mono = ≤⇒<⊎≡ ∘ floor-mono ∘ [ ℚₚ.<⇒≤ , ℚₚ.≤-reflexive ]′
    }
  ; ⌊⌋-floor = floor-floor
  -- λ
  --   { x y (*<* ↥x*1<y*↧x) → ℤₚ.*-cancelʳ-<-nonNeg (↧ₙ x) $ (begin-strict
  --     floor x ℤ.* ↧ x           ≡˘⟨ cong (ℤ._* (↧ x)) (ℤDM.div-pos-is-divℕ (↥ x) (↧ₙ x)) ⟩
  --     (↥ x ℤDM.div ↧ x) ℤ.* ↧ x ≤⟨  ℤDM.[n/d]*d≤n (↥ x) (↧ x) ⟩
  --     ↥ x                       ≡˘⟨ ℤₚ.*-identityʳ (↥ x) ⟩
  --     ↥ x ℤ.* 1ℤ                <⟨  ↥x*1<y*↧x ⟩
  --     y ℤ.* ↧ x                 ∎)
  --   }
  ; ⌊x/1⌋≈x = floor[x/1]≡x
  }
  where
  open ℤₚ.≤-Reasoning
  open +-*-Solver
