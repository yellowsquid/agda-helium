--------------------------------------------------------------------------------
-- Agda Helium
--
-- Ring solver tactic using integers as coefficients
--------------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Helium.Algebra.Ordered.StrictTotal.Bundles using (CommutativeRing)
import Helium.Algebra.Ordered.StrictTotal.Properties.CommutativeRing as Ringₚ
open import Relation.Nullary

module Helium.Tactic.CommutativeRing.NonReflective
  {ℓ₁ ℓ₂ ℓ₃}
  (R : CommutativeRing ℓ₁ ℓ₂ ℓ₃)
  (1≉0 : let module R = CommutativeRing R in ¬ R.1# R.≈ R.0#)
  where

open import Data.Bool.Base
open import Data.Sign using (Sign) renaming (_*_ to _S*_)
open import Level using (0ℓ; _⊔_)

open import Relation.Binary.Reasoning.StrictPartialOrder (CommutativeRing.strictPartialOrder R)

module R where
  open CommutativeRing R public
     renaming
     ( trans to <-trans
     ; irrefl to <-irrefl
     ; asym to <-asym
     ; 0<a+0<b⇒0<ab to x>0∧y>0⇒xy>0
     )

  open Ringₚ R public

  infixr 2 _,_

  record Positive : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    constructor _,_
    field
      val   : Carrier
      proof : val ≥ 0#

  open Positive

  infixl 6 _*⁺_ _*′_
  infix 5 _◃_

  _*⁺_ : Positive → Positive → Positive
  +x *⁺ +y = +x .val * +y .val , x≥0∧y≥0⇒x*y≥0 (+x .proof) (+y .proof)

  _◃_ : Sign → Positive → Carrier
  Sign.- ◃ +x = - (+x .val)
  Sign.+ ◃ +x = +x .val

  sign : Carrier → Sign
  sign x with does (x <? 0#)
  ... | true  = Sign.-
  ... | false = Sign.+

  ∣_∣ : Carrier → Positive
  ∣ x ∣ with x <? 0#
  ... | yes x<0 = - x , <⇒≤ (x<0⇒-x>0 x<0)
  ... | no x≮0  = x , ≮⇒≥ x≮0

  ◃-congˡ : ∀ s +x +y → +x .val ≈ +y .val → s ◃ +x ≈ s ◃ +y
  ◃-congˡ Sign.- +x +y x≈y = -‿cong x≈y
  ◃-congˡ Sign.+ +x +y x≈y = x≈y

  _*′_ : Carrier → Carrier → Carrier
  x *′ y = sign x S* sign y ◃ ∣ x ∣ *⁺ ∣ y ∣

  *′≈* : ∀ x y → x *′ y ≈ x * y
  *′≈* x y with x <? 0# | y <? 0#
  ... | yes x<0 | yes y<0 = -x*-y≈x*y x y
  ... | yes x<0 | no y≮0  = begin-equality
    - (- x * y) ≈⟨ -‿cong (-‿*-distribˡ x y) ⟩
    - - (x * y) ≈⟨ -‿involutive (x * y) ⟩
    x * y       ∎
  ... | no x≮0  | yes y<0 = begin-equality
    - (x * - y) ≈⟨ -‿cong (-‿*-distribʳ x y) ⟩
    - - (x * y) ≈⟨ -‿involutive (x * y) ⟩
    x * y       ∎
  ... | no x≮0  | no y≮0  = Eq.refl

open import Algebra.Bundles using (Ring)
open import Algebra.Morphism
import Data.Bool.Properties as Boolₚ
open import Data.Empty using (⊥-elim)
open import Data.Integer as ℤ hiding (suc)
open import Data.Integer.Properties as ℤₚ
open import Data.Maybe.Base
open import Data.Nat.Base as ℕ using (ℕ; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕₚ
open import Data.Product
import Data.Unit
open import Data.Vec hiding (_⊛_)
open import Data.Vec.N-ary
open import Function

open import Relation.Binary.PropositionalEquality

open import Tactic.RingSolver.Core.AlmostCommutativeRing
open import Tactic.RingSolver.Core.Expression public
open import Tactic.RingSolver.Core.Polynomial.Parameters

private
  T-≡ : ∀ {x} → T x ⇔ x ≡ true
  T-≡ {false} = mk⇔ (λ ()) (λ ())
  T-≡ {true}  = mk⇔ (λ _ → refl) (λ _ → _)

  T-≡′ : ∀ {x} → T (not x) ⇔ x ≡ false
  T-≡′ {false} = mk⇔ (λ _ → refl) (λ _ → _)
  T-≡′ {true}  = mk⇔ (λ ()) λ ()

  T-¬ : ∀ {x} → T (not x) ⇔ (¬ T x)
  T-¬ {false} = mk⇔ (λ _ ⊥ → ⊥) (λ ¬⊥ → _)
  T-¬ {true}  = mk⇔ (λ ⊥ _ → ⊥) (λ ¬⊤ → ¬⊤ _)

module Ops where
  ℤ-coeff : RawCoeff 0ℓ 0ℓ
  ℤ-coeff = record
    { rawRing = Ring.rawRing ℤₚ.+-*-ring
    ; isZero = does ∘ (0ℤ ℤ.≟_)
    }

  ring : AlmostCommutativeRing ℓ₁ ℓ₂
  ring = fromCommutativeRing R.Unordered.commutativeRing (decToMaybe ∘ (R.0# R.≟_))

  ℤ⟶R : RawCoeff.rawRing ℤ-coeff -Raw-AlmostCommutative⟶ ring
  ℤ⟶R = record
    { ⟦_⟧    = ⟦_⟧
    ; +-homo = +-homo
    ; *-homo = *-homo
    ; -‿homo = -‿homo
    ; 0-homo = R.Eq.refl
    ; 1-homo = R.Eq.refl
    }
    where
    ⟦_⟧ : ℤ → R.Carrier
    ⟦ + n      ⟧ = n R.× R.1#
    ⟦ -[1+ n ] ⟧ = R.- (suc n R.× R.1#)

    ∸-homo : ∀ {m n} → m ℕ.≤ n → ⟦ + (n ℕ.∸ m) ⟧ R.≈ ⟦ + n ⟧ R.- ⟦ + m ⟧
    ∸-homo {.0}     {n}      z≤n       = begin-equality
      n R.× R.1#          ≈˘⟨ R.+-identityʳ _ ⟩
      n R.× R.1# R.+ R.0# ≈˘⟨ R.+-congˡ R.-0≈0 ⟩
      n R.× R.1# R.- R.0# ∎
    ∸-homo {.suc m} {.suc n} (s≤s m≤n) = begin-equality
      (n ℕ.∸ m) R.× R.1#                                ≈⟨  ∸-homo m≤n ⟩
      n R.× R.1# R.- m R.× R.1#                         ≈˘⟨ R.+-congʳ (R.+-identityʳ _) ⟩
      n R.× R.1# R.+ R.0# R.- m R.× R.1#                ≈˘⟨ R.+-congʳ (R.+-congˡ (R.-‿inverseʳ R.1#)) ⟩
      n R.× R.1# R.+ (R.1# R.- R.1#) R.- m R.× R.1#     ≈˘⟨ R.+-congʳ (R.+-assoc _ _ _) ⟩
      n R.× R.1# R.+ R.1# R.- R.1# R.- m R.× R.1#       ≈⟨  R.+-assoc _ _ _ ⟩
      n R.× R.1# R.+ R.1# R.+ (R.- R.1# R.- m R.× R.1#) ≈⟨  R.+-cong (R.+-comm _ R.1#) (R.-‿+-comm R.1# _) ⟩
      R.1# R.+ n R.× R.1# R.- (R.1# R.+ m R.× R.1#)     ≈˘⟨ R.+-cong (R.1+× n R.1#) (R.-‿cong (R.1+× m R.1#)) ⟩
      suc n R.× R.1# R.- suc m R.× R.1#                 ∎

    -‿homo : ∀ n → ⟦ - n ⟧ R.≈ R.- ⟦ n ⟧
    -‿homo -[1+ n ] = R.Eq.sym (R.-‿involutive _)
    -‿homo +0       = R.Eq.sym R.-0≈0
    -‿homo +[1+ n ] = R.Eq.refl

    ⊖-homo : ∀ m n → ⟦ m ⊖ n ⟧ R.≈ ⟦ + m ⟧ R.- ⟦ + n ⟧
    ⊖-homo m n with m ℕ.<ᵇ n in eq
    ... | true  = begin-equality
      ⟦ - (+ (n ℕ.∸ m)) ⟧         ≈⟨  -‿homo (+ (n ℕ.∸ m)) ⟩
      R.- ⟦ + (n ℕ.∸ m) ⟧         ≈⟨  R.-‿cong (∸-homo (ℕₚ.<⇒≤ (ℕₚ.<ᵇ⇒< m n (Equivalence.g T-≡ eq)))) ⟩
      R.- (⟦ + n ⟧ R.- ⟦ + m ⟧)   ≈˘⟨ R.-‿+-comm ⟦ + n ⟧ (R.- ⟦ + m ⟧) ⟩
      R.- ⟦ + n ⟧ R.- R.- ⟦ + m ⟧ ≈⟨  R.+-congˡ (R.-‿involutive ⟦ + m ⟧) ⟩
      R.- ⟦ + n ⟧ R.+ ⟦ + m ⟧     ≈⟨  R.+-comm (R.- ⟦ + n ⟧) ⟦ + m ⟧ ⟩
      ⟦ + m ⟧ R.- ⟦ + n ⟧         ∎
    ... | false = ∸-homo (ℕₚ.≮⇒≥ {m} {n} (Equivalence.f T-¬ (Equivalence.g T-≡′ eq) ∘ ℕₚ.<⇒<ᵇ))

    +-homo : ∀ m n → ⟦ m + n ⟧ R.≈ ⟦ m ⟧ R.+ ⟦ n ⟧
    +-homo -[1+ m ] -[1+ n ] = begin-equality
      R.- (suc (suc (m ℕ.+ n)) R.× R.1#)        ≡˘⟨ cong (λ x → R.- (x R.× R.1#)) (ℕₚ.+-suc (suc m) n) ⟩
      R.- ((suc m ℕ.+ suc n) R.× R.1#)          ≈⟨  R.-‿cong (R.×-homo-+ R.1# (suc m) (suc n)) ⟩
      R.- (suc m R.× R.1# R.+ suc n R.× R.1#)   ≈˘⟨ R.-‿+-comm _ _ ⟩
      R.- (suc m R.× R.1#) R.- (suc n R.× R.1#) ∎
    +-homo -[1+ m ] (+ n)    = begin-equality
      ⟦ n ⊖ suc m ⟧             ≈⟨ ⊖-homo n (suc m) ⟩
      ⟦ + n ⟧ R.+ ⟦ -[1+ m ] ⟧  ≈⟨ R.+-comm ⟦ + n ⟧ ⟦ -[1+ m ] ⟧ ⟩
      ⟦ -[1+ m ] ⟧ R.+ ⟦ + n ⟧  ∎
    +-homo (+ m)    -[1+ n ] = ⊖-homo m (suc n)
    +-homo (+ m)    (+ n)    = R.×-homo-+ R.1# m n

    ∣∙∣-homo : ∀ n → ⟦ + ∣ n ∣ ⟧ R.≈ R.Positive.val R.∣ ⟦ n ⟧ ∣
    ∣∙∣-homo n with ⟦ n ⟧ R.<? R.0#
    ∣∙∣-homo (+ n)    | yes n<0 = ⊥-elim (R.<⇒≱ n<0 (R.x≥0⇒n×x≥0 n R.0≤1))
    ∣∙∣-homo (+ n)    | no n≮0  = R.Eq.refl
    ∣∙∣-homo -[1+ n ] | yes n<0 = R.Eq.sym (R.-‿involutive _)
    ∣∙∣-homo -[1+ n ] | no n≮0  = ⊥-elim (n≮0 (R.x>0⇒-x<0 (R.n≢0∧x>0⇒n×x>0 (suc n) (R.x≉y⇒0<1 1≉0))))

    sign-homo : ∀ n → sign n ≡ R.sign ⟦ n ⟧
    sign-homo n with ⟦ n ⟧ R.<? R.0#
    sign-homo (+ n)    | yes n<0 = ⊥-elim (R.<⇒≱ n<0 (R.x≥0⇒n×x≥0 n R.0≤1))
    sign-homo (+ n)    | no n≮0  = refl
    sign-homo -[1+ n ] | yes n<0 = refl
    sign-homo -[1+ n ] | no n≮0  = ⊥-elim (n≮0 (R.x>0⇒-x<0 (R.n≢0∧x>0⇒n×x>0 (suc n) (R.x≉y⇒0<1 1≉0))))

    ◃-homo : ∀ s n → ⟦ s ◃ n ⟧ R.≈ s R.◃ (⟦ + n ⟧ R., R.x≥0⇒n×x≥0 n R.0≤1)
    ◃-homo Sign.- 0       = R.Eq.sym R.-0≈0
    ◃-homo Sign.- (suc n) = R.Eq.refl
    ◃-homo Sign.+ 0       = R.Eq.refl
    ◃-homo Sign.+ (suc n) = R.Eq.refl

    *ⁿ-homo : ∀ m n → ⟦ + (m ℕ.* n) ⟧ R.≈ ⟦ + m ⟧ R.* ⟦ + n ⟧
    *ⁿ-homo 0       n = R.Eq.sym (R.zeroˡ ⟦ + n ⟧)
    *ⁿ-homo (suc m) n = begin-equality
      (n ℕ.+ m ℕ.* n) R.× R.1#                          ≈⟨  R.×-homo-+ R.1# n (m ℕ.* n) ⟩
      n R.× R.1# R.+ (m ℕ.* n) R.× R.1#                 ≈⟨  R.+-congˡ (*ⁿ-homo m n) ⟩
      n R.× R.1# R.+ m R.× R.1# R.* n R.× R.1#          ≈˘⟨ R.+-congʳ (R.*-identityˡ _) ⟩
      R.1# R.* n R.× R.1# R.+ m R.× R.1# R.* n R.× R.1# ≈˘⟨ R.distribʳ _ R.1# _ ⟩
      (R.1# R.+ m R.× R.1#) R.* n R.× R.1#              ≈˘⟨ R.*-congʳ (R.1+× m R.1#) ⟩
      suc m R.× R.1# R.* n R.× R.1#                     ∎

    *-homo : ∀ m n → ⟦ m * n ⟧ R.≈ ⟦ m ⟧ R.* ⟦ n ⟧
    *-homo m n = begin-equality
      ⟦ m * n ⟧                                          ≡⟨⟩
      ⟦ sm*sn ◃ ∣ m ∣ ℕ.* ∣ n ∣ ⟧                        ≈⟨ ◃-homo sm*sn (∣ m ∣ ℕ.* ∣ n ∣) ⟩
      sm*sn R.◃ (⟦ + (∣ m ∣ ℕ.* ∣ n ∣) ⟧ R., ∣m∣∣n∣≥0)   ≈⟨ R.◃-congˡ sm*sn _ _ (*ⁿ-homo ∣ m ∣ ∣ n ∣) ⟩
      sm*sn R.◃ (⟦ + ∣ m ∣ ⟧ R.* ⟦ + ∣ n ∣ ⟧ R., ∣mn∣≥0) ≈⟨ R.◃-congˡ sm*sn _ _ (R.*-cong (∣∙∣-homo m) (∣∙∣-homo n)) ⟩
      sm*sn R.◃ R.∣ ⟦ m ⟧ ∣ R.*⁺ R.∣ ⟦ n ⟧ ∣             ≡⟨ cong₂ (λ x y → x S* y R.◃ R.∣ ⟦ m ⟧ ∣ R.*⁺ R.∣ ⟦ n ⟧ ∣) (sign-homo m) (sign-homo n) ⟩
      Rsm*Rsn R.◃ R.∣ ⟦ m ⟧ ∣ R.*⁺ R.∣ ⟦ n ⟧ ∣           ≡⟨⟩
      ⟦ m ⟧ R.*′ ⟦ n ⟧                                   ≈⟨ R.*′≈* ⟦ m ⟧ ⟦ n ⟧ ⟩
      ⟦ m ⟧ R.* ⟦ n ⟧                                    ∎
      where
      ∣m∣∣n∣≥0 = R.x≥0⇒n×x≥0 (∣ m ∣ ℕ.* ∣ n ∣) R.0≤1
      ∣mn∣≥0 = R.x≥0∧y≥0⇒x*y≥0 (R.x≥0⇒n×x≥0 ∣ m ∣ R.0≤1) (R.x≥0⇒n×x≥0 ∣ n ∣ R.0≤1)
      sm*sn = sign m S* sign n
      Rsm*Rsn = R.sign ⟦ m ⟧ S* R.sign ⟦ n ⟧

  homo : Homomorphism 0ℓ 0ℓ ℓ₁ ℓ₂
  homo = record
    { from          = ℤ-coeff
    ; to            = ring
    ; morphism      = ℤ⟶R
    ; Zero-C⟶Zero-R = λ { +0 _  → R.Eq.refl }
    }

  open Eval R.Unordered.rawRing (_-Raw-AlmostCommutative⟶_.⟦_⟧ ℤ⟶R) public

  open import Tactic.RingSolver.Core.Polynomial.Base (Homomorphism.from homo)

  norm : ∀ {n} → Expr ℤ n → Poly n
  norm (Κ x)   = κ x
  norm (Ι x)   = ι x
  norm (x ⊕ y) = norm x ⊞ norm y
  norm (x ⊗ y) = norm x ⊠ norm y
  norm (x ⊛ i) = norm x ⊡ i
  norm (⊝ x)   = ⊟ norm x

  ⟦_⇓⟧ : ∀ {n} → Expr ℤ n → Vec R.Carrier n → R.Carrier
  ⟦ expr ⇓⟧ = ⟦ norm expr ⟧ₚ
    where open import Tactic.RingSolver.Core.Polynomial.Semantics homo renaming (⟦_⟧ to ⟦_⟧ₚ)

  correct : ∀ {n} (expr : Expr ℤ n) ρ → ⟦ expr ⇓⟧ ρ R.≈ ⟦ expr ⟧ ρ
  correct {n = n} = go
    where
    open import Tactic.RingSolver.Core.Polynomial.Homomorphism homo

    go : ∀ (expr : Expr ℤ n) ρ → ⟦ expr ⇓⟧ ρ R.≈ ⟦ expr ⟧ ρ
    go (Κ x)   ρ = κ-hom x ρ
    go (Ι x)   ρ = ι-hom x ρ
    go (x ⊕ y) ρ = ⊞-hom (norm x) (norm y) ρ ⟨ R.Eq.trans ⟩ (go x ρ ⟨ R.+-cong ⟩ go y ρ)
    go (x ⊗ y) ρ = ⊠-hom (norm x) (norm y) ρ ⟨ R.Eq.trans ⟩ (go x ρ ⟨ R.*-cong ⟩ go y ρ)
    go (x ⊛ i) ρ = ⊡-hom (norm x) i ρ ⟨ R.Eq.trans ⟩ R.^-congˡ i (go x ρ)
    go (⊝ x)   ρ = ⊟-hom (norm x) ρ ⟨ R.Eq.trans ⟩ R.-‿cong (go x ρ)

  open import Relation.Binary.Reflection R.strictTotalOrder.Eq.setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public

solve : ∀ (n : ℕ) →
        (f : N-ary n (Expr ℤ n) (Expr ℤ n × Expr ℤ n)) →
        Eqʰ n R._≈_ (curryⁿ (Ops.⟦_⇓⟧ (proj₁ (Ops.close n f)))) (curryⁿ (Ops.⟦_⇓⟧ (proj₂ (Ops.close n f)))) →
        Eq  n R._≈_ (curryⁿ (Ops.⟦_⟧  (proj₁ (Ops.close n f)))) (curryⁿ (Ops.⟦_⟧  (proj₂ (Ops.close n f))))
solve = Ops.solve
{-# INLINE solve #-}

infixl 6 _⊜_
_⊜_ : ∀ {n} → Expr ℤ n → Expr ℤ n → Expr ℤ n × Expr ℤ n
_⊜_ = _,_
{-# INLINE _⊜_ #-}
