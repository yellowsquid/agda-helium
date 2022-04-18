------------------------------------------------------------------------
-- Agda Helium
--
-- Base definitions for semantics
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)

module Helium.Semantics.Core
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

private
  open module C = RawPseudocode rawPseudocode

open import Algebra.Core using (Op₁)
open import Data.Bool as Bool using (Bool)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Fin.Patterns
import Data.Fin.Properties as Finₚ
open import Data.Integer as 𝕀 using () renaming (ℤ to 𝕀)
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product as × using (_×_; _,_)
open import Data.Sign using (Sign)
open import Data.Unit using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; lookup; map; take; drop)
open import Data.Vec.Relation.Binary.Pointwise.Extensional using (Pointwise; decidable)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function
open import Helium.Data.Pseudocode.Core
open import Level hiding (suc)
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable.Core using (map′)

private
  variable
    a : Level
    A : Set a
    t t′ t₁ t₂ : Type
    m n        : ℕ
    Γ Δ Σ ts   : Vec Type m

  ℓ = b₁ ⊔ i₁ ⊔ r₁
  ℓ₁ = ℓ ⊔ b₂ ⊔ i₂ ⊔ r₂
  ℓ₂ = i₁ ⊔ i₃ ⊔ r₁ ⊔ r₃

  Sign⇒- : Sign → Op₁ A → Op₁ A
  Sign⇒- Sign.+ f = id
  Sign⇒- Sign.- f = f

open ℕₚ.≤-Reasoning

𝕀⇒ℤ : 𝕀 → ℤ
𝕀⇒ℤ z = Sign⇒- (𝕀.sign z) ℤ.-_ (𝕀.∣ z ∣ ℤ′.×′ 1ℤ)

𝕀⇒ℝ : 𝕀 → ℝ
𝕀⇒ℝ z = Sign⇒- (𝕀.sign z) ℝ.-_ (𝕀.∣ z ∣ ℝ′.×′ 1ℝ)

castVec : .(eq : m ≡ n) → Vec A m → Vec A n
castVec {m = .0}     {0}     eq []       = []
castVec {m = .suc m} {suc n} eq (x ∷ xs) = x ∷ castVec (ℕₚ.suc-injective eq) xs

⟦_⟧ₜ  : Type → Set ℓ
⟦_⟧ₜ′ : Vec Type n → Set ℓ

⟦ bool ⟧ₜ      = Lift ℓ Bool
⟦ int ⟧ₜ       = Lift ℓ ℤ
⟦ fin n ⟧ₜ     = Lift ℓ (Fin n)
⟦ real ⟧ₜ      = Lift ℓ ℝ
⟦ bit ⟧ₜ       = Lift ℓ Bit
⟦ tuple ts ⟧ₜ  = ⟦ ts ⟧ₜ′
⟦ array t n ⟧ₜ = Vec ⟦ t ⟧ₜ n

⟦ [] ⟧ₜ′          = Lift ℓ ⊤
⟦ t ∷ [] ⟧ₜ′      = ⟦ t ⟧ₜ
⟦ t ∷ t₁ ∷ ts ⟧ₜ′ = ⟦ t ⟧ₜ × ⟦ t₁ ∷ ts ⟧ₜ′

fetch : ∀ (i : Fin n) Γ → ⟦ Γ ⟧ₜ′ → ⟦ lookup Γ i ⟧ₜ
fetch 0F      (t ∷ [])     x        = x
fetch 0F      (t ∷ t₁ ∷ Γ) (x , xs) = x
fetch (suc i) (t ∷ t₁ ∷ Γ) (x , xs) = fetch i (t₁ ∷ Γ) xs

updateAt : ∀ (i : Fin n) Γ → ⟦ lookup Γ i ⟧ₜ → ⟦ Γ ⟧ₜ′ → ⟦ Γ ⟧ₜ′
updateAt 0F      (t ∷ [])     v x        = v
updateAt 0F      (t ∷ t₁ ∷ Γ) v (x , xs) = v , xs
updateAt (suc i) (t ∷ t₁ ∷ Γ) v (x , xs) = x , updateAt i (t₁ ∷ Γ) v xs

cons′ : ∀ (ts : Vec Type n) → ⟦ t ⟧ₜ → ⟦ tuple ts ⟧ₜ → ⟦ tuple (t ∷ ts) ⟧ₜ
cons′ []      x xs = x
cons′ (_ ∷ _) x xs = x , xs

head′ : ∀ (ts : Vec Type n) → ⟦ tuple (t ∷ ts) ⟧ₜ → ⟦ t ⟧ₜ
head′ []      x        = x
head′ (_ ∷ _) (x , xs) = x

tail′ : ∀ (ts : Vec Type n) → ⟦ tuple (t ∷ ts) ⟧ₜ → ⟦ tuple ts ⟧ₜ
tail′ []      x        = _
tail′ (_ ∷ _) (x , xs) = xs

_≈_ : ⦃ HasEquality t ⦄ → Rel ⟦ t ⟧ₜ  ℓ₁
_≈_ ⦃ bool ⦄  = Lift ℓ₁ ∘₂ _≡_ on lower
_≈_ ⦃ int ⦄   = Lift ℓ₁ ∘₂ ℤ._≈_ on lower
_≈_ ⦃ fin ⦄   = Lift ℓ₁ ∘₂ _≡_ on lower
_≈_ ⦃ real ⦄  = Lift ℓ₁ ∘₂ ℝ._≈_ on lower
_≈_ ⦃ bit ⦄   = Lift ℓ₁ ∘₂ 𝔹._≈_ on lower
_≈_ ⦃ array ⦄ = Pointwise _≈_

_<_ : ⦃ Ordered t ⦄ → Rel ⟦ t ⟧ₜ ℓ₂
_<_ ⦃ int ⦄  = Lift ℓ₂ ∘₂ ℤ._<_ on lower
_<_ ⦃ fin ⦄  = Lift ℓ₂ ∘₂ Fin._<_ on lower
_<_ ⦃ real ⦄ = Lift ℓ₂ ∘₂ ℝ._<_ on lower

≈-dec : ⦃ hasEq : HasEquality t ⦄ → Decidable (_≈_ ⦃ hasEq ⦄)
≈-dec ⦃ bool ⦄  = map′ lift lower ∘₂ On.decidable lower _≡_ Bool._≟_
≈-dec ⦃ int ⦄   = map′ lift lower ∘₂ On.decidable lower ℤ._≈_ _≟ᶻ_
≈-dec ⦃ fin ⦄   = map′ lift lower ∘₂ On.decidable lower _≡_ Fin._≟_
≈-dec ⦃ real ⦄  = map′ lift lower ∘₂ On.decidable lower ℝ._≈_ _≟ʳ_
≈-dec ⦃ bit ⦄   = map′ lift lower ∘₂ On.decidable lower 𝔹._≈_ _≟ᵇ₁_
≈-dec ⦃ array ⦄ = decidable ≈-dec

<-dec : ⦃ ordered : Ordered t ⦄ → Decidable (_<_ ⦃ ordered ⦄)
<-dec ⦃ int ⦄  = map′ lift lower ∘₂ On.decidable lower ℤ._<_ _<ᶻ?_
<-dec ⦃ fin ⦄  = map′ lift lower ∘₂ On.decidable lower Fin._<_ Fin._<?_
<-dec ⦃ real ⦄ = map′ lift lower ∘₂ On.decidable lower ℝ._<_ _<ʳ?_

Κ[_]_ : ∀ t → literalType t → ⟦ t ⟧ₜ
Κ[ bool ]                x        = lift x
Κ[ int ]                 x        = lift (𝕀⇒ℤ x)
Κ[ fin n ]               x        = lift x
Κ[ real ]                x        = lift (𝕀⇒ℝ x)
Κ[ bit ]                 x        = lift (Bool.if x then 1𝔹 else 0𝔹)
Κ[ tuple [] ]            x        = _
Κ[ tuple (t ∷ []) ]      x        = Κ[ t ] x
Κ[ tuple (t ∷ t₁ ∷ ts) ] (x , xs) = Κ[ t ] x , Κ[ tuple (t₁ ∷ ts) ] xs
Κ[ array t n ]           x        = map Κ[ t ]_ x

2≉0 : Set _
2≉0 = ¬ 2 ℝ′.×′ 1ℝ ℝ.≈ 0ℝ

neg : ⦃ IsNumeric t ⦄ → Op₁ ⟦ t ⟧ₜ
neg ⦃ int ⦄  = lift ∘ ℤ.-_ ∘ lower
neg ⦃ real ⦄ = lift ∘ ℝ.-_ ∘ lower

add : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → ⟦ t₁ ⟧ₜ → ⟦ t₂ ⟧ₜ → ⟦ isNum₁ +ᵗ isNum₂ ⟧ₜ
add ⦃ int ⦄  ⦃ int ⦄  x y = lift (lower x ℤ.+ lower y)
add ⦃ int ⦄  ⦃ real ⦄ x y = lift (lower x /1 ℝ.+ lower y)
add ⦃ real ⦄ ⦃ int ⦄  x y = lift (lower x ℝ.+ lower y /1)
add ⦃ real ⦄ ⦃ real ⦄ x y = lift (lower x ℝ.+ lower y)

mul : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → ⟦ t₁ ⟧ₜ → ⟦ t₂ ⟧ₜ → ⟦ isNum₁ +ᵗ isNum₂ ⟧ₜ
mul ⦃ int ⦄  ⦃ int ⦄  x y = lift (lower x ℤ.* lower y)
mul ⦃ int ⦄  ⦃ real ⦄ x y = lift (lower x /1 ℝ.* lower y)
mul ⦃ real ⦄ ⦃ int ⦄  x y = lift (lower x ℝ.* lower y /1)
mul ⦃ real ⦄ ⦃ real ⦄ x y = lift (lower x ℝ.* lower y)

pow : ⦃ IsNumeric t ⦄ → ⟦ t ⟧ₜ → ℕ → ⟦ t ⟧ₜ
pow ⦃ int ⦄  = lift ∘₂ ℤ′._^′_ ∘ lower
pow ⦃ real ⦄ = lift ∘₂ ℝ′._^′_ ∘ lower

shift : 2≉0 → ℤ → ℕ → ℤ
shift 2≉0 z n = ⌊ z /1 ℝ.* 2≉0 ℝ.⁻¹ ℝ′.^′ n ⌋

lowerFin : ∀ (ms : Vec ℕ n) → ⟦ tuple (map fin ms) ⟧ₜ → literalTypes (map fin ms)
lowerFin []            _        = _
lowerFin (_ ∷ [])      x        = lower x
lowerFin (_ ∷ m₁ ∷ ms) (x , xs) = lower x , lowerFin (m₁ ∷ ms) xs

mergeVec : Vec A m → Vec A n → Fin (suc n) → Vec A (n ℕ.+ m)
mergeVec {m = m} {n} xs ys i = castVec eq (low ++ xs ++ high)
  where
  i′ = Fin.toℕ i
  ys′ = castVec (sym (ℕₚ.m+[n∸m]≡n (ℕ.≤-pred (Finₚ.toℕ<n i)))) ys
  low = take i′ ys′
  high = drop i′ ys′
  eq = begin-equality
    i′ ℕ.+ (m ℕ.+ (n ℕ.∸ i′)) ≡⟨ ℕₚ.+-comm i′ _ ⟩
    m ℕ.+ (n ℕ.∸ i′) ℕ.+ i′   ≡⟨ ℕₚ.+-assoc m _ _ ⟩
    m ℕ.+ (n ℕ.∸ i′ ℕ.+ i′)   ≡⟨ cong (m ℕ.+_) (ℕₚ.m∸n+n≡m (ℕ.≤-pred (Finₚ.toℕ<n i))) ⟩
    m ℕ.+ n                   ≡⟨ ℕₚ.+-comm m n ⟩
    n ℕ.+ m                   ∎

sliceVec : Vec A (n ℕ.+ m) → Fin (suc n) → Vec A m
sliceVec {n = n} {m} xs i = take m (drop i′ (castVec eq xs))
  where
  i′ = Fin.toℕ i
  eq = sym $ begin-equality
    i′ ℕ.+ (m ℕ.+ (n ℕ.∸ i′)) ≡⟨ ℕₚ.+-comm i′ _ ⟩
    m ℕ.+ (n ℕ.∸ i′) ℕ.+ i′   ≡⟨ ℕₚ.+-assoc m _ _ ⟩
    m ℕ.+ (n ℕ.∸ i′ ℕ.+ i′)   ≡⟨ cong (m ℕ.+_) (ℕₚ.m∸n+n≡m (ℕ.≤-pred (Finₚ.toℕ<n i))) ⟩
    m ℕ.+ n                   ≡⟨ ℕₚ.+-comm m n ⟩
    n ℕ.+ m                   ∎

cutVec : Vec A (n ℕ.+ m) → Fin (suc n) → Vec A n
cutVec {n = n} {m} xs i = castVec (ℕₚ.m+[n∸m]≡n (ℕ.≤-pred (Finₚ.toℕ<n i))) (take i′ (castVec eq xs) ++ drop m (drop i′ (castVec eq xs)))
  where
  i′ = Fin.toℕ i
  eq = sym $ begin-equality
    i′ ℕ.+ (m ℕ.+ (n ℕ.∸ i′)) ≡⟨ ℕₚ.+-comm i′ _ ⟩
    m ℕ.+ (n ℕ.∸ i′) ℕ.+ i′   ≡⟨ ℕₚ.+-assoc m _ _ ⟩
    m ℕ.+ (n ℕ.∸ i′ ℕ.+ i′)   ≡⟨ cong (m ℕ.+_) (ℕₚ.m∸n+n≡m (ℕ.≤-pred (Finₚ.toℕ<n i))) ⟩
    m ℕ.+ n                   ≡⟨ ℕₚ.+-comm m n ⟩
    n ℕ.+ m                   ∎
