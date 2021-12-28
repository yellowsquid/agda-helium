------------------------------------------------------------------------
-- Agda Helium
--
-- Base definitions for the denotational semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Semantics.Denotational.Core
  {ℓ′}
  (State : Set ℓ′)
  where

open import Algebra.Core
open import Data.Bool as Bool using (Bool)
open import Data.Fin hiding (lift)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product hiding (_<*>_; _,′_)
open import Data.Product.Nary.NonDependent
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤)
open import Level renaming (suc to ℓsuc) hiding (zero)
open import Function using (_∘_; _∘₂_; _|>_)
open import Function.Nary.NonDependent.Base
open import Relation.Nullary.Decidable using (True)

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    τ τ′ : Set ℓ

  mapAll : ∀ {m ls} {Γ : Sets m ls} {l l′}
           (f : ∀ {ℓ} → Set ℓ → Set (l ℓ))
           (g : ∀ {ℓ} → Set ℓ → Set (l′ ℓ))
           (h : ∀ {a} {A : Set a} → f A → g A) →
           Product⊤ m (smap l f m Γ) →
           Product⊤ m (smap l′ g m Γ)
  mapAll {zero}  f g h xs       = xs
  mapAll {suc m} f g h (x , xs) = h x , mapAll f g h xs

  update : ∀ {n ls} {Γ : Sets n ls} i → Projₙ Γ i → Product⊤ n Γ → Product⊤ n Γ
  update zero    y (_ , xs) = y , xs
  update (suc i) y (x , xs) = x , update i y xs

PureExpr : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
PureExpr n Γ τ = (σ : State) → (ρ : Product⊤ n Γ) → τ

Expr : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Expr n Γ τ = (σ : State) → (ρ : Product⊤ n Γ) → State × τ


record Reference n {ls} (Γ : Sets n ls) (τ : Set ℓ) : Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′) where
  field
    get : PureExpr n Γ τ
    set : τ → (σ : State) → (ρ : Product⊤ n Γ) → State × Product⊤ n Γ

Function : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Function = Expr

Procedure : ∀ n {ls} → Sets n ls → Set (⨆ n ls ⊔ ℓ′)
Procedure n Γ = Function n Γ ⊤

Block : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Block n Γ τ = (σ : State) → (ρ : Product⊤ n Γ) → State × (Product⊤ n Γ ⊎ τ)

-- Expressions

pure′ : ∀ {n ls} {Γ : Sets n ls} → τ → PureExpr n Γ τ
pure′ v σ ρ = v

pure : ∀ {n ls} {Γ : Sets n ls} → τ → Expr n Γ τ
pure v σ ρ = σ , v

↓_ : ∀ {n ls} {Γ : Sets n ls} → PureExpr n Γ τ → Expr n Γ τ
(↓ e) σ ρ = σ , e σ ρ

_<*>_ : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ (τ → τ′) → Expr n Γ τ → Expr n Γ τ′
_<*>_ f e σ ρ = f σ ρ |> λ (σ , f) → map₂ f (e σ ρ)

!_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → PureExpr n Γ τ
! r = Reference.get r

↓!_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → Expr n Γ τ
↓! r = ↓ ! r

call : ∀ {m n ls₁ ls₂} {Γ : Sets m ls₁} {Δ : Sets n ls₂} → Function m Γ τ → Expr n Δ (Product m Γ) → Expr n Δ τ
call f e σ ρ = e σ ρ |> map₂ (toProduct⊤ _) |> uncurry f

declare : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ → Expr (suc n) (τ , Γ) τ′ → Expr n Γ τ′
declare e s σ ρ = e σ ρ |> map₂ (_, ρ) |> uncurry s

-- References

var : ∀ {n ls} {Γ : Sets n ls} i → Reference n Γ (Projₙ Γ i)
var i = record
  { get = λ σ ρ → projₙ _ i (toProduct _ ρ)
  ; set = λ v → curry (map₂ (update i v))
  }

!#_ : ∀ {n ls} {Γ : Sets n ls} m {m<n : True (suc m ℕₚ.≤? n)} → PureExpr n Γ (Projₙ Γ (#_ m {n} {m<n}))
(!# m) {m<n} = ! var (#_ m {m<n = m<n})

_,′_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → Reference n Γ τ′ → Reference n Γ (τ × τ′)
&x ,′ &y = record
  { get = λ σ ρ → Reference.get &x σ ρ , Reference.get &y σ ρ
  ; set = λ (x , y) σ ρ → uncurry (Reference.set &y y) (Reference.set &x x σ ρ)
  }

-- Blocks

infixr 1 _∙_
infixl 2 if_then_else_
infix 4 _≔_ _⟵_

skip : ∀ {n ls} {Γ : Sets n ls} → Block n Γ τ
skip σ ρ = σ , inj₁ ρ

invoke : ∀ {m n ls₁ ls₂} {Γ : Sets m ls₁} {Δ : Sets n ls₂} → Procedure m Γ → Expr n Δ (Product m Γ) → Block n Δ τ
invoke f e σ ρ = call f e σ ρ |> map₂ (λ _ → inj₁ ρ)

_≔_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → Expr n Γ τ → Block n Γ τ′
(&x ≔ e) σ ρ = e σ ρ |> λ (σ , x) → Reference.set &x x σ ρ |> map₂ inj₁

_⟵_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → Op₁ τ → Block n Γ τ′
&x ⟵ e = &x ≔ ⦇ e (↓ (! &x)) ⦈

if_then_else_ : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ Bool → Block n Γ τ → Block n Γ τ → Block n Γ τ
(if e then b₁ else b₂) σ ρ = e σ ρ |> λ (σ , b) → Bool.if b then b₁ σ ρ else b₂ σ ρ

for : ∀ {n ls} {Γ : Sets n ls} m → Block (suc n) (Fin m , Γ) τ → Block n Γ τ
for zero    b σ ρ = σ , inj₁ ρ
for (suc m) b σ ρ with b σ (zero , ρ)
... | σ′ , inj₂ x        = σ′ , inj₂ x
... | σ′ , inj₁ (_ , ρ′) = for m b′ σ′ ρ′
  where
  b′ : Block (suc _) (Fin m , _) _
  b′ σ (i , ρ) with b σ (suc i , ρ)
  ... | σ′ , inj₂ x        = σ′ , inj₂ x
  ... | σ′ , inj₁ (_ , ρ′) = σ′ , inj₁ (i , ρ′)

_∙_ : ∀ {n ls} {Γ : Sets n ls} → Block n Γ τ → Expr n Γ τ → Expr n Γ τ
(b ∙ e) σ τ = b σ τ |> λ (σ , ρ⊎x) → [ e σ , σ ,_ ]′ ρ⊎x
