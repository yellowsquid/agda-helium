{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode

module Helium.Semantics.Denotational.Core
  {ℓ′}
  (State : Set ℓ′)
  where

open import Algebra.Core
open import Data.Bool as Bool using (Bool)
open import Data.Fin hiding (lift)
open import Data.Maybe using (Maybe; just; nothing; map; _>>=_)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_×_; _,_; map₂; uncurry)
open import Data.Product.Nary.NonDependent
open import Data.Unit using (⊤)
open import Level renaming (suc to ℓsuc) hiding (lift)
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

Expr : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Expr _ Γ τ = (σ : State) → (ρ : Product⊤ _ Γ) → Maybe (State × τ)

record Reference n {ls} (Γ : Sets n ls) (τ : Set ℓ) : Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′) where
  field
    get : Expr n Γ τ
    set : (σ : State) → (ρ : Product⊤ _ Γ) → τ → Maybe (State × Product⊤ _ Γ)

Statement : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Statement n Γ τ = (cont : Expr n Γ τ) → Expr n Γ τ

ForStatement : ∀ n {ls} → Sets n ls → Set ℓ → ℕ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
ForStatement n Γ τ m = (cont break : Expr n Γ τ) → Expr (suc n) (Fin m , Γ) τ

Function : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Function = Statement

Procedure : ∀ n {ls} → Sets n ls → Set (⨆ n ls ⊔ ℓ′)
Procedure n Γ = Function n Γ ⊤

-- Expressions

unknown : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ
unknown σ ρ = nothing

pure : ∀ {n ls} {Γ : Sets n ls} → τ → Expr n Γ τ
pure v σ ρ = just (σ , v)

apply : ∀ {n ls} {Γ : Sets n ls} → (τ → τ′) → Expr n Γ τ → Expr n Γ τ′
apply f e σ ρ = map (map₂ f) (e σ ρ)

_<*>_ : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ (τ → τ′) → Expr n Γ τ → Expr n Γ τ′
_<*>_ f e σ ρ = f σ ρ >>= λ (σ , f) → apply f e σ ρ

!_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → Expr n Γ τ
! r = Reference.get r

call : ∀ {m n ls₁ ls₂} {Γ : Sets m ls₁} {Δ : Sets n ls₂} → Function m Γ τ → Expr n Δ (Product m Γ) → Expr n Δ τ
call f e σ ρ = e σ ρ >>= λ (σ , v) → f unknown σ (toProduct⊤ _ v)

-- References

var : ∀ {n ls} {Γ : Sets n ls} i → Reference n Γ (Projₙ Γ i)
var i = record
  { get = λ σ ρ → just (σ , projₙ _ i (toProduct _ ρ))
  ; set = λ σ ρ v → just (σ , update i v ρ)
  }

!#_ : ∀ {n ls} {Γ : Sets n ls} m {m<n : True (suc m ℕₚ.≤? n)} → Expr n Γ (Projₙ Γ (#_ m {n} {m<n}))
(!# m) {m<n} = ! (var (#_ m {m<n = m<n}))

wknRef : ∀ {m ls} {Γ : Sets m ls} → Reference m Γ τ → Reference (suc m) (τ′ , Γ) τ
wknRef &x = record
  { get = λ σ (_ , ρ) → Reference.get &x σ ρ
  ; set = λ σ (v , ρ) x → Reference.set &x σ ρ x >>= λ (σ , ρ) → just (σ , (v , ρ))
  }

_,′_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → Reference n Γ τ′ → Reference n Γ (τ × τ′)
&x ,′ &y = record
  { get = λ σ ρ → Reference.get &x σ ρ >>= λ (σ , x) → Reference.get &y σ ρ >>= λ (σ , y) → just (σ , (x , y))
  ; set = λ σ ρ (x , y) → Reference.set &x σ ρ x >>= λ (σ , ρ) → Reference.set &y σ ρ y
  }

-- Statements

infixr 1 _∙_
infix 4 _≔_
infixl 2 if_then_else_

skip : ∀ {n ls} {Γ : Sets n ls} → Statement n Γ τ
skip cont = cont

ignore : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ → Statement n Γ τ′
ignore e cont σ ρ = e σ ρ >>= λ (σ , _) → cont σ ρ

return : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ → Statement n Γ τ
return e _ = e

_≔_ : ∀ {n ls} {Γ : Sets n ls} → Reference n Γ τ → Expr n Γ τ → Statement n Γ τ′
(ref ≔ e) cont σ ρ = e σ ρ >>= λ (σ , v) → Reference.set ref σ ρ v >>= λ (σ , v) → cont σ v

label : ∀ {n ls} {Γ : Sets n ls} → smap _ (Reference n Γ) n Γ ⇉ Statement n Γ τ → Statement n Γ τ
label {n = n} s = uncurry⊤ₙ n s vars
  where
  vars : ∀ {n ls} {Γ : Sets n ls} → Product⊤ n (smap _ (Reference n Γ) n Γ)
  vars {zero}  = _
  vars {suc n} = var (# 0) , mapAll _ _ wknRef vars

declare : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ → Statement (suc n) (τ , Γ) τ′ → Statement n Γ τ′
declare e s cont σ ρ = e σ ρ >>= λ (σ , v) → s (λ σ (_ , ρ) → cont σ ρ) σ (v , ρ)

if_then_else_ : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ Bool → Statement n Γ τ → Statement n Γ τ → Statement n Γ τ
(if e then b₁ else b₂) cont σ ρ = e σ ρ >>= λ (σ , b) → Bool.if b then b₁ cont σ ρ else b₂ cont σ ρ

for : ∀ {n ls} {Γ : Sets n ls} m → ForStatement n Γ τ m → Statement n Γ τ
for zero    s cont σ ρ = cont σ ρ
for (suc m) s cont σ ρ = s (for m (λ cont break σ (i , ρ) → s cont break σ (suc i , ρ)) cont) cont σ (# 0 , ρ)

_∙_ : ∀ {n ls} {Γ : Sets n ls} → Op₂ (Statement n Γ τ)
(s ∙ t) cont = s (t cont)

-- For statements

infixr 9 _∙′_

lift : ∀ {m n ls} {Γ : Sets n ls} → Statement (suc n) (Fin m , Γ) τ → ForStatement n Γ τ m
lift s cont _ = s (λ σ (_ , ρ) → cont σ ρ)

continue : ∀ {m n ls} {Γ : Sets n ls} → ForStatement n Γ τ m
continue cont break σ (_ , ρ) = cont σ ρ

break : ∀ {m n ls} {Γ : Sets n ls} → ForStatement n Γ τ m
break cont break σ (_ , ρ) = break σ ρ

_∙′_ : ∀ {m n ls} {Γ : Sets n ls} → Op₂ (ForStatement n Γ τ m)
(s ∙′ t) cont break σ (i , ρ) = s (λ σ ρ → t cont break σ (i , ρ)) break σ (i , ρ)
