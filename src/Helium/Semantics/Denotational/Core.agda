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
open import Data.Product using (_×_; _,_; map₂; uncurry)
open import Data.Product.Nary.NonDependent
open import Data.Unit using (⊤)
open import Level renaming (suc to ℓsuc) hiding (lift)
open import Function.Nary.NonDependent.Base

private
  variable
    ℓ ℓ₁ ℓ₂ : Level
    τ τ′ : Set ℓ

  update : ∀ {n ls} {Γ : Sets n ls} i → Projₙ Γ i → Product⊤ n Γ → Product⊤ n Γ
  update zero    y (_ , xs) = y , xs
  update (suc i) y (x , xs) = x , update i y xs

Expr : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Expr _ Γ τ = State → Product⊤ _ Γ → Maybe (State × τ)

Statement : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Statement n Γ τ = Op₁ (Expr n Γ τ)

ForStatement : ∀ n {ls} → Sets n ls → Set ℓ → ℕ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
ForStatement n Γ τ m = (cont break : Expr n Γ τ) → Expr (suc n) (Fin m , Γ) τ

Function : ∀ n {ls} → Sets n ls → Set ℓ → Set (ℓ ⊔ ⨆ n ls ⊔ ℓ′)
Function = Statement

Procedure : ∀ n {ls} → Sets n ls → Set (⨆ n ls ⊔ ℓ′)
Procedure n Γ = Function n Γ ⊤

-- Expressions

unknown : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ
unknown σ vars = nothing

pure : ∀ {n ls} {Γ : Sets n ls} → τ → Expr n Γ τ
pure v σ vars = just (σ , v)

apply : ∀ {n ls} {Γ : Sets n ls} → (τ → τ′) → Expr n Γ τ → Expr n Γ τ′
apply f e σ vars = map (map₂ f) (e σ vars)

_<*>_ : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ (τ → τ′) → Expr n Γ τ → Expr n Γ τ′
_<*>_ f e σ vars = f σ vars >>= λ (σ , f) → apply f e σ vars

lookup : ∀ {n ls} {Γ : Sets n ls} i → Expr n Γ (Projₙ Γ i)
lookup i σ vars = just (σ , projₙ _ i (toProduct _ vars))

call : ∀ {m n ls₁ ls₂} {Γ : Sets m ls₁} {Δ : Sets n ls₂} → Function m Γ τ → Expr n Δ (Product⊤ m Γ) → Expr n Δ τ
call f e σ var = e σ var >>= λ (σ , v) → f unknown σ v

-- Statements

infixr 9 _∙_

return : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ → Statement n Γ τ
return e _ = e

assign : ∀ {n ls} {Γ : Sets n ls} i → Expr n Γ (Projₙ Γ i) → Statement n Γ τ
assign i e cont σ vars = e σ vars >>= λ (σ , v) → cont σ (update i v vars)

declare : ∀ {n ls} {Γ : Sets n ls} → Expr n Γ τ′ → Statement (suc n) (τ′ , Γ) τ → Statement n Γ τ
declare e s cont σ vars = e σ vars >>= λ (σ , v) → s (λ σ (_ , vars) → cont σ vars) σ (v , vars)

for : ∀ {n ls} {Γ : Sets n ls} m → ForStatement n Γ τ m → Statement n Γ τ
for zero    s cont σ vars = cont σ vars
for (suc m) s cont σ vars = s (for m (λ cont break σ (i , vars) → s cont break σ (suc i , vars)) cont) cont σ (# 0 , vars)

_∙_ : ∀ {n ls} {Γ : Sets n ls} → Op₂ (Statement n Γ τ)
(s ∙ t) cont = s (t cont)

-- For statements

infixr 9 _∙′_

lift : ∀ {m n ls} {Γ : Sets n ls} → Statement (suc n) (Fin m , Γ) τ → ForStatement n Γ τ m
lift s cont _ = s (λ σ (_ , vars) → cont σ vars)

continue : ∀ {m n ls} {Γ : Sets n ls} → ForStatement n Γ τ m
continue cont break σ (_ , vars) = cont σ vars

break : ∀ {m n ls} {Γ : Sets n ls} → ForStatement n Γ τ m
break cont break σ (_ , vars) = break σ vars

_∙′_ : ∀ {m n ls} {Γ : Sets n ls} → Op₂ (ForStatement n Γ τ m)
(s ∙′ t) cont break σ (i , vars) = s (λ σ vars → t cont break σ (i , vars)) break σ (i , vars)
