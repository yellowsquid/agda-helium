------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of terms for use in assertions
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)

module Helium.Semantics.Axiomatic.Term
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where


open RawPseudocode rawPseudocode

import Data.Bool as Bool
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin; suc; punchIn; punchOut)
open import Data.Fin.Patterns
import Data.Integer as 𝕀
import Data.Fin.Properties as Finₚ
open import Data.Nat as ℕ using (ℕ; suc)
import Data.Nat.Properties as ℕₚ
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Vec as Vec using (Vec; []; _∷_; _++_; length; lookup; insert; remove; map; zipWith)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_; tabulate)
open import Function
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Core rawPseudocode
import Helium.Semantics.Denotational.Core rawPseudocode as Den
open import Level using (_⊔_; lift; lower)
open import Relation.Binary.PropositionalEquality hiding (subst)
open import Relation.Nullary using (does; yes; no)

private
  variable
    t t′ t₁ t₂   : Type
    i j k m n o  : ℕ
    Γ Δ Σ ts ts₁ : Vec Type m

  ℓ = i₁ ⊔ r₁

data Term (Σ : Vec Type i) (Γ : Vec Type j) (Δ : Vec Type k) : Type → Set ℓ where
  lit           : ⟦ t ⟧ₜ → Term Σ Γ Δ t
  state         : ∀ i → Term Σ Γ Δ (lookup Σ i)
  var           : ∀ i → Term Σ Γ Δ (lookup Γ i)
  meta          : ∀ i → Term Σ Γ Δ (lookup Δ i)
  _≟_           : ⦃ HasEquality t ⦄ → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ bool
  _<?_          : ⦃ Ordered t ⦄ → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ bool
  inv           : Term Σ Γ Δ bool → Term Σ Γ Δ bool
  _&&_          : Term Σ Γ Δ bool → Term Σ Γ Δ bool → Term Σ Γ Δ bool
  _||_          : Term Σ Γ Δ bool → Term Σ Γ Δ bool → Term Σ Γ Δ bool
  not           : Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n)
  _and_         : Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n)
  _or_          : Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n) → Term Σ Γ Δ (bits n)
  [_]           : Term Σ Γ Δ t → Term Σ Γ Δ (array t 1)
  unbox         : Term Σ Γ Δ (array t 1) → Term Σ Γ Δ t
  merge         : Term Σ Γ Δ (array t m) → Term Σ Γ Δ (array t n) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (array t (n ℕ.+ m))
  slice         : Term Σ Γ Δ (array t (n ℕ.+ m)) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (array t m)
  cut           : Term Σ Γ Δ (array t (n ℕ.+ m)) → Term Σ Γ Δ (fin (suc n)) → Term Σ Γ Δ (array t n)
  cast          : .(eq : m ≡ n) → Term Σ Γ Δ (array t m) → Term Σ Γ Δ (array t n)
  -_            : ⦃ IsNumeric t ⦄ → Term Σ Γ Δ t → Term Σ Γ Δ t
  _+_           : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → Term Σ Γ Δ t₁ → Term Σ Γ Δ t₂ → Term Σ Γ Δ (isNum₁ +ᵗ isNum₂)
  _*_           : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → Term Σ Γ Δ t₁ → Term Σ Γ Δ t₂ → Term Σ Γ Δ (isNum₁ +ᵗ isNum₂)
  _^_           : ⦃ IsNumeric t ⦄ → Term Σ Γ Δ t → ℕ → Term Σ Γ Δ t
  _>>_          : Term Σ Γ Δ int → (n : ℕ) → Term Σ Γ Δ int
  rnd           : Term Σ Γ Δ real → Term Σ Γ Δ int
  fin           : ∀ {ms} (f : literalTypes (map fin ms) → Fin n) → Term Σ Γ Δ (tuple {n = o} (map fin ms)) → Term Σ Γ Δ (fin n)
  asInt         : Term Σ Γ Δ (fin n) → Term Σ Γ Δ int
  nil           : Term Σ Γ Δ (tuple [])
  cons          : Term Σ Γ Δ t → Term Σ Γ Δ (tuple ts) → Term Σ Γ Δ (tuple (t ∷ ts))
  head          : Term Σ Γ Δ (tuple (t ∷ ts)) → Term Σ Γ Δ t
  tail          : Term Σ Γ Δ (tuple (t ∷ ts)) → Term Σ Γ Δ (tuple ts)
  call          : Function ts ts₁ t → All (Term Σ Γ Δ) ts → All (Term Σ Γ Δ) ts₁ → Term Σ Γ Δ t
  if_then_else_ : Term Σ Γ Δ bool → Term Σ Γ Δ t → Term Σ Γ Δ t → Term Σ Γ Δ t

↓_ : Expression Σ Γ t → Term Σ Γ Δ t
↓s_ : All (Expression Σ Γ) ts → All (Term Σ Γ Δ) ts

↓ lit {t} x              = lit (Κ[ t ] x)
↓ state i                = state i
↓ var i                  = var i
↓ (e ≟ e₁)               = ↓ e ≟ ↓ e₁
↓ (e <? e₁)              = ↓ e <? ↓ e₁
↓ inv e                  = inv (↓ e)
↓ (e && e₁)              = ↓ e && ↓ e₁
↓ (e || e₁)              = ↓ e || ↓ e₁
↓ not e                  = not (↓ e)
↓ (e and e₁)             = ↓ e and ↓ e₁
↓ (e or e₁)              = ↓ e or ↓ e₁
↓ [ e ]                  = [ ↓ e ]
↓ unbox e                = unbox (↓ e)
↓ merge e e₁ e₂          = merge (↓ e) (↓ e₁) (↓ e₂)
↓ slice e e₁             = slice (↓ e) (↓ e₁)
↓ cut e e₁               = cut (↓ e) (↓ e₁)
↓ cast eq e              = cast eq (↓ e)
↓ (- e)                  = - ↓ e
↓ (e + e₁)               = ↓ e + ↓ e₁
↓ (e * e₁)               = ↓ e * ↓ e₁
↓ (e ^ x)                = ↓ e ^ x
↓ (e >> n)               = ↓ e >> n
↓ rnd e                  = rnd (↓ e)
↓ fin f e                = fin f (↓ e)
↓ asInt e                = asInt (↓ e)
↓ nil                    = nil
↓ cons e e₁              = cons (↓ e) (↓ e₁)
↓ head e                 = head (↓ e)
↓ tail e                 = tail (↓ e)
↓ call f es              = call f (tabulate state) (↓s es)
↓ (if e then e₁ else e₂) = if ↓ e then ↓ e₁ else ↓ e₂

↓s []       = []
↓s (e ∷ es) = ↓ e ∷ ↓s es

record RecBuilder (Σ′ : Vec Type i) (Γ′ : Vec Type j) (Δ′ : Vec Type k)
                  (Σ : Vec Type m)  (Γ : Vec Type n)  (Δ : Vec Type o)
                  : Set ℓ where
  field
    onState : ∀ i → Term Σ Γ Δ (lookup Σ′ i)
    onVar   : ∀ i → Term Σ Γ Δ (lookup Γ′ i)
    onMeta  : ∀ i → Term Σ Γ Δ (lookup Δ′ i)

  extend : Term Σ′ Γ′ Δ′ t → Term Σ Γ Δ t
  extends : All (Term Σ′ Γ′ Δ′) ts → All (Term Σ Γ Δ) ts

  extend (lit x)                = lit x
  extend (state i)              = onState i
  extend (var i)                = onVar i
  extend (meta i)               = onMeta i
  extend (e ≟ e₁)               = extend e ≟ extend e₁
  extend (e <? e₁)              = extend e <? extend e₁
  extend (inv e)                = inv (extend e)
  extend (e && e₁)              = extend e && extend e₁
  extend (e || e₁)              = extend e || extend e₁
  extend (not e)                = not (extend e)
  extend (e and e₁)             = extend e and extend e₁
  extend (e or e₁)              = extend e or extend e₁
  extend [ e ]                  = [ extend e ]
  extend (unbox e)              = unbox (extend e)
  extend (merge e e₁ e₂)        = merge (extend e) (extend e₁) (extend e₂)
  extend (slice e e₁)           = slice (extend e) (extend e₁)
  extend (cut e e₁)             = cut (extend e) (extend e₁)
  extend (cast eq e)            = cast eq (extend e)
  extend (- e)                  = - extend e
  extend (e + e₁)               = extend e + extend e₁
  extend (e * e₁)               = extend e * extend e₁
  extend (e ^ x)                = extend e ^ x
  extend (e >> n)               = extend e >> n
  extend (rnd e)                = rnd (extend e)
  extend (fin f e)              = fin f (extend e)
  extend (asInt e)              = asInt (extend e)
  extend nil                    = nil
  extend (cons e e₁)            = cons (extend e) (extend e₁)
  extend (head e)               = head (extend e)
  extend (tail e)               = tail (extend e)
  extend (call f es es₁)        = call f (extends es) (extends es₁)
  extend (if e then e₁ else e₂) = if extend e then extend e₁ else extend e₂

  extends []       = []
  extends (e ∷ es) = extend e ∷ extends es

module Cast where
  type : t ≡ t′ → Term Σ Γ Δ t → Term Σ Γ Δ t′
  type refl = id

module State where
  substBuilder : ∀ i → Term Σ Γ Δ (lookup Σ i) → RecBuilder Σ Γ Δ Σ Γ Δ
  substBuilder {Σ = Σ} i e = record
    { onState = onState
    ; onVar   = var
    ; onMeta  = meta
    }
    where
    onState : ∀ j → Term _ _ _ (lookup Σ j)
    onState j with i Fin.≟ j
    ...       | yes refl = e
    ...       | no i≢j   = state j

  subst : ∀ i → Term Σ Γ Δ t → Term Σ Γ Δ (lookup Σ i) → Term Σ Γ Δ t
  subst i e e′ = RecBuilder.extend (substBuilder i e′) e

module Var where
  weakenBuilder : ∀ i → RecBuilder Σ Γ Δ Σ (insert Γ i t) Δ
  weakenBuilder {Γ = Γ} i = record
    { onState = state
    ; onVar   = λ j → Cast.type (Vecₚ.insert-punchIn Γ i _ j) (var (punchIn i j))
    ; onMeta  = meta
    }

  weaken : ∀ i → Term Σ Γ Δ t → Term Σ (insert Γ i t′) Δ t
  weaken i e = RecBuilder.extend (weakenBuilder i) e

  weakenAllBuilder : RecBuilder Σ [] Δ Σ Γ Δ
  weakenAllBuilder = record
    { onState = state
    ; onVar   = λ ()
    ; onMeta  = meta
    }

  weakenAll : Term Σ [] Δ t → Term Σ Γ Δ t
  weakenAll e = RecBuilder.extend weakenAllBuilder e

  elimBuilder : ∀ i → Term Σ Γ Δ t → RecBuilder Σ (insert Γ i t) Δ Σ Γ Δ
  elimBuilder {Γ = Γ} i e = record
    { onState = state
    ; onVar   = onVar
    ; onMeta  = meta
    }
    where
    onVar : ∀ j → Term _ Γ _ (lookup (insert Γ i _) j)
    onVar j with i Fin.≟ j
    ...     | yes refl = Cast.type (sym (Vecₚ.insert-lookup Γ i _)) e
    ...     | no i≢j   = Cast.type (punchOut-insert Γ i≢j _) (var _)

  elim : ∀ i → Term Σ (insert Γ i t′) Δ t → Term Σ Γ Δ t′ → Term Σ Γ Δ t
  elim i e e′ = RecBuilder.extend (elimBuilder i e′) e

  elimAllBuilder : All (Term Σ ts Δ) Γ → RecBuilder Σ Γ Δ Σ ts Δ
  elimAllBuilder es = record
    { onState = state
    ; onVar   = flip All.lookup es
    ; onMeta  = meta
    }

  elimAll : Term Σ Γ Δ t → All (Term Σ ts Δ) Γ → Term Σ ts Δ t
  elimAll e es = RecBuilder.extend (elimAllBuilder es) e

  substBuilder : ∀ i → Term Σ Γ Δ (lookup Γ i) → RecBuilder Σ Γ Δ Σ Γ Δ
  substBuilder {Γ = Γ} i e = record
    { onState = state
    ; onVar   = onVar
    ; onMeta  = meta
    }
    where
    onVar : ∀ j → Term _ _ _ (lookup Γ j)
    onVar j with i Fin.≟ j
    ...     | yes refl = e
    ...     | no i≢j   = var j

  subst : ∀ i → Term Σ Γ Δ t → Term Σ Γ Δ (lookup Γ i) → Term Σ Γ Δ t
  subst i e e′ = RecBuilder.extend (substBuilder i e′) e

module Meta where
  weakenBuilder : ∀ i → RecBuilder Σ Γ Δ Σ Γ (insert Δ i t)
  weakenBuilder {Δ = Δ} i = record
    { onState = state
    ; onVar   = var
    ; onMeta  = λ j → Cast.type (Vecₚ.insert-punchIn Δ i _ j) (meta (punchIn i j))
    }

  weaken : ∀ i → Term Σ Γ Δ t → Term Σ Γ (insert Δ i t′) t
  weaken i e = RecBuilder.extend (weakenBuilder i) e

  weakenAllBuilder : ∀ (Δ′ : Vec Type k) (ts : Vec Type m) → RecBuilder Σ Γ (Δ′ ++ Δ) Σ Γ (Δ′ ++ ts ++ Δ)
  weakenAllBuilder {Δ = Δ} Δ′ ts = record
    { onState = state
    ; onVar   = var
    ; onMeta  = onMeta
    }
    where
    onMeta : ∀ i → Term Σ Γ (Δ′ ++ ts ++ Δ) (lookup (Δ′ ++ Δ) i)
    onMeta i with Fin.toℕ i ℕ.<? length Δ′
    ...      | yes i<|Δ′| = Cast.type
      (begin
        lookup (Δ′ ++ ts ++ Δ) _      ≡⟨  Vecₚ.lookup-++ˡ Δ′ (ts ++ Δ) (Fin.fromℕ< i<|Δ′|) ⟩
        lookup Δ′ (Fin.fromℕ< i<|Δ′|) ≡˘⟨ Vecₚ.lookup-++-< Δ′ Δ i i<|Δ′| ⟩
        lookup (Δ′ ++ Δ) i            ∎)
      (meta _)
      where open ≡-Reasoning
    ...      | no i≮|Δ′|  = Cast.type
      (begin
        lookup (Δ′ ++ ts ++ Δ) _        ≡⟨  Vecₚ.lookup-++ʳ Δ′ (ts ++ Δ) (Fin.raise _ (Fin.reduce≥ i i≥|Δ′|)) ⟩
        lookup (ts ++ Δ) _              ≡⟨  Vecₚ.lookup-++ʳ ts Δ (Fin.reduce≥ i i≥|Δ′|) ⟩
        lookup Δ (Fin.reduce≥ i i≥|Δ′|) ≡˘⟨ Vecₚ.lookup-++-≥ Δ′ Δ i i≥|Δ′| ⟩
        lookup (Δ′ ++ Δ) i              ∎)
      (meta _)
      where
      open ≡-Reasoning
      i≥|Δ′| = ℕₚ.≮⇒≥ i≮|Δ′|


  weakenAll : ∀ (Δ′ : Vec Type k) (ts : Vec Type m) → Term Σ Γ (Δ′ ++ Δ) t → Term Σ Γ (Δ′ ++ ts ++ Δ) t
  weakenAll Δ′ ts e = RecBuilder.extend (weakenAllBuilder Δ′ ts) e

  injectBuilder : ∀ (ts : Vec Type n) → RecBuilder Σ Γ Δ Σ Γ (Δ ++ ts)
  injectBuilder {Δ = Δ} ts = record
    { onState = state
    ; onVar   = var
    ; onMeta  = λ i → Cast.type (Vecₚ.lookup-++ˡ Δ ts i) (meta _)
    }

  inject : ∀ (ts : Vec Type n) → Term Σ Γ Δ t → Term Σ Γ (Δ ++ ts) t
  inject ts e = RecBuilder.extend (injectBuilder ts) e

  elimBuilder : ∀ i → Term Σ Γ Δ t → RecBuilder Σ Γ (insert Δ i t) Σ Γ Δ
  elimBuilder {Δ = Δ} i e = record
    { onState = state
    ; onVar   = var
    ; onMeta  = onMeta
    }
    where
    onMeta : ∀ j → Term _ _ Δ (lookup (insert Δ i _) j)
    onMeta j with i Fin.≟ j
    ...      | yes refl = Cast.type (sym (Vecₚ.insert-lookup Δ i _)) e
    ...      | no i≢j   = Cast.type (punchOut-insert Δ i≢j _) (meta _)

  elim : ∀ i → Term Σ Γ (insert Δ i t′) t → Term Σ Γ Δ t′ → Term Σ Γ Δ t
  elim i e e′ = RecBuilder.extend (elimBuilder i e′) e

  -- elimAllBuilder : ∀ (Δ′ : Vec Type k) → All (Term Σ Γ (Δ′ ++ Δ)) ts → RecBuilder Σ Γ (Δ′ ++ ts ++ Δ) Σ Γ (Δ′ ++ Δ)
  -- elimAllBuilder {Σ = Σ} {Γ = Γ} {Δ = Δ} {ts = ts} Δ′ es = record
  --   { onState = state
  --   ; onVar   = var
  --   ; onMeta  = onMeta
  --   }
  --   where
  --   onMeta : ∀ i → Term Σ Γ (Δ′ ++ Δ) (lookup (Δ′ ++ ts ++ Δ) i)
  --   onMeta i with Fin.splitAt (length Δ′) i in eq
  --   ... | inj₁ j =
  --     Cast.type
  --       (begin
  --         _ ≡⟨  Vecₚ.lookup-++ˡ Δ′ Δ j ⟩
  --         _ ≡˘⟨ cong [ lookup Δ′ , lookup (ts ++ Δ) ]′ eq ⟩
  --         _ ≡˘⟨ Vecₚ.lookup-splitAt (length Δ′) Δ′ (ts ++ Δ) i ⟩
  --         _ ∎)
  --       (meta _)
  --     where open ≡-Reasoning
  --   ... | inj₂ j with Fin.splitAt (length ts) j in eq₁
  --   ... | inj₁ k =
  --     Cast.type
  --       (begin
  --         _ ≡˘⟨ cong [ lookup ts , lookup Δ ]′ eq₁ ⟩
  --         _ ≡˘⟨ Vecₚ.lookup-splitAt (length ts) ts Δ j ⟩
  --         _ ≡˘⟨ cong [ lookup Δ′ , lookup (ts ++ Δ) ]′ eq ⟩
  --         _ ≡˘⟨ Vecₚ.lookup-splitAt (length Δ′) Δ′ (ts ++ Δ) i ⟩
  --         _ ∎ )
  --       (All.lookup k es)
  --     where open ≡-Reasoning
  --   ... | inj₂ k =
  --     Cast.type
  --       (begin
  --         _ ≡⟨  Vecₚ.lookup-++ʳ Δ′ Δ k ⟩
  --         _ ≡˘⟨ cong [ lookup ts , lookup Δ ]′ eq₁ ⟩
  --         _ ≡˘⟨ Vecₚ.lookup-splitAt (length ts) ts Δ j ⟩
  --         _ ≡˘⟨ cong [ lookup Δ′ , lookup (ts ++ Δ) ]′ eq ⟩
  --         _ ≡˘⟨ Vecₚ.lookup-splitAt (length Δ′) Δ′ (ts ++ Δ) i ⟩
  --         _ ∎)
  --       (meta _)
  --     where open ≡-Reasoning

subst : Term Σ Γ Δ t → Reference Σ Γ t′ → Term Σ Γ Δ t′ → Term Σ Γ Δ t
subst e (state i)          val = State.subst i e val
subst e (var i)            val = Var.subst i e val
subst e [ ref ]            val = subst e ref (unbox val)
subst e (unbox ref)        val = subst e ref [ val ]
subst e (slice ref x)      val = subst e ref (merge val (↓ ! cut ref x) (↓ x))
subst e (cut ref x)        val = subst e ref (merge (↓ ! slice ref x) val (↓ x))
subst e (cast eq ref)      val = subst e ref (cast (sym eq) val)
subst e (head ref)         val = subst e ref (cons val (↓ ! tail ref))
subst e (tail ref)         val = subst e ref (cons (↓ ! head ref) val)

module Semantics (2≉0 : 2≉0) {Σ : Vec Type i} {Γ : Vec Type j} {Δ : Vec Type k} where
  ⟦_⟧  : Term Σ Γ Δ t → ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ t ⟧ₜ
  ⟦_⟧ₛ : All (Term Σ Γ Δ) ts → ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ ts ⟧ₜₛ

  ⟦ lit x ⟧                σ γ δ = x
  ⟦ state i ⟧              σ γ δ = fetch i Σ σ
  ⟦ var i ⟧                σ γ δ = fetch i Γ γ
  ⟦ meta i ⟧               σ γ δ = fetch i Δ δ
  ⟦ e ≟ e₁ ⟧               σ γ δ = (lift ∘₂ does ∘₂ ≈-dec) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e <? e₁ ⟧              σ γ δ = (lift ∘₂ does ∘₂ <-dec) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ inv e ⟧                σ γ δ = lift ∘ Bool.not ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ e && e₁ ⟧              σ γ δ = (lift ∘₂ Bool._∧_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e || e₁ ⟧              σ γ δ = (lift ∘₂ Bool._∨_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ not e ⟧                σ γ δ = map (lift ∘ Bool.not ∘ lower) (⟦ e ⟧ σ γ δ)
  ⟦ e and e₁ ⟧             σ γ δ = zipWith (lift ∘₂ Bool._∧_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e or e₁ ⟧              σ γ δ = zipWith (lift ∘₂ Bool._∨_ on lower) (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ [ e ] ⟧                σ γ δ = ⟦ e ⟧ σ γ δ ∷ []
  ⟦ unbox e ⟧              σ γ δ = Vec.head (⟦ e ⟧ σ γ δ)
  ⟦ merge e e₁ e₂ ⟧        σ γ δ = mergeVec (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ) (lower (⟦ e₂ ⟧ σ γ δ))
  ⟦ slice e e₁ ⟧           σ γ δ = sliceVec (⟦ e ⟧ σ γ δ) (lower (⟦ e₁ ⟧ σ γ δ))
  ⟦ cut e e₁ ⟧             σ γ δ = cutVec (⟦ e ⟧ σ γ δ) (lower (⟦ e₁ ⟧ σ γ δ))
  ⟦ cast eq e ⟧            σ γ δ = castVec eq (⟦ e ⟧ σ γ δ)
  ⟦ - e ⟧                  σ γ δ = neg (⟦ e ⟧ σ γ δ)
  ⟦ e + e₁ ⟧               σ γ δ = add (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e * e₁ ⟧               σ γ δ = mul (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ e ^ x ⟧                σ γ δ = pow (⟦ e ⟧ σ γ δ) x
  ⟦ e >> n ⟧               σ γ δ = lift ∘ flip (shift 2≉0) n ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ rnd e ⟧                σ γ δ = lift ∘ ⌊_⌋ ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ fin {ms = ms} f e ⟧    σ γ δ = lift ∘ f ∘ lowerFin ms $ ⟦ e ⟧ σ γ δ
  ⟦ asInt e ⟧              σ γ δ = lift ∘ 𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower $ ⟦ e ⟧ σ γ δ
  ⟦ nil ⟧                  σ γ δ = _
  ⟦ cons {ts = ts} e e₁ ⟧  σ γ δ = cons′ ts (⟦ e ⟧ σ γ δ) (⟦ e₁ ⟧ σ γ δ)
  ⟦ head {ts = ts} e ⟧     σ γ δ = head′ ts (⟦ e ⟧ σ γ δ)
  ⟦ tail {ts = ts} e ⟧     σ γ δ = tail′ ts (⟦ e ⟧ σ γ δ)
  ⟦ call f es es₁ ⟧        σ γ δ = Den.Semantics.fun 2≉0 f (⟦ es ⟧ₛ σ γ δ , ⟦ es₁ ⟧ₛ σ γ δ)
  ⟦ if e then e₁ else e₂ ⟧ σ γ δ = Bool.if lower (⟦ e ⟧ σ γ δ) then ⟦ e₁ ⟧ σ γ δ else ⟦ e₂ ⟧ σ γ δ

  ⟦_⟧ₛ               []            σ γ δ = _
  ⟦_⟧ₛ {ts = _ ∷ ts} (e ∷ es)      σ γ δ = cons′ ts (⟦ e ⟧ σ γ δ) (⟦ es ⟧ₛ σ γ δ)
