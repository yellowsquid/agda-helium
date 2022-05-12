--------------------------------------------------------------------------------
-- Agda Helium
--
-- Properties of the Term type.
--------------------------------------------------------------------------------
{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Semantics.Axiomatic.Term.Properties
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

import Data.Bool as Bool
import Data.Integer as 𝕀
open import Data.Fin as Fin using (suc; punchIn)
open import Data.Fin.Patterns using (0F)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; insert; map; zipWith)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function
open import Function.Nary.NonDependent using (congₙ)
open import Helium.Data.Pseudocode.Algebra.Properties pseudocode
open import Helium.Data.Pseudocode.Core
open import Level using (_⊔_; lift; lower)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (does; yes; no)

open import Helium.Semantics.Axiomatic pseudocode
import Helium.Semantics.Core.Properties pseudocode
  as Coreₚ
open import Helium.Semantics.Denotational.Core rawPseudocode
  renaming (module Semantics to Semantics′)

private
  variable
    o k m n : ℕ
    Σ Γ Δ Σ′ Γ′ Δ′ ts : Vec Type n
    t t′ : Type

  module Semantics = Semantics′ proof-2≉0

private
  ℓ = i₁ ⊔ r₁

record RecBuilder⇒ (f : Term.RecBuilder Σ Γ Δ Σ′ Γ′ Δ′) : Set ℓ where
  private
    module f = Term.RecBuilder f
  field
    onState⇒  : ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ Σ′ ⟧ₜₛ
    onVar⇒    : ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ
    onMeta⇒   : ⟦ Σ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ
    onState-iso : ∀ i σ γ δ → Term.⟦ f.onState i ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Core.fetch i Σ σ
    onVar-iso   : ∀ i σ γ δ → Term.⟦ f.onVar i ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Core.fetch i Γ γ
    onMeta-iso  : ∀ i σ γ δ → Term.⟦ f.onMeta i ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Core.fetch i Δ δ

  extend : ∀ {t} (e : Term Σ Γ Δ t) σ γ δ → Term.⟦ f.extend e ⟧ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Term.⟦ e ⟧ σ γ δ
  extends : ∀ {ts : Vec Type n} (es : All (Term Σ Γ Δ) ts) σ γ δ → Term.⟦ f.extends es ⟧ₛ (onState⇒ σ γ δ) (onVar⇒ σ γ δ) (onMeta⇒ σ γ δ) ≡ Term.⟦ es ⟧ₛ σ γ δ

  extend (lit x) σ γ δ = refl
  extend (state i) σ γ δ = onState-iso i σ γ δ
  extend (var i) σ γ δ = onVar-iso i σ γ δ
  extend (meta i) σ γ δ = onMeta-iso i σ γ δ
  extend (e ≟ e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.≈-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e <? e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.<-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (inv e) σ γ δ = cong (lift ∘ Bool.not ∘ lower) (extend e σ γ δ)
  extend (e && e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∧_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e || e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∨_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (not e) σ γ δ = cong (map (lift ∘ Bool.not ∘ lower)) (extend e σ γ δ)
  extend (e and e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∧_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e or e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∨_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend [ e ] σ γ δ = cong (_∷ []) (extend e σ γ δ)
  extend (unbox e) σ γ δ = cong Vec.head (extend e σ γ δ)
  extend (merge e e₁ e₂) σ γ δ = congₙ 3 Core.mergeVec (extend e σ γ δ) (extend e₁ σ γ δ) (cong lower (extend e₂ σ γ δ))
  extend (slice e e₁) σ γ δ = cong₂ Core.sliceVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cut e e₁) σ γ δ = cong₂ Core.cutVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cast eq e) σ γ δ = cong (Core.castVec eq) (extend e σ γ δ)
  extend (- e) σ γ δ = cong Core.neg (extend e σ γ δ)
  extend (e + e₁) σ γ δ = cong₂ Core.add (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e * e₁) σ γ δ = cong₂ Core.mul (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e ^ x) σ γ δ = cong (flip Core.pow x) (extend e σ γ δ)
  extend (e >> n) σ γ δ = cong (lift ∘ flip Core.shift n ∘ lower) (extend e σ γ δ)
  extend (rnd e) σ γ δ = cong (lift ∘ ⌊_⌋ ∘ lower) (extend e σ γ δ)
  extend (fin {ms = ms} f e) σ γ δ = cong (lift ∘ f ∘ Core.lowerFin ms) (extend e σ γ δ)
  extend (asInt e) σ γ δ = cong (lift ∘ Core.𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower) (extend e σ γ δ)
  extend nil σ γ δ = refl
  extend (cons {ts = ts} e e₁) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (head {ts = ts} e) σ γ δ = cong (Core.head′ ts) (extend e σ γ δ)
  extend (tail {ts = ts} e) σ γ δ = cong (Core.tail′ ts) (extend e σ γ δ)
  extend (call f es es₁) σ γ δ = cong₂ (Semantics.fun f ∘₂ _,_) (extends es σ γ δ) (extends es₁ σ γ δ)
  extend (if e then e₁ else e₂) σ γ δ = congₙ 3 Bool.if_then_else_ (cong lower (extend e σ γ δ)) (extend e₁ σ γ δ) (extend e₂ σ γ δ)

  extends               []       σ γ δ = refl
  extends {ts = _ ∷ ts} (e ∷ es) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extends es σ γ δ)

record RecBuilder⇐ (f : Term.RecBuilder Σ Γ Δ Σ′ Γ′ Δ′) : Set ℓ where
  private
    module f = Term.RecBuilder f
  field
    onState⇐  : ⟦ Σ′ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ
    onVar⇐    : ⟦ Σ′ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ
    onMeta⇐   : ⟦ Σ′ ⟧ₜₛ → ⟦ Γ′ ⟧ₜₛ → ⟦ Δ′ ⟧ₜₛ → ⟦ Δ ⟧ₜₛ
    onState-iso : ∀ i σ γ δ → Term.⟦ f.onState i ⟧ σ γ δ ≡ Core.fetch i Σ (onState⇐ σ γ δ)
    onVar-iso   : ∀ i σ γ δ → Term.⟦ f.onVar i ⟧ σ γ δ ≡ Core.fetch i Γ (onVar⇐ σ γ δ)
    onMeta-iso  : ∀ i σ γ δ → Term.⟦ f.onMeta i ⟧ σ γ δ ≡ Core.fetch i Δ (onMeta⇐ σ γ δ)

  extend : ∀ {t} (e : Term Σ Γ Δ t) σ γ δ → Term.⟦ f.extend e ⟧ σ γ δ ≡ Term.⟦ e ⟧ (onState⇐ σ γ δ) (onVar⇐ σ γ δ) (onMeta⇐ σ γ δ)
  extends : ∀ {ts : Vec Type n} (es : All (Term Σ Γ Δ) ts) σ γ δ → Term.⟦ f.extends es ⟧ₛ σ γ δ ≡ Term.⟦ es ⟧ₛ (onState⇐ σ γ δ) (onVar⇐ σ γ δ) (onMeta⇐ σ γ δ)

  extend (lit x) σ γ δ = refl
  extend (state i) σ γ δ = onState-iso i σ γ δ
  extend (var i) σ γ δ = onVar-iso i σ γ δ
  extend (meta i) σ γ δ = onMeta-iso i σ γ δ
  extend (e ≟ e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.≈-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e <? e₁) σ γ δ = cong₂ (lift ∘₂ does ∘₂ Core.<-dec) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (inv e) σ γ δ = cong (lift ∘ Bool.not ∘ lower) (extend e σ γ δ)
  extend (e && e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∧_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e || e₁) σ γ δ = cong₂ (lift ∘₂ Bool._∨_ on lower) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (not e) σ γ δ = cong (map (lift ∘ Bool.not ∘ lower)) (extend e σ γ δ)
  extend (e and e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∧_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e or e₁) σ γ δ = cong₂ (zipWith (lift ∘₂ Bool._∨_ on lower)) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend [ e ] σ γ δ = cong (_∷ []) (extend e σ γ δ)
  extend (unbox e) σ γ δ = cong Vec.head (extend e σ γ δ)
  extend (merge e e₁ e₂) σ γ δ = congₙ 3 Core.mergeVec (extend e σ γ δ) (extend e₁ σ γ δ) (cong lower (extend e₂ σ γ δ))
  extend (slice e e₁) σ γ δ = cong₂ Core.sliceVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cut e e₁) σ γ δ = cong₂ Core.cutVec (extend e σ γ δ) (cong lower (extend e₁ σ γ δ))
  extend (cast eq e) σ γ δ = cong (Core.castVec eq) (extend e σ γ δ)
  extend (- e) σ γ δ = cong Core.neg (extend e σ γ δ)
  extend (e + e₁) σ γ δ = cong₂ Core.add (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e * e₁) σ γ δ = cong₂ Core.mul (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (e ^ x) σ γ δ = cong (flip Core.pow x) (extend e σ γ δ)
  extend (e >> n) σ γ δ = cong (lift ∘ flip Core.shift n ∘ lower) (extend e σ γ δ)
  extend (rnd e) σ γ δ = cong (lift ∘ ⌊_⌋ ∘ lower) (extend e σ γ δ)
  extend (fin {ms = ms} f e) σ γ δ = cong (lift ∘ f ∘ Core.lowerFin ms) (extend e σ γ δ)
  extend (asInt e) σ γ δ = cong (lift ∘ Core.𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower) (extend e σ γ δ)
  extend nil σ γ δ = refl
  extend (cons {ts = ts} e e₁) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extend e₁ σ γ δ)
  extend (head {ts = ts} e) σ γ δ = cong (Core.head′ ts) (extend e σ γ δ)
  extend (tail {ts = ts} e) σ γ δ = cong (Core.tail′ ts) (extend e σ γ δ)
  extend (call f es es₁) σ γ δ = cong₂ (Semantics.fun f ∘₂ _,_) (extends es σ γ δ) (extends es₁ σ γ δ)
  extend (if e then e₁ else e₂) σ γ δ = congₙ 3 Bool.if_then_else_ (cong lower (extend e σ γ δ)) (extend e₁ σ γ δ) (extend e₂ σ γ δ)

  extends               []       σ γ δ = refl
  extends {ts = _ ∷ ts} (e ∷ es) σ γ δ = cong₂ (Core.cons′ ts) (extend e σ γ δ) (extends es σ γ δ)


module Cast where
  type : (eq : t ≡ t′) → ∀ (e : Term Σ Γ Δ t) σ γ δ → Term.⟦ Term.Cast.type eq e ⟧ σ γ δ ≡ subst ⟦_⟧ₜ eq (Term.⟦ e ⟧ σ γ δ)
  type refl e σ γ δ = refl

module State where
  substBuilder : ∀ i (e : Term Σ Γ Δ (lookup Σ i)) → RecBuilder⇐ (Term.State.substBuilder i e)
  substBuilder {Σ = Σ} i e = record
    { onState⇐ = λ σ γ δ → Core.updateAt i Σ (Term.⟦ e ⟧ σ γ δ) σ
    ; onVar⇐   = λ σ γ δ → γ
    ; onMeta⇐  = λ σ γ δ → δ
    ; onState-iso = onState-iso
    ; onVar-iso   = λ _ _ _ _ → refl
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where
    open ≡-Reasoning

    onState-iso : ∀ j σ γ δ → Term.⟦ Term.RecBuilder.onState (Term.State.substBuilder i e) j ⟧ σ γ δ ≡ _
    onState-iso j σ γ δ with i Fin.≟ j
    ...                 | yes refl = sym (Coreₚ.fetch-updateAt-≡ j Σ (Term.⟦ e ⟧ σ γ δ) σ)
    ...                 | no i≢j   = sym (Coreₚ.fetch-updateAt-≢ i≢j Σ (Term.⟦ e ⟧ σ γ δ) σ)

module Var where
  weakenBuilder : ∀ i → ⟦ t ⟧ₜ → RecBuilder⇒ (Term.Var.weakenBuilder {Σ = Σ} {Γ = Γ} {Δ = Δ} {t = t} i)
  weakenBuilder {t = t} {Γ = Γ} i v = record
    { onState⇒ = λ σ γ δ → σ
    ; onVar⇒   = λ σ γ δ → Core.insert′ i Γ γ v
    ; onMeta⇒  = λ σ γ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = onVar⇒
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where

    onVar⇒ : ∀ j σ γ δ → _
    onVar⇒ j σ γ δ = begin
      Term.⟦ Term.Cast.type eq (var (punchIn i j)) ⟧ σ γ′ δ
        ≡⟨ Cast.type eq (var (punchIn i j)) σ γ′ δ ⟩
      subst ⟦_⟧ₜ eq (Core.fetch (punchIn i j) (insert Γ i t) γ′)
        ≡⟨ Coreₚ.fetch-punchIn Γ i t j γ v ⟩
      Core.fetch j Γ γ
        ∎
      where
      open ≡-Reasoning
      γ′ = Core.insert′ i Γ γ v
      eq = Vecₚ.insert-punchIn Γ i t j

  weakenAllBuilder : ⟦ Γ ⟧ₜₛ → RecBuilder⇒ (Term.Var.weakenAllBuilder {Σ = Σ} {Δ = Δ} {Γ = Γ})
  weakenAllBuilder γ = record
    { onState⇒ = λ σ _ δ → σ
    ; onVar⇒   = λ σ _ δ → γ
    ; onMeta⇒  = λ σ _ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = λ ()
    ; onMeta-iso  = λ _ _ _ _ → refl
    }

  elimAllBuilder : (es : All (Term Σ ts Δ) Γ) → RecBuilder⇐ (Term.Var.elimAllBuilder es)
  elimAllBuilder es = record
    { onState⇐ = λ σ γ δ → σ
    ; onVar⇐   = Term.⟦ es ⟧ₛ
    ; onMeta⇐  = λ σ γ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = onVar-iso es
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where
      onVar-iso : ∀ (es : All (Term _ _ _) ts) i σ γ δ → Term.⟦ All.lookup i es ⟧ σ γ δ ≡ Core.fetch i ts (Term.⟦ es ⟧ₛ σ γ δ)
      onVar-iso {ts = _ ∷ ts} (e ∷ es) 0F      σ γ δ = sym (Coreₚ.head′-cons′ ts (Term.⟦ e ⟧ σ γ δ) (Term.⟦ es ⟧ₛ σ γ δ))
      onVar-iso {ts = _ ∷ ts} (e ∷ es) (suc i) σ γ δ = begin
        Term.⟦ All.lookup i es ⟧ σ γ δ
          ≡⟨ onVar-iso es i σ γ δ ⟩
        Core.fetch i ts (Term.⟦ es ⟧ₛ σ γ δ)
          ≡˘⟨ cong (Core.fetch i ts) (Coreₚ.tail′-cons′ ts _ _) ⟩
        Core.fetch (suc i) (_ ∷ ts) (Term.⟦ e ∷ es ⟧ₛ σ γ δ)
          ∎
        where open ≡-Reasoning

  substBuilder : ∀ i (e : Term Σ Γ Δ (lookup Γ i)) → RecBuilder⇐ (Term.Var.substBuilder i e)
  substBuilder {Γ = Γ} i e = record
    { onState⇐ = λ σ γ δ → σ
    ; onVar⇐   = λ σ γ δ → Core.updateAt i Γ (Term.⟦ e ⟧ σ γ δ) γ
    ; onMeta⇐  = λ σ γ δ → δ
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = onVar-iso
    ; onMeta-iso  = λ _ _ _ _ → refl
    }
    where
    open ≡-Reasoning

    onVar-iso : ∀ j σ γ δ → Term.⟦ Term.RecBuilder.onVar (Term.Var.substBuilder i e) j ⟧ σ γ δ ≡ _
    onVar-iso j σ γ δ with i Fin.≟ j
    ...               | yes refl = sym (Coreₚ.fetch-updateAt-≡ j Γ (Term.⟦ e ⟧ σ γ δ) γ)
    ...               | no i≢j   = sym (Coreₚ.fetch-updateAt-≢ i≢j Γ (Term.⟦ e ⟧ σ γ δ) γ)

module Meta where
  weakenBuilder : ∀ i → ⟦ t ⟧ₜ → RecBuilder⇒ (Term.Meta.weakenBuilder {Σ = Σ} {Γ = Γ} {Δ = Δ} {t = t} i)
  weakenBuilder {t = t} {Δ = Δ} i v = record
    { onState⇒ = λ σ γ δ → σ
    ; onVar⇒   = λ σ γ δ → γ
    ; onMeta⇒  = λ σ γ δ → Core.insert′ i Δ δ v
    ; onState-iso = λ _ _ _ _ → refl
    ; onVar-iso   = λ _ _ _ _ → refl
    ; onMeta-iso  = onMeta⇒
    }
    where
    onMeta⇒ : ∀ j σ γ δ → _
    onMeta⇒ j σ γ δ = begin
      Term.⟦ Term.Cast.type eq (meta (punchIn i j)) ⟧ σ γ δ′
        ≡⟨ Cast.type eq (meta (punchIn i j)) σ γ δ′ ⟩
      subst ⟦_⟧ₜ eq (Core.fetch (punchIn i j) (insert Δ i t) δ′)
        ≡⟨ Coreₚ.fetch-punchIn Δ i t j δ v ⟩
      Core.fetch j Δ δ
        ∎
      where
      open ≡-Reasoning
      δ′ = Core.insert′ i Δ δ v
      eq = Vecₚ.insert-punchIn Δ i t j
