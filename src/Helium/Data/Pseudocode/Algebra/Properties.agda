------------------------------------------------------------------------
-- Agda Helium
--
-- Algebraic properties of types used by the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra

module Helium.Data.Pseudocode.Algebra.Properties
  {b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃}
  (pseudocode : Pseudocode b₁ b₂ i₁ i₂ i₃ r₁ r₂ r₃)
  where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Nat using (ℕ; suc; NonZero)
import Data.Nat.Literals as ℕₗ
open import Data.Product as × using (∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map)
import Data.Unit
open import Function using (_∘_)
import Helium.Algebra.Ordered.StrictTotal.Properties.CommutativeRing as CommRingₚ
open import Level using (_⊔_)
open import Relation.Binary.Core using (_Preserves_⟶_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Nullary.Negation using (contradiction)

private
  module pseudocode = Pseudocode pseudocode
  instance
    numberℕ : Number ℕ
    numberℕ = ℕₗ.number

open pseudocode public
  hiding
  ( integerDiscrete; 1≉0; ⌊⌋-floor
  ; module ℤ; module ℤ′; module ℤ-Reasoning
  ; module ℝ; module ℝ′; module ℝ-Reasoning
  ; module ⌊⌋
  ; module /1
  )

module ℤ where
  open pseudocode.ℤ public
    hiding (ℤ; 0ℤ; 1ℤ)
    renaming
    ( trans to <-trans
    ; irrefl to <-irrefl
    ; asym to <-asym
    ; 0<a+0<b⇒0<ab to x>0∧y>0⇒xy>0
    )
  module Reasoning = pseudocode.ℤ-Reasoning

  open CommRingₚ integerRing public

  discrete : ∀ x y → y ≤ x ⊎ x + 1ℤ ≤ y
  discrete = pseudocode.integerDiscrete

  1≉0 : 1ℤ ≉ 0ℤ
  1≉0 = pseudocode.1≉0

  x≤y<x+1⇒x≈y : ∀ {x y} → x ≤ y → y < x + 1ℤ → x ≈ y
  x≤y<x+1⇒x≈y {x} {y} x≤y y<x+1 with discrete x y
  ... | inj₁ y≤x   = ≤-antisym x≤y y≤x
  ... | inj₂ x+1≤y = contradiction x+1≤y (<⇒≱ y<x+1)

module ℝ where
  open pseudocode.ℝ public
    hiding (ℝ; 0ℝ; 1ℝ)
    renaming
    ( trans to <-trans
    ; irrefl to <-irrefl
    ; asym to <-asym
    ; 0<a+0<b⇒0<ab to x>0∧y>0⇒x*y>0
    )
  module Reasoning = pseudocode.ℝ-Reasoning

  open CommRingₚ commutativeRing public
    hiding ()

  1≉0 : 1ℝ ≉ 0ℝ
  1≉0 1≈0 = ℤ.1≉0 (begin-equality
    1ℤ        ≈˘⟨ ⌊x/1⌋≈x 1ℤ ⟩
    ⌊ 1ℤ /1 ⌋ ≈⟨  ⌊⌋.cong /1.1#-homo ⟩
    ⌊ 1ℝ ⌋    ≈⟨  ⌊⌋.cong 1≈0 ⟩
    ⌊ 0ℝ ⌋    ≈˘⟨ ⌊⌋.cong /1.0#-homo ⟩
    ⌊ 0ℤ /1 ⌋ ≈⟨  ⌊x/1⌋≈x 0ℤ ⟩
    0ℤ        ∎)
    where
    open ℤ.Reasoning
    open pseudocode using (module /1; module ⌊⌋)

  x>0⇒x⁻¹>0 : ∀ {x} → (x≉0 : x ≉ 0ℝ) → x > 0ℝ → x≉0 ⁻¹ > 0ℝ
  x>0⇒x⁻¹>0 {x} x≉0 x>0 = ≰⇒> (λ x⁻¹≤0 → <⇒≱ x>0 (begin
    x               ≈˘⟨ *-identityˡ x ⟩
    1ℝ * x          ≈˘⟨ *-congʳ (⁻¹-inverseˡ x≉0) ⟩
    x≉0 ⁻¹ * x * x  ≤⟨  x≥0⇒*-monoʳ-≤ (<⇒≤ x>0) (x≤0⇒*-anti-monoˡ-≤ x⁻¹≤0 (<⇒≤ x>0)) ⟩
    x≉0 ⁻¹ * 0ℝ * x ≈⟨  *-congʳ (zeroʳ (x≉0 ⁻¹)) ⟩
    0ℝ * x          ≈⟨  zeroˡ x ⟩
    0ℝ              ∎))
    where open Reasoning

  record IsMonotoneContinuous (f : ℝ → ℝ) : Set (r₁ ⊔ r₂ ⊔ r₃) where
    field
      cong : f Preserves _≈_ ⟶ _≈_
      mono-≤ : f Preserves _≤_ ⟶ _≤_
      continuous-≤-< : ∀ {x y z} → f x ≤ z → z < f y → ∃ λ α → f α ≈ z × x ≤ α × α < y
      continuous-<-≤ : ∀ {x y z} → f x < z → z ≤ f y → ∃ λ α → f α ≈ z × x < α × α ≤ y
      continuous-<-< : ∀ {x y z} → f x < z → z < f y → ∃ λ α → f α ≈ z × x < α × α < y

  record MCHelper (f : ℝ → ℝ) : Set (r₁ ⊔ r₂ ⊔ r₃) where
    field
      cong : f Preserves _≈_ ⟶ _≈_
      mono-≤ : f Preserves _≤_ ⟶ _≤_
      continuous-<-< : ∀ {x y z} → f x < z → z < f y → ∃ λ α → f α ≈ z × x < α × α < y

  mcHelper : ∀ {f} → MCHelper f → IsMonotoneContinuous f
  mcHelper {f} helper = record
    { cong = cong
    ; mono-≤ = mono-≤
    ; continuous-≤-< = continuous-≤-<
    ; continuous-<-≤ = continuous-<-≤
    ; continuous-<-< = continuous-<-<
    }
    where
    open MCHelper helper
    cancel-< : ∀ {x y} → f x < f y → x < y
    cancel-< fx<fy = ≰⇒> (<⇒≱ fx<fy ∘ mono-≤)

    continuous-≤-< : ∀ {x y z} → f x ≤ z → z < f y → ∃ λ α → f α ≈ z × x ≤ α × α < y
    continuous-≤-< {x} {y} {z} (inj₁ fx<z) z<fy with continuous-<-< fx<z z<fy
    ... | α , fα≈z , x<α , α<y = α , fα≈z , inj₁ x<α , α<y
    continuous-≤-< {x} {y} {z} (inj₂ fx≈z) z<fy = x , fx≈z , inj₂ Eq.refl , cancel-< (<-respˡ-≈ (Eq.sym fx≈z) z<fy)

    continuous-<-≤ : ∀ {x y z} → f x < z → z ≤ f y → ∃ λ α → f α ≈ z × x < α × α ≤ y
    continuous-<-≤ {x} {y} {z} fx<z (inj₁ z<fy) with continuous-<-< fx<z z<fy
    ... | α , fα≈z , x<α , α<y = α , fα≈z , x<α , inj₁ α<y
    continuous-<-≤ {x} {y} {z} fx<z (inj₂ z≈fy) = y , Eq.sym z≈fy , cancel-< (<-respʳ-≈ z≈fy fx<z) , inj₂ Eq.refl

  -- FIXME: bikeshed
  record IntegerPreimage (f : ℝ → ℝ) : Set (i₁ ⊔ r₁ ⊔ r₂) where
    field
      g        : ℤ → ℤ
      preimage : ∀ {x y} → f y ≈ x /1 → g x /1 ≈ y

module /1 where
  open pseudocode./1 public
    renaming
      (mono to mono-<)

  mono-≤ : ∀ {x y} → x ℤ.≤ y → x /1 ℝ.≤ y /1
  mono-≤ = map mono-< cong

  cancel-< : ∀ {x y} → x /1 ℝ.< y /1 → x ℤ.< y
  cancel-< {x} {y} x<y = ℤ.≤∧≉⇒<
    (begin
      x        ≈˘⟨ ⌊x/1⌋≈x x ⟩
      ⌊ x /1 ⌋ ≤⟨  pseudocode.⌊⌋.mono (ℝ.<⇒≤ x<y) ⟩
      ⌊ y /1 ⌋ ≈⟨  ⌊x/1⌋≈x y ⟩
      y        ∎)
    (ℝ.<⇒≉ x<y ∘ cong)
    where open ℤ.Reasoning

  cancel-≤ : ∀ {x y} → x /1 ℝ.≤ y /1 → x ℤ.≤ y
  cancel-≤ {x} {y} x≤y = begin
      x        ≈˘⟨ ⌊x/1⌋≈x x ⟩
      ⌊ x /1 ⌋ ≤⟨  pseudocode.⌊⌋.mono x≤y ⟩
      ⌊ y /1 ⌋ ≈⟨  ⌊x/1⌋≈x y ⟩
      y        ∎
    where open ℤ.Reasoning

module ⌊⌋ where
  open pseudocode.⌊⌋ public
    renaming
      (mono to mono-≤)

  cancel-< : ∀ {x y} → ⌊ x ⌋ ℤ.< ⌊ y ⌋ → x ℝ.< y
  cancel-< {x} {y} ⌊x⌋<⌊y⌋ = ℝ.≰⇒> (λ x≥y → ℤ.<⇒≱ ⌊x⌋<⌊y⌋ (mono-≤ x≥y))

  floor : ∀ {x y} → x ℝ.< y /1 → ⌊ x ⌋ ℤ.< y
  floor {x} {y} = pseudocode.⌊⌋-floor x y

  n≤x⇒n≤⌊x⌋ : ∀ {n x} → n /1 ℝ.≤ x → n ℤ.≤ ⌊ x ⌋
  n≤x⇒n≤⌊x⌋ {n} {x} n≤x = begin
    n       ≈˘⟨ ⌊x/1⌋≈x n ⟩
    ⌊ n /1 ⌋ ≤⟨  mono-≤ n≤x ⟩
    ⌊ x ⌋    ∎
    where open ℤ.Reasoning

  ⌊x⌋≤x : ∀ x → ⌊ x ⌋ /1 ℝ.≤ x
  ⌊x⌋≤x x = ℝ.≮⇒≥ (λ x<⌊x⌋ → ℤ.<-asym (floor x<⌊x⌋) (floor x<⌊x⌋))

  x<⌊x⌋+1 : ∀ x → x ℝ.< (⌊ x ⌋ ℤ.+ 1ℤ) /1
  x<⌊x⌋+1 x = ℝ.≰⇒> (λ x≥⌊x⌋+1 → ℤ.<⇒≱ (ℤ.≤∧≉⇒< ℤ.0≤1 (ℤ.1≉0 ∘ ℤ.Eq.sym)) (ℤ.+-cancelˡ-≤ ⌊ x ⌋ (begin
    ⌊ x ⌋ ℤ.+ 1ℤ ≤⟨  n≤x⇒n≤⌊x⌋ x≥⌊x⌋+1 ⟩
    ⌊ x ⌋        ≈˘⟨ ℤ.+-identityʳ ⌊ x ⌋ ⟩
    ⌊ x ⌋ ℤ.+ 0ℤ ∎)))
    where open ℤ.Reasoning

  n≤x<n+1⇒n≈⌊x⌋ : ∀ {n x} → n /1 ℝ.≤ x → x ℝ.< n /1 ℝ.+ 1ℝ → n ℤ.≈ ⌊ x ⌋
  n≤x<n+1⇒n≈⌊x⌋ {n} {x} n≤x x<n+1 = begin-equality
    n       ≈˘⟨ ⌊x/1⌋≈x n ⟩
    ⌊ n /1 ⌋ ≈⟨  ℤ.x≤y<x+1⇒x≈y (mono-≤ n≤x) (floor x<[⌊n/1⌋+1]/1) ⟩
    ⌊ x ⌋    ∎
    where
    x<[⌊n/1⌋+1]/1 = begin-strict
      x                     <⟨  x<n+1 ⟩
      n /1 ℝ.+ 1ℝ           ≈˘⟨ ℝ.+-cong (/1.cong (⌊x/1⌋≈x n)) /1.1#-homo ⟩
      ⌊ n /1 ⌋ /1 ℝ.+ 1ℤ /1 ≈˘⟨ /1.+-homo ⌊ n /1 ⌋ 1ℤ ⟩
      (⌊ n /1 ⌋ ℤ.+ 1ℤ) /1  ∎
      where open ℝ.Reasoning
    open ℤ.Reasoning

  ⌊x+n⌋≈⌊x⌋+n : ∀ x n → ⌊ x ℝ.+ n /1 ⌋ ℤ.≈ ⌊ x ⌋ ℤ.+ n
  ⌊x+n⌋≈⌊x⌋+n x n = ℤ.Eq.sym (n≤x<n+1⇒n≈⌊x⌋ ⌊x⌋+n≤x+n x+n<⌊x⌋+n+1)
    where
    open ℝ.Reasoning
    ⌊x⌋+n≤x+n = begin
      (⌊ x ⌋ ℤ.+ n) /1  ≈⟨ /1.+-homo ⌊ x ⌋ n ⟩
      ⌊ x ⌋ /1 ℝ.+ n /1 ≤⟨ ℝ.+-monoʳ-≤ (⌊x⌋≤x x) ⟩
      x ℝ.+ n /1       ∎

    x+n<⌊x⌋+n+1 = begin-strict
      x ℝ.+ n /1                 <⟨  ℝ.+-monoʳ-< (x<⌊x⌋+1 x) ⟩
      (⌊ x ⌋ ℤ.+ 1ℤ) /1 ℝ.+ n /1   ≈⟨  ℝ.+-congʳ (/1.+-homo ⌊ x ⌋ 1ℤ) ⟩
      ⌊ x ⌋ /1 ℝ.+ 1ℤ /1 ℝ.+ n /1  ≈⟨  ℝ.+-congʳ (ℝ.+-congˡ /1.1#-homo) ⟩
      ⌊ x ⌋ /1 ℝ.+ 1ℝ ℝ.+ n /1     ≈⟨  ℝ.+-assoc (⌊ x ⌋ /1) 1ℝ (n /1) ⟩
      ⌊ x ⌋ /1 ℝ.+ (1ℝ ℝ.+ n /1)   ≈⟨  ℝ.+-congˡ (ℝ.+-comm 1ℝ (n /1)) ⟩
      ⌊ x ⌋ /1 ℝ.+ (n /1 ℝ.+ 1ℝ)   ≈˘⟨ ℝ.+-assoc (⌊ x ⌋ /1) (n /1) 1ℝ ⟩
      ⌊ x ⌋ /1 ℝ.+ n /1 ℝ.+ 1ℝ     ≈˘⟨ ℝ.+-congʳ (/1.+-homo ⌊ x ⌋ n) ⟩
      (⌊ x ⌋ ℤ.+ n) /1 ℝ.+ 1ℝ      ∎

  ⌊x⌋+⌊y⌋≤⌊x+y⌋ : ∀ x y → ⌊ x ⌋ ℤ.+ ⌊ y ⌋ ℤ.≤ ⌊ x ℝ.+ y ⌋
  ⌊x⌋+⌊y⌋≤⌊x+y⌋ x y = begin
    ⌊ x ⌋ ℤ.+ ⌊ y ⌋    ≈˘⟨ ⌊x+n⌋≈⌊x⌋+n x ⌊ y ⌋ ⟩
    ⌊ x ℝ.+ ⌊ y ⌋ /1 ⌋ ≤⟨  mono-≤ (ℝ.+-monoˡ-≤ (⌊x⌋≤x y)) ⟩
    ⌊ x ℝ.+ y ⌋        ∎
    where open ℤ.Reasoning

  ⌊x+y⌋≤⌊x⌋+⌊y⌋+1 : ∀ x y → ⌊ x ℝ.+ y ⌋ ℤ.≤ ⌊ x ⌋ ℤ.+ ⌊ y ⌋ ℤ.+ 1ℤ
  ⌊x+y⌋≤⌊x⌋+⌊y⌋+1 x y = begin
    ⌊ x ℝ.+ y ⌋                 ≤⟨  mono-≤ (ℝ.+-monoˡ-≤ (ℝ.<⇒≤ (x<⌊x⌋+1 y))) ⟩
    ⌊ x ℝ.+ (⌊ y ⌋ ℤ.+ 1ℤ) /1 ⌋ ≈⟨  ⌊x+n⌋≈⌊x⌋+n x (⌊ y ⌋ ℤ.+ 1ℤ) ⟩
    ⌊ x ⌋ ℤ.+ (⌊ y ⌋ ℤ.+ 1ℤ)    ≈˘⟨ ℤ.+-assoc ⌊ x ⌋ ⌊ y ⌋ 1ℤ ⟩
    ⌊ x ⌋ ℤ.+ ⌊ y ⌋ ℤ.+ 1ℤ      ∎
    where open ℤ.Reasoning

  -- ⌊⌊x⌋+m/n⌋≈⌊x+m/n⌋ : ∀ x m {n} → (n>0 : n ℤ.> 0) →
  --   let n≉0 = ℤ.<⇒≉ n>0 ∘ ℤ.Eq.sym in
  --   ⌊ ⌊ x ⌋ /1 ℝ.* m /1 ℝ.* n≉0 ℤ.⁻¹ ⌋ ℤ.≈ ⌊ x ℝ.* m /1 ℝ.* n≉0 ℤ.⁻¹ ⌋
  -- ⌊⌊x⌋+m/n⌋≈⌊x+m/n⌋ x m {n} n>0 = ℤ.≤∧≮⇒≈ {!!} {!!}

  f-monocont+int-preimage⇒⌊f⌊x⌋⌋≈⌊fx⌋  :
    ∀ (f : ℝ → ℝ) → ℝ.IsMonotoneContinuous f → ℝ.IntegerPreimage f →
    ∀ x → ⌊ f (⌊ x ⌋ /1) ⌋ ℤ.≈ ⌊ f x ⌋
  f-monocont+int-preimage⇒⌊f⌊x⌋⌋≈⌊fx⌋ f cont int-preimage x =
    ℤ.≤∧≮⇒≈ (mono-≤ (cont.mono-≤ (⌊x⌋≤x x))) (×.uncurry ¬helper ∘ ×.proj₂ ∘ helper)
    where
    module cont = ℝ.IsMonotoneContinuous cont
    module int-preimage = ℝ.IntegerPreimage int-preimage

    helper : ⌊ f (⌊ x ⌋ /1) ⌋ ℤ.< ⌊ f x ⌋ → ∃ λ y → ⌊ x ⌋ ℤ.< y × y /1 ℝ.≤ x
    helper f⌊x⌋<fx = b , /1.cancel-< ⌊x⌋<b , b≤x
      where
      f⌊x⌋<⌊fx⌋ = cancel-< (begin-strict
        ⌊ f (⌊ x ⌋ /1) ⌋ <⟨  f⌊x⌋<fx ⟩
        ⌊ f x ⌋          ≈˘⟨ ⌊x/1⌋≈x ⌊ f x ⌋ ⟩
        ⌊ ⌊ f x ⌋ /1 ⌋   ∎)
        where open ℤ.Reasoning
      a = cont.continuous-<-≤ f⌊x⌋<⌊fx⌋ (⌊x⌋≤x (f x))
      b  = int-preimage.g ⌊ f x ⌋
      b≈a = int-preimage.preimage (×.proj₁ (×.proj₂ a))
      ⌊x⌋<b = begin-strict
        ⌊ x ⌋ /1     <⟨  ×.proj₁ (×.proj₂ (×.proj₂ a)) ⟩
        ×.proj₁ a    ≈˘⟨ b≈a ⟩
        b /1         ∎
        where open ℝ.Reasoning

      b≤x = begin
        b /1         ≈⟨ b≈a ⟩
        ×.proj₁ a    ≤⟨ ×.proj₂ (×.proj₂ (×.proj₂ a)) ⟩
        x            ∎
        where open ℝ.Reasoning

    ¬helper : ∀ {y} → ⌊ x ⌋ ℤ.< y → y /1 ℝ.≰ x
    ¬helper {y} x<y = ℤ.<⇒≱ x<y ∘ ℤ.≤-respˡ-≈ (⌊x/1⌋≈x y) ∘ mono-≤

  0#-homo : ⌊ 0ℝ ⌋ ℤ.≈ 0ℤ
  0#-homo = begin-equality
    ⌊ 0ℝ ⌋    ≈˘⟨ cong /1.0#-homo ⟩
    ⌊ 0ℤ /1 ⌋ ≈⟨  ⌊x/1⌋≈x 0ℤ ⟩
    0ℤ       ∎
    where open ℤ.Reasoning

  1#-homo : ⌊ 1ℝ ⌋ ℤ.≈ 1ℤ
  1#-homo = begin-equality
    ⌊ 1ℝ ⌋    ≈˘⟨ cong /1.1#-homo ⟩
    ⌊ 1ℤ /1 ⌋ ≈⟨  ⌊x/1⌋≈x 1ℤ ⟩
    1ℤ       ∎
    where open ℤ.Reasoning
