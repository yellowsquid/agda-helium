------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode.Core where

open import Data.Bool using (Bool; true; false)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Integer as ℤ using (ℤ)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    k m n o : ℕ

--- The set of types and boolean properties of them
data Type : Set where
  bool  : Type
  int   : Type
  fin   : (n : ℕ) → Type
  real  : Type
  tuple : Vec Type n → Type
  array : Type → (n : ℕ) → Type

bit : Type
bit = bool

bits : ℕ → Type
bits = array bit

private
  variable
    t t′ t₁ t₂ : Type
    Σ Γ Δ ts : Vec Type n

data HasEquality : Type → Set where
  instance bool  : HasEquality bool
  instance int   : HasEquality int
  instance fin   : HasEquality (fin n)
  instance real  : HasEquality real
  instance array : ∀ {t n} → ⦃ HasEquality t ⦄ → HasEquality (array t n)

data Ordered : Type → Set where
  instance int  : Ordered int
  instance fin  : Ordered (fin n)
  instance real : Ordered real

data IsNumeric : Type → Set where
  instance int  : IsNumeric int
  instance real : IsNumeric real

_+ᵗ_ : IsNumeric t₁ → IsNumeric t₂ → Type
int  +ᵗ int  = int
int  +ᵗ real = real
real +ᵗ t₂   = real

literalType : Type → Set
literalTypes : Vec Type n → Set

literalType bool        = Bool
literalType int         = ℤ
literalType (fin n)     = Fin n
literalType real        = ℤ
literalType (tuple ts)  = literalTypes ts
literalType (array t n) = Vec (literalType t) n

literalTypes []            = ⊤
literalTypes (t ∷ [])      = literalType t
literalTypes (t ∷ t′ ∷ ts) = literalType t × literalTypes (t′ ∷ ts)

infix  8 -_
infixr 7 _^_
infixl 6 _*_ _and_ _>>_
infixl 5 _+_ _or_ _&&_ _||_
infix  4 _≟_ _<?_
infix  3 _≔_

infixl 2 if_then_ if_then_else_
infixl 1 _∙_ init_∙_end
infix  1 _∙end

data Expression (Σ : Vec Type o) (Γ : Vec Type n) : Type → Set
data Reference (Σ : Vec Type o) (Γ : Vec Type n) : Type → Set
data LocalReference (Σ : Vec Type o) (Γ : Vec Type n) : Type → Set
data Statement (Σ : Vec Type o) (Γ : Vec Type n) : Set
data LocalStatement (Σ : Vec Type o) (Γ : Vec Type n) : Set
data Function (Σ : Vec Type o) (Γ : Vec Type n) (ret : Type) : Set
data Procedure (Σ : Vec Type o) (Γ : Vec Type n) : Set

data Expression Σ Γ where
  lit           : literalType t → Expression Σ Γ t
  state         : ∀ i → Expression Σ Γ (lookup Σ i)
  var           : ∀ i → Expression Σ Γ (lookup Γ i)
  _≟_           : ⦃ HasEquality t ⦄ → Expression Σ Γ t → Expression Σ Γ t → Expression Σ Γ bool
  _<?_          : ⦃ Ordered t ⦄ → Expression Σ Γ t → Expression Σ Γ t → Expression Σ Γ bool
  inv           : Expression Σ Γ bool → Expression Σ Γ bool
  _&&_          : Expression Σ Γ bool → Expression Σ Γ bool → Expression Σ Γ bool
  _||_          : Expression Σ Γ bool → Expression Σ Γ bool → Expression Σ Γ bool
  not           : Expression Σ Γ (bits n) → Expression Σ Γ (bits n)
  _and_         : Expression Σ Γ (bits n) → Expression Σ Γ (bits n) → Expression Σ Γ (bits n)
  _or_          : Expression Σ Γ (bits n) → Expression Σ Γ (bits n) → Expression Σ Γ (bits n)
  [_]           : Expression Σ Γ t → Expression Σ Γ (array t 1)
  unbox         : Expression Σ Γ (array t 1) → Expression Σ Γ t
  merge         : Expression Σ Γ (array t m) → Expression Σ Γ (array t n) → Expression Σ Γ (fin (suc n)) → Expression Σ Γ (array t (n ℕ.+ m))
  slice         : Expression Σ Γ (array t (n ℕ.+ m)) → Expression Σ Γ (fin (suc n)) → Expression Σ Γ (array t m)
  cut           : Expression Σ Γ (array t (n ℕ.+ m)) → Expression Σ Γ (fin (suc n)) → Expression Σ Γ (array t n)
  cast          : .(eq : m ≡ n) → Expression Σ Γ (array t m) → Expression Σ Γ (array t n)
  -_            : ⦃ IsNumeric t ⦄ → Expression Σ Γ t → Expression Σ Γ t
  _+_           : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → Expression Σ Γ t₁ → Expression Σ Γ t₂ → Expression Σ Γ (isNum₁ +ᵗ isNum₂)
  _*_           : ⦃ isNum₁ : IsNumeric t₁ ⦄ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → Expression Σ Γ t₁ → Expression Σ Γ t₂ → Expression Σ Γ (isNum₁ +ᵗ isNum₂)
  _^_           : ⦃ IsNumeric t ⦄ → Expression Σ Γ t → ℕ → Expression Σ Γ t
  _>>_          : Expression Σ Γ int → (n : ℕ) → Expression Σ Γ int
  rnd           : Expression Σ Γ real → Expression Σ Γ int
  fin           : ∀ {ms} (f : literalTypes (map fin ms) → Fin n) → Expression Σ Γ (tuple {n = k} (map fin ms)) → Expression Σ Γ (fin n)
  asInt         : Expression Σ Γ (fin n) → Expression Σ Γ int
  nil           : Expression Σ Γ (tuple [])
  cons          : Expression Σ Γ t → Expression Σ Γ (tuple ts) → Expression Σ Γ (tuple (t ∷ ts))
  head          : Expression Σ Γ (tuple (t ∷ ts)) → Expression Σ Γ t
  tail          : Expression Σ Γ (tuple (t ∷ ts)) → Expression Σ Γ (tuple ts)
  call          : (f : Function Σ Δ t) → All (Expression Σ Γ) Δ → Expression Σ Γ t
  if_then_else_ : Expression Σ Γ bool → Expression Σ Γ t → Expression Σ Γ t → Expression Σ Γ t

data Reference Σ Γ where
  state : ∀ i → Reference Σ Γ (lookup Σ i)
  var   : ∀ i → Reference Σ Γ (lookup Γ i)
  [_]   : Reference Σ Γ t → Reference Σ Γ (array t 1)
  unbox : Reference Σ Γ (array t 1) → Reference Σ Γ t
  merge : Reference Σ Γ (array t m) → Reference Σ Γ (array t n) → Expression Σ Γ (fin (suc n)) → Reference Σ Γ (array t (n ℕ.+ m))
  slice : Reference Σ Γ (array t (n ℕ.+ m)) → Expression Σ Γ (fin (suc n)) → Reference Σ Γ (array t m)
  cut   : Reference Σ Γ (array t (n ℕ.+ m)) → Expression Σ Γ (fin (suc n)) → Reference Σ Γ (array t n)
  cast  : .(eq : m ≡ n) → Reference Σ Γ (array t m) → Reference Σ Γ (array t n)
  nil   : Reference Σ Γ (tuple [])
  cons  : Reference Σ Γ t → Reference Σ Γ (tuple ts) → Reference Σ Γ (tuple (t ∷ ts))
  head  : Reference Σ Γ (tuple (t ∷ ts)) → Reference Σ Γ t
  tail  : Reference Σ Γ (tuple (t ∷ ts)) → Reference Σ Γ (tuple ts)

data LocalReference Σ Γ where
  var   : ∀ i → LocalReference Σ Γ (lookup Γ i)
  [_]   : LocalReference Σ Γ t → LocalReference Σ Γ (array t 1)
  unbox : LocalReference Σ Γ (array t 1) → LocalReference Σ Γ t
  merge : LocalReference Σ Γ (array t m) → LocalReference Σ Γ (array t n) → Expression Σ Γ (fin (suc n)) → LocalReference Σ Γ (array t (n ℕ.+ m))
  slice : LocalReference Σ Γ (array t (n ℕ.+ m)) → Expression Σ Γ (fin (suc n)) → LocalReference Σ Γ (array t m)
  cut   : LocalReference Σ Γ (array t (n ℕ.+ m)) → Expression Σ Γ (fin (suc n)) → LocalReference Σ Γ (array t n)
  cast  : .(eq : m ≡ n) → LocalReference Σ Γ (array t m) → LocalReference Σ Γ (array t n)
  nil   : LocalReference Σ Γ (tuple [])
  cons  : LocalReference Σ Γ t → LocalReference Σ Γ (tuple ts) → LocalReference Σ Γ (tuple (t ∷ ts))
  head  : LocalReference Σ Γ (tuple (t ∷ ts)) → LocalReference Σ Γ t
  tail  : LocalReference Σ Γ (tuple (t ∷ ts)) → LocalReference Σ Γ (tuple ts)

data Statement Σ Γ where
  _∙_           : Statement Σ Γ → Statement Σ Γ → Statement Σ Γ
  skip          : Statement Σ Γ
  _≔_           : Reference Σ Γ t → Expression Σ Γ t → Statement Σ Γ
  declare       : Expression Σ Γ t → Statement Σ (t ∷ Γ) → Statement Σ Γ
  invoke        : (f : Procedure Σ Δ) → All (Expression Σ Γ) Δ → Statement Σ Γ
  if_then_      : Expression Σ Γ bool → Statement Σ Γ → Statement Σ Γ
  if_then_else_ : Expression Σ Γ bool → Statement Σ Γ → Statement Σ Γ → Statement Σ Γ
  for           : ∀ n → Statement Σ (fin n ∷ Γ) → Statement Σ Γ

data LocalStatement Σ Γ where
  _∙_           : LocalStatement Σ Γ → LocalStatement Σ Γ → LocalStatement Σ Γ
  skip          : LocalStatement Σ Γ
  _≔_           : LocalReference Σ Γ t → Expression Σ Γ t → LocalStatement Σ Γ
  declare       : Expression Σ Γ t → LocalStatement Σ (t ∷ Γ) → LocalStatement Σ Γ
  if_then_      : Expression Σ Γ bool → LocalStatement Σ Γ → LocalStatement Σ Γ
  if_then_else_ : Expression Σ Γ bool → LocalStatement Σ Γ → LocalStatement Σ Γ → LocalStatement Σ Γ
  for           : ∀ n → LocalStatement Σ (fin n ∷ Γ) → LocalStatement Σ Γ

data Function Σ Γ ret where
  init_∙_end : Expression Σ Γ ret → LocalStatement Σ (ret ∷ Γ) → Function Σ Γ ret

data Procedure Σ Γ where
  _∙end : Statement Σ Γ → Procedure Σ Γ

infixl 6 _<<_
infixl 5 _-_ _∶_

tup : All (Expression Σ Γ) ts → Expression Σ Γ (tuple ts)
tup []       = nil
tup (e ∷ es) = cons e (tup es)

_∶_ : Expression Σ Γ (array t m) → Expression Σ Γ (array t n) → Expression Σ Γ (array t (n ℕ.+ m))
e ∶ e₁ = merge e e₁ (lit (Fin.fromℕ _))

slice′ : Expression Σ Γ (array t (n ℕ.+ m)) → Expression Σ Γ (fin (suc m)) → Expression Σ Γ (array t n)
slice′ {m = m} e = slice (cast (+-comm _ m) e)

_-_ : Expression Σ Γ t₁ → ⦃ isNum₁ : IsNumeric t₁ ⦄ → Expression Σ Γ t₂ → ⦃ isNum₂ : IsNumeric t₂ ⦄ → Expression Σ Γ (isNum₁ +ᵗ isNum₂)
e - e₁ = e + (- e₁)

_<<_ : Expression Σ Γ int → (n : ℕ) → Expression Σ Γ int
e << n = e * lit (ℤ.+ (2 ℕ.^ n))

getBit : ℕ → Expression Σ Γ int → Expression Σ Γ bit
getBit i x = if x - x >> suc i << suc i <? lit (ℤ.+ (2 ℕ.^ i)) then lit false else lit true

uint : Expression Σ Γ (bits m) → Expression Σ Γ int
uint {m = 0}           x = lit ℤ.0ℤ
uint {m = 1}           x = if unbox x then lit ℤ.1ℤ else lit ℤ.0ℤ
uint {m = suc (suc m)} x =
  lit (ℤ.+ 2) * uint (slice {n = _} {n = 1} x (lit 1F)) +
  uint (cut {n = _} {n = 1} x (lit 1F))

sint : Expression Σ Γ (bits m) → Expression Σ Γ int
sint {m = 0}           x = lit ℤ.0ℤ
sint {m = 1}           x = if unbox x then lit ℤ.-1ℤ else lit ℤ.0ℤ
sint {m = suc (suc m)} x =
  lit (ℤ.+ 2) * sint {m = m} (slice x (lit 1F)) +
  uint (cut {n = _} {n = 1} x (lit 1F))

!_ : Reference Σ Γ t → Expression Σ Γ t
! state i          = state i
! var i            = var i
! [ ref ]          = [ ! ref ]
! unbox ref        = unbox (! ref)
! merge ref ref₁ e = merge (! ref) (! ref₁) e
! slice ref x      = slice (! ref) x
! cut ref x        = cut (! ref) x
! cast eq ref      = cast eq (! ref)
! nil              = nil
! cons ref ref₁    = cons (! ref) (! ref₁)
! head ref         = head (! ref)
! tail ref         = tail (! ref)

!!_ : LocalReference Σ Γ t → Expression Σ Γ t
!! var i            = var i
!! [ ref ]          = [ !! ref ]
!! unbox ref        = unbox (!! ref)
!! merge ref ref₁ x = merge (!! ref) (!! ref₁) x
!! slice ref x      = slice (!! ref) x
!! cut ref x        = cut (!! ref) x
!! cast eq ref      = cast eq (!! ref)
!! nil              = nil
!! cons ref ref₁    = cons (!! ref) (!! ref₁)
!! head ref         = head (!! ref)
!! tail ref         = tail (!! ref)
