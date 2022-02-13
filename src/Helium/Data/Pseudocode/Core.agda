------------------------------------------------------------------------
-- Agda Helium
--
-- Definition of the Armv8-M pseudocode.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode.Core where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; #_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (∃; _,_; proj₂; uncurry)
open import Data.Vec using (Vec; []; _∷_; lookup; map)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_; reduce; all?)
open import Function as F using (_∘_; _∘′_; _∋_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (True; map′)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary using (Decidable)

--- The set of types and boolean properties of them
data Type : Set where
  unit  : Type
  bool  : Type
  int   : Type
  fin   : (n : ℕ) → Type
  real  : Type
  bits  : (n : ℕ) → Type
  tuple : ∀ n → Vec Type n → Type
  array : Type → (n : ℕ) → Type

bit : Type
bit = bits 1

data HasEquality : Type → Set where
  bool : HasEquality bool
  int  : HasEquality int
  fin  : ∀ {n} → HasEquality (fin n)
  real : HasEquality real
  bits : ∀ {n} → HasEquality (bits n)

hasEquality? : Decidable HasEquality
hasEquality? unit        = no (λ ())
hasEquality? bool        = yes bool
hasEquality? int         = yes int
hasEquality? (fin n)     = yes fin
hasEquality? real        = yes real
hasEquality? (bits n)    = yes bits
hasEquality? (tuple n x) = no (λ ())
hasEquality? (array t n) = no (λ ())

data IsNumeric : Type → Set where
  int  : IsNumeric int
  real : IsNumeric real

isNumeric? : Decidable IsNumeric
isNumeric? unit        = no (λ ())
isNumeric? bool        = no (λ ())
isNumeric? int         = yes int
isNumeric? real        = yes real
isNumeric? (fin n)     = no (λ ())
isNumeric? (bits n)    = no (λ ())
isNumeric? (tuple n x) = no (λ ())
isNumeric? (array t n) = no (λ ())

combineNumeric : ∀ t₁ t₂ → {isNumeric₁ : True (isNumeric? t₁)} → {isNumeric₂ : True (isNumeric? t₂)} → Type
combineNumeric int  int  = int
combineNumeric int  real = real
combineNumeric real _    = real

data Sliced : Set where
  bits  : Sliced
  array : Type → Sliced

asType : Sliced → ℕ → Type
asType bits      n = bits n
asType (array t) n = array t n

elemType : Sliced → Type
elemType bits      = bit
elemType (array t) = t

--- Literals

data Literal : Type → Set where
  _′b : Bool → Literal bool
  _′i : ℕ → Literal int
  _′f : ∀ {n} → Fin n → Literal (fin n)
  _′r : ℕ → Literal real
  _′x : ∀ {n} → Vec Bool n → Literal (bits n)
  _′a : ∀ {n t} → Literal t → Literal (array t n)

--- Expressions, references, statements, functions and procedures

module Code {o} (Σ : Vec Type o) where
  data Expression {n} (Γ : Vec Type n) : Type → Set
  data CanAssign {n} {Γ} : ∀ {t} → Expression {n} Γ t → Set
  canAssign? : ∀ {n Γ t} → Decidable (CanAssign {n} {Γ} {t})
  canAssignAll? : ∀ {n Γ m ts} → Decidable {A = All (Expression {n} Γ) {m} ts} (All (CanAssign ∘ proj₂) ∘ (reduce (λ {x} e → x , e)))
  data Statement {n} (Γ : Vec Type n) (ret : Type) : Set
  data Function {n} (Γ : Vec Type n) (ret : Type) : Set
  data Procedure {n} (Γ : Vec Type n) : Set

  infix  8 -_
  infixr 7 _^_
  infixl 6 _*_ _and_ _>>_
  -- infixl 6 _/_
  infixl 5 _+_ _or_ _&&_ _||_ _∶_
  infix  4 _≟_ _<?_

  data Expression {n} Γ where
    lit   : ∀ {t} → Literal t → Expression Γ t
    state : ∀ i {i<o : True (i ℕ.<? o)} → Expression Γ (lookup Σ (#_ i {m<n = i<o}))
    var   : ∀ i {i<n : True (i ℕ.<? n)} → Expression Γ (lookup Γ (#_ i {m<n = i<n}))
    abort : ∀ {t} → Expression Γ (fin 0) → Expression Γ t
    _≟_   : ∀ {t} {hasEquality : True (hasEquality? t)} → Expression Γ t → Expression Γ t → Expression Γ bool
    _<?_  : ∀ {t} {isNumeric : True (isNumeric? t)} → Expression Γ t → Expression Γ t → Expression Γ bool
    inv   : Expression Γ bool → Expression Γ bool
    _&&_  : Expression Γ bool → Expression Γ bool → Expression Γ bool
    _||_  : Expression Γ bool → Expression Γ bool → Expression Γ bool
    not   : ∀ {n} → Expression Γ (bits n) → Expression Γ (bits n)
    _and_ : ∀ {n} → Expression Γ (bits n) → Expression Γ (bits n) → Expression Γ (bits n)
    _or_  : ∀ {n} → Expression Γ (bits n) → Expression Γ (bits n) → Expression Γ (bits n)
    [_]   : ∀ {t} → Expression Γ t → Expression Γ (array t 1)
    unbox : ∀ {t} → Expression Γ (array t 1) → Expression Γ t
    _∶_   : ∀ {m n t} → Expression Γ (asType t m) → Expression Γ (asType t n) → Expression Γ (asType t (n ℕ.+ m))
    slice : ∀ {i j t} → Expression Γ (asType t (i ℕ.+ j)) → Expression Γ (fin (suc i)) → Expression Γ (asType t j)
    cast  : ∀ {i j t} → .(eq : i ≡ j) → Expression Γ (asType t i) → Expression Γ (asType t j)
    -_    : ∀ {t} {isNumeric : True (isNumeric? t)} → Expression Γ t → Expression Γ t
    _+_   : ∀ {t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ {isNumeric₁} {isNumeric₂})
    _*_   : ∀ {t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ {isNumeric₁} {isNumeric₂})
    -- _/_   : Expression Γ real → Expression Γ real → Expression Γ real
    _^_   : ∀ {t} {isNumeric : True (isNumeric? t)} → Expression Γ t → ℕ → Expression Γ t
    _>>_  : Expression Γ int → ℕ → Expression Γ int
    rnd   : Expression Γ real → Expression Γ int
    -- get   : ℕ → Expression Γ int → Expression Γ bit
    fin   : ∀ {k ms n} → (All (Fin) ms → Fin n) → Expression Γ (tuple k (map fin ms)) → Expression Γ (fin n)
    asInt : ∀ {n} → Expression Γ (fin n) → Expression Γ int
    tup   : ∀ {m ts} → All (Expression Γ) ts → Expression Γ (tuple m ts)
    call  : ∀ {t m Δ} → Function Δ t → Expression Γ (tuple m Δ) → Expression Γ t
    if_then_else_ : ∀ {t} → Expression Γ bool → Expression Γ t → Expression Γ t → Expression Γ t

  data CanAssign {n} {Γ} where
    state : ∀ i {i<o : True (i ℕ.<? o)} → CanAssign (state i {i<o})
    var   : ∀ i {i<n : True (i ℕ.<? n)} → CanAssign (var i {i<n})
    abort : ∀ {t} {e : Expression Γ (fin 0)} → CanAssign (abort {t = t} e)
    _∶_   : ∀ {m n t} {e₁ : Expression Γ (asType t m)} {e₂ : Expression Γ (asType t n)} → CanAssign e₁ → CanAssign e₂ → CanAssign (e₁ ∶ e₂)
    [_]   : ∀ {t} {e : Expression Γ t} → CanAssign e → CanAssign [ e ]
    unbox : ∀ {t} {e : Expression Γ (array t 1)} → CanAssign e → CanAssign (unbox e)
    slice : ∀ {i j t} {e₁ : Expression Γ (asType t (i ℕ.+ j))} → CanAssign e₁ → (e₂ : Expression Γ (fin (suc i))) → CanAssign (slice e₁ e₂)
    cast  : ∀ {i j t} {e : Expression Γ (asType t i)} .(eq : i ≡ j) → CanAssign e → CanAssign (cast eq e)
    tup   : ∀ {m ts} {es : All (Expression Γ) {m} ts} → All (CanAssign ∘ proj₂) (reduce (λ {x} e → x , e) es) → CanAssign (tup es)

  canAssign? (lit x)      = no λ ()
  canAssign? (state i)    = yes (state i)
  canAssign? (var i)      = yes (var i)
  canAssign? (abort e)    = yes abort
  canAssign? (e ≟ e₁)     = no λ ()
  canAssign? (e <? e₁)    = no λ ()
  canAssign? (inv e)      = no λ ()
  canAssign? (e && e₁)    = no λ ()
  canAssign? (e || e₁)    = no λ ()
  canAssign? (not e)      = no λ ()
  canAssign? (e and e₁)   = no λ ()
  canAssign? (e or e₁)    = no λ ()
  canAssign? [ e ]        = map′ [_] (λ { [ e ] → e }) (canAssign? e)
  canAssign? (unbox e)    = map′ unbox (λ { (unbox e) → e }) (canAssign? e)
  canAssign? (e ∶ e₁)     = map′ (uncurry _∶_) (λ { (e ∶ e₁) → e , e₁ }) (canAssign? e ×-dec canAssign? e₁)
  canAssign? (slice e e₁) = map′ (λ e → slice e e₁) (λ { (slice e e₁) → e }) (canAssign? e)
  canAssign? (cast eq e)  = map′ (cast eq) (λ { (cast eq e) → e }) (canAssign? e)
  canAssign? (- e)        = no λ ()
  canAssign? (e + e₁)     = no λ ()
  canAssign? (e * e₁)     = no λ ()
  -- canAssign? (e / e₁)     = no λ ()
  canAssign? (e ^ e₁)     = no λ ()
  canAssign? (e >> e₁)    = no λ ()
  canAssign? (rnd e)      = no λ ()
  -- canAssign? (get x e)    = no λ ()
  canAssign? (fin x e)    = no λ ()
  canAssign? (asInt e)    = no λ ()
  canAssign? (tup es)     = map′ tup (λ { (tup es) → es }) (canAssignAll? es)
  canAssign? (call x e)   = no λ ()
  canAssign? (if e then e₁ else e₂) = no λ ()

  canAssignAll? []       = yes []
  canAssignAll? (e ∷ es) = map′ (uncurry _∷_) (λ { (e ∷ es) → e , es }) (canAssign? e ×-dec canAssignAll? es)

  infix  4 _≔_
  infixl 2 if_then_else_
  infixl 1 _∙_ _∙return_
  infix  1 _∙end

  data Statement Γ ret where
    _∙_           : Statement Γ ret → Statement Γ ret → Statement Γ ret
    skip          : Statement Γ ret
    _≔_           : ∀ {t} → (ref : Expression Γ t) → {canAssign : True (canAssign? ref)}→ Expression Γ t → Statement Γ ret
    declare       : ∀ {t} → Expression Γ t → Statement (t ∷ Γ) ret → Statement Γ ret
    invoke        : ∀ {m Δ} → Procedure Δ → Expression Γ (tuple m Δ) → Statement Γ ret
    if_then_else_ : Expression Γ bool → Statement Γ ret → Statement Γ ret → Statement Γ ret
    for           : ∀ m → Statement (fin m ∷ Γ) ret → Statement Γ ret

  data Function Γ ret where
    _∙return_ : Statement Γ ret → Expression Γ ret → Function Γ ret
    declare   : ∀ {t} → Expression Γ t → Function (t ∷ Γ) ret → Function Γ ret

  data Procedure Γ where
    _∙end   : Statement Γ unit → Procedure Γ
    declare : ∀ {t} → Expression Γ t → Procedure (t ∷ Γ) → Procedure Γ

  infixl  6 _<<_
  infixl 5 _-_

  slice′ : ∀ {n Γ i j t} → Expression {n} Γ (asType t (i ℕ.+ j)) → Expression Γ (fin (suc j)) → Expression Γ (asType t i)
  slice′ {i = i} e₁ e₂ = slice (cast (+-comm i _) e₁) e₂

  _-_   : ∀ {n Γ t₁ t₂} {isNumeric₁ : True (isNumeric? t₁)} {isNumeric₂ : True (isNumeric? t₂)} → Expression {n} Γ t₁ → Expression Γ t₂ → Expression Γ (combineNumeric t₁ t₂ {isNumeric₁} {isNumeric₂})
  _-_ {isNumeric₂ = isNumeric₂} x y = x + (-_ {isNumeric = isNumeric₂} y)

  _<<_ : ∀ {n Γ} → Expression {n} Γ int → ℕ → Expression Γ int
  x << n = rnd (x * lit (2 ′r) ^ n)

  get : ∀ {n Γ} → ℕ → Expression {n} Γ int → Expression Γ bit
  get i x = if x - x >> suc i << suc i <? lit (2 ′i) ^ i then lit ((false ∷ []) ′x) else lit ((true ∷ []) ′x)

  uint : ∀ {n Γ m} → Expression {n} Γ (bits m) → Expression Γ int
  uint {m = zero}  x = lit (0 ′i)
  uint {m = suc m} x =
    lit (2 ′i) * uint {m = m} (slice x (lit ((# 1) ′f))) +
    ( if slice′ x (lit ((# 0) ′f)) ≟ lit ((true ∷ []) ′x)
      then lit (1 ′i)
      else lit (0 ′i))

  sint : ∀ {n Γ m} → Expression {n} Γ (bits m) → Expression Γ int
  sint {m = zero}        x = lit (0 ′i)
  sint {m = suc zero}    x = if x ≟ lit ((true ∷ []) ′x) then - lit (1 ′i) else lit (0 ′i)
  sint {m = suc (suc m)} x =
    lit (2 ′i) * sint (slice {i = 1} x (lit ((# 1) ′f))) +
    ( if slice′ x (lit ((# 0) ′f)) ≟ lit ((true ∷ []) ′x)
      then lit (1 ′i)
      else lit (0 ′i))
