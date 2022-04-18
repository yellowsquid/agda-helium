------------------------------------------------------------------------
-- Agda Helium
--
-- Ways to modify pseudocode statements and expressions.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

module Helium.Data.Pseudocode.Manipulate where

open import Helium.Data.Pseudocode.Core

open import Algebra.Bundles using (IdempotentCommutativeMonoid)
import Algebra.Solver.IdempotentCommutativeMonoid as ICMSolver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
import Algebra.Solver.Ring.Simple as RingSolver
open import Data.Fin as Fin using (suc; punchOut; punchIn)
open import Data.Fin.Patterns
open import Data.Nat as ℕ using (ℕ; suc; _<_; _≤_; z≤n; s≤s; _⊔_)
import Data.Nat.Induction as ℕᵢ
import Data.Nat.Properties as ℕₚ
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; -,_; <_,_>)
open import Data.Product.Nary.NonDependent using (Product; uncurryₙ)
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_; lookup; insert; remove)
import Data.Vec.Properties as Vecₚ
open import Data.Vec.Recursive as Vecᵣ using (2+_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Function
open import Function.Nary.NonDependent using (_⇉_; Sets; congₙ; 0ℓs)
open import Helium.Data.Pseudocode.Core
open import Induction.WellFounded as Wf using (WellFounded)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

private
  variable
    k m n o : ℕ
    ret t t′ t₁ t₂ : Type
    Σ Γ Δ ts : Vec Type n

private
  punchOut-insert : ∀ {a} {A : Set a} (xs : Vec A n) {i j} (i≢j : i ≢ j) x → lookup xs (punchOut i≢j) ≡ lookup (insert xs i x) j
  punchOut-insert xs {i} {j} i≢j x = begin
    lookup xs (punchOut i≢j)                         ≡˘⟨ cong (flip lookup (punchOut i≢j)) (Vecₚ.remove-insert xs i x) ⟩
    lookup (remove (insert xs i x) i) (punchOut i≢j) ≡⟨  Vecₚ.remove-punchOut (insert xs i x) i≢j ⟩
    lookup (insert xs i x) j                         ∎
    where open ≡-Reasoning

  lookupᵣ-map : ∀ {a b} {A : Set a} {B : Set b} {f : A → B} i (xs : A Vecᵣ.^ n) → Vecᵣ.lookup i (Vecᵣ.map f n xs) ≡ f (Vecᵣ.lookup i xs)
  lookupᵣ-map {n = 1}    0F      xs = refl
  lookupᵣ-map {n = 2+ n} 0F      xs = refl
  lookupᵣ-map {n = 2+ n} (suc i) xs = lookupᵣ-map i (proj₂ xs)

  ⊔-0-boundedLattice : IdempotentCommutativeMonoid _ _
  ⊔-0-boundedLattice = record
    { isIdempotentCommutativeMonoid = record
      { isCommutativeMonoid = ℕₚ.⊔-0-isCommutativeMonoid
      ; idem                = ℕₚ.⊔-idem
      }
    }

open ICMSolver ⊔-0-boundedLattice
  using (_⊜_; _⊕_)
  renaming (solve to solve-⊔; id to ε)

open RingSolver (ACR.fromCommutativeSemiring ℕₚ.+-*-commutativeSemiring) ℕₚ._≟_
  using (_:=_; _:+_; _:*_; con)
  renaming (solve to solve-+)

open ℕₚ.≤-Reasoning

private
  [_]_$_⊗_ : ∀ {a b c} {A : Set a} {B : Set b} m → (C : A → B → Set c) → A Vecᵣ.^ m → B Vecᵣ.^ m → Set c
  [ m ] f $ xs ⊗ ys = Vecᵣ.foldr ⊤ id (const _×_) m (Vecᵣ.zipWith f m xs ys)

  ⨆[_]_ : ∀ n → ℕ Vecᵣ.^ n → ℕ
  ⨆[_]_ = Vecᵣ.foldl (const ℕ) 0 id (const (flip _⊔_))

  ⨆-step : ∀ m x xs → ⨆[ 2+ m ] (x , xs) ≡ x ⊔ ⨆[ suc m ] xs
  ⨆-step 0       x xs       = refl
  ⨆-step (suc m) x (y , xs) = begin-equality
    ⨆[ 2+ suc m ] (x , y , xs) ≡⟨  ⨆-step m (x ⊔ y) xs ⟩
    x ⊔ y ⊔ ⨆[ suc m ] xs      ≡⟨  ℕₚ.⊔-assoc x y _ ⟩
    x ⊔ (y ⊔ ⨆[ suc m ] xs)    ≡˘⟨ cong (_ ⊔_) (⨆-step m y xs) ⟩
    x ⊔ ⨆[ 2+ m ] (y , xs)     ∎

  join-lubs : ∀ n m {lhs rhs} → [ m ] (λ x y → x ≤ y ⊔ n) $ lhs ⊗ rhs → ⨆[ m ] lhs ≤ (⨆[ m ] rhs) ⊔ n
  join-lubs n 0      {lhs}     {rhs}     ≤s           = z≤n
  join-lubs n 1      {lhs}     {rhs}     ≤s           = ≤s
  join-lubs n (2+ m) {x , lhs} {y , rhs} (x≤y⊔n , ≤s) = begin
    ⨆[ 2+ m ] (x , lhs)          ≡⟨  ⨆-step m x lhs ⟩
    x ⊔ ⨆[ suc m ] lhs           ≤⟨  ℕₚ.⊔-mono-≤ x≤y⊔n (join-lubs n (suc m) ≤s) ⟩
    y ⊔ n ⊔ (⨆[ suc m ] rhs ⊔ n) ≡⟨  solve-⊔ 3 (λ a b c → (a ⊕ c) ⊕ b ⊕ c ⊜ (a ⊕ b) ⊕ c) refl y _ n ⟩
    y ⊔ ⨆[ suc m ] rhs ⊔ n       ≡˘⟨ cong (_⊔ _) (⨆-step m y rhs) ⟩
    ⨆[ 2+ m ] (y , rhs) ⊔ n      ∎ 

  lookup-⨆-≤ : ∀ i (xs : ℕ Vecᵣ.^ n) → Vecᵣ.lookup i xs ≤ ⨆[ n ] xs
  lookup-⨆-≤ {1}    0F      x        = ℕₚ.≤-refl
  lookup-⨆-≤ {2+ n} 0F      (x , xs) = begin
    x                  ≤⟨  ℕₚ.m≤m⊔n x _ ⟩
    x ⊔ ⨆[ suc n ] xs  ≡˘⟨ ⨆-step n x xs ⟩
    ⨆[ 2+ n ] (x , xs) ∎
  lookup-⨆-≤ {2+ n} (suc i) (x , xs) = begin
    Vecᵣ.lookup i xs   ≤⟨  lookup-⨆-≤ i xs ⟩
    ⨆[ suc n ] xs      ≤⟨  ℕₚ.m≤n⊔m x _ ⟩
    x ⊔ ⨆[ suc n ] xs  ≡˘⟨ ⨆-step n x xs ⟩
    ⨆[ 2+ n ] (x , xs) ∎

  Σ[_]_ : ∀ n → ℕ Vecᵣ.^ n → ℕ
  Σ[_]_ = Vecᵣ.foldl (const ℕ) 0 id (const (flip ℕ._+_))

  Σ-step : ∀ m x xs → Σ[ 2+ m ] (x , xs) ≡ x ℕ.+ Σ[ suc m ] xs
  Σ-step 0       x xs       = refl
  Σ-step (suc m) x (y , xs) = begin-equality
    Σ[ 2+ suc m ] (x , y , xs)  ≡⟨  Σ-step m (x ℕ.+ y) xs ⟩
    x ℕ.+ y ℕ.+ Σ[ suc m ] xs   ≡⟨  ℕₚ.+-assoc x y _ ⟩
    x ℕ.+ (y ℕ.+ Σ[ suc m ] xs) ≡˘⟨ cong (x ℕ.+_) (Σ-step m y xs) ⟩
    x ℕ.+ Σ[ 2+ m ] (y , xs)    ∎

  lookup-Σ-≤ : ∀ i (xs : ℕ Vecᵣ.^ n) → Vecᵣ.lookup i xs ≤ Σ[ n ] xs
  lookup-Σ-≤ {1}    0F      x        = ℕₚ.≤-refl
  lookup-Σ-≤ {2+ n} 0F      (x , xs) = begin
    x                   ≤⟨  ℕₚ.m≤m+n x _ ⟩
    x ℕ.+ Σ[ suc n ] xs ≡˘⟨ Σ-step n x xs ⟩
    Σ[ 2+ n ] (x , xs)  ∎
  lookup-Σ-≤ {2+ n} (suc i) (x , xs) = begin
    Vecᵣ.lookup i xs    ≤⟨  lookup-Σ-≤ i xs ⟩
    Σ[ suc n ] xs       ≤⟨  ℕₚ.m≤n+m _ x ⟩
    x ℕ.+ Σ[ suc n ] xs ≡˘⟨ Σ-step n x xs ⟩
    Σ[ 2+ n ] (x , xs)  ∎


  foldr-lubs : ∀ {a b c} {A : Set a} {B : ℕ → Set b}
               (f : ∀ {n} → A → B n → B (suc n)) y
               (P : ∀ {n} → B n → Set c) →
               P y →
               (∀ {n} a {b : B n} → P b → P (f a b)) →
               ∀ (xs : Vec A n) →
               P (Vec.foldr B f y xs)
  foldr-lubs f y P y∈P f-pres []       = y∈P
  foldr-lubs f y P y∈P f-pres (x ∷ xs) = f-pres x (foldr-lubs f y P y∈P f-pres xs)

module CallDepth where
  expr    : Expression Σ Γ t → ℕ
  exprs   : All (Expression Σ Γ) ts → ℕ
  locRef  : LocalReference Σ Γ t → ℕ
  locStmt : LocalStatement Σ Γ → ℕ
  fun     : Function Σ Γ ret → ℕ

  expr (lit x)                = 0
  expr (state i)              = 0
  expr (var i)                = 0
  expr (e ≟ e₁)               = expr e ⊔ expr e₁
  expr (e <? e₁)              = expr e ⊔ expr e₁
  expr (inv e)                = expr e
  expr (e && e₁)              = expr e ⊔ expr e₁
  expr (e || e₁)              = expr e ⊔ expr e₁
  expr (not e)                = expr e
  expr (e and e₁)             = expr e ⊔ expr e₁
  expr (e or e₁)              = expr e ⊔ expr e₁
  expr [ e ]                  = expr e
  expr (unbox e)              = expr e
  expr (merge e e₁ e₂)        = expr e ⊔ expr e₁ ⊔ expr e₂
  expr (slice e e₁)           = expr e ⊔ expr e₁
  expr (cut e e₁)             = expr e ⊔ expr e₁
  expr (cast eq e)            = expr e
  expr (- e)                  = expr e
  expr (e + e₁)               = expr e ⊔ expr e₁
  expr (e * e₁)               = expr e ⊔ expr e₁
  expr (e ^ x)                = expr e
  expr (e >> n)               = expr e
  expr (rnd e)                = expr e
  expr (fin f e)              = expr e
  expr (asInt e)              = expr e
  expr nil                    = 0
  expr (cons e e₁)            = expr e ⊔ expr e₁
  expr (head e)               = expr e
  expr (tail e)               = expr e
  expr (call f es)            = exprs es ⊔ suc (fun f)
  expr (if e then e₁ else e₂) = expr e ⊔ expr e₁ ⊔ expr e₂

  exprs []       = 0
  exprs (e ∷ es) = exprs es ⊔ expr e

  locRef (var i)            = 0
  locRef [ ref ]            = locRef ref
  locRef (unbox ref)        = locRef ref
  locRef (merge ref ref₁ x) = locRef ref ⊔ locRef ref₁ ⊔ expr x
  locRef (slice ref x)      = locRef ref ⊔ expr x
  locRef (cut ref x)        = locRef ref ⊔ expr x
  locRef (cast eq ref)      = locRef ref
  locRef nil                = 0
  locRef (cons ref ref₁)    = locRef ref ⊔ locRef ref₁
  locRef (head ref)         = locRef ref
  locRef (tail ref)         = locRef ref

  locStmt (s ∙ s₁)              = locStmt s ⊔ locStmt s₁
  locStmt skip                  = 0
  locStmt (ref ≔ e)             = locRef ref ⊔ expr e
  locStmt (declare x s)         = locStmt s ⊔ expr x
  locStmt (if x then s)         = locStmt s ⊔ expr x
  locStmt (if x then s else s₁) = locStmt s ⊔ locStmt s₁ ⊔ expr x
  locStmt (for n s)             = locStmt s

  fun (declare x f) = fun f ⊔ expr x
  fun (s ∙return e) = locStmt s ⊔ expr e

  homo-!! : ∀ (ref : LocalReference Σ Γ t) → expr (!! ref) ≡ locRef ref
  homo-!! (var i)            = refl
  homo-!! [ ref ]            = homo-!! ref
  homo-!! (unbox ref)        = homo-!! ref
  homo-!! (merge ref ref₁ x) = cong₂ (λ m n → m ⊔ n ⊔ _) (homo-!! ref) (homo-!! ref₁)
  homo-!! (slice ref x)      = cong (_⊔ _) (homo-!! ref)
  homo-!! (cut ref x)        = cong (_⊔ _) (homo-!! ref)
  homo-!! (cast eq ref)      = homo-!! ref
  homo-!! nil                = refl
  homo-!! (cons ref ref₁)    = cong₂ _⊔_ (homo-!! ref) (homo-!! ref₁)
  homo-!! (head ref)         = homo-!! ref
  homo-!! (tail ref)         = homo-!! ref

  ∷ˡ-≤ : ∀ (e : Expression Σ Γ t) (es : All (Expression Σ Γ) ts) →
             expr e ≤ exprs (e ∷ es)
  ∷ˡ-≤ e es = ℕₚ.m≤n⊔m (exprs es) (expr e)

  ∷ʳ-≤ : ∀ (e : Expression Σ Γ t) (es : All (Expression Σ Γ) ts) →
             exprs es ≤ exprs (e ∷ es)
  ∷ʳ-≤ e es = ℕₚ.m≤m⊔n (exprs es) (expr e)

  lookup-≤ : ∀ i (es : All (Expression Σ Γ) ts) → expr (All.lookup i es) ≤ exprs es
  lookup-≤ 0F      (e ∷ es) = ∷ˡ-≤ e es
  lookup-≤ (suc i) (e ∷ es) = ℕₚ.≤-trans (lookup-≤ i es) (∷ʳ-≤ e es)

  call>0 : ∀ (f : Function Σ Δ t) (es : All (Expression Σ Γ) Δ) → 0 < expr (call f es)
  call>0 f es = ℕₚ.<-transˡ ℕₚ.0<1+n (ℕₚ.m≤n⊔m (exprs es) (suc (fun f)))

module Cast where
  expr : t ≡ t′ → Expression Σ Γ t → Expression Σ Γ t′
  expr refl e = e

  locRef : t ≡ t′ → LocalReference Σ Γ t → LocalReference Σ Γ t′
  locRef refl ref = ref

  homo-!! : ∀ (eq : t ≡ t′) (ref : LocalReference Σ Γ t) → expr eq (!! ref) ≡ !! (locRef eq ref)
  homo-!! refl _ = refl

  expr-depth : ∀ (eq : t ≡ t′) (e : Expression Σ Γ t) → CallDepth.expr (expr eq e) ≡ CallDepth.expr e
  expr-depth refl _ = refl

module Elim where
  expr  : ∀ i → Expression Σ (insert Γ i t′) t → Expression Σ Γ t′ → Expression Σ Γ t
  exprs : ∀ i → All (Expression Σ (insert Γ i t′)) ts → Expression Σ Γ t′ → All (Expression Σ Γ) ts

  expr i (lit x)                e′ = lit x
  expr i (state j)              e′ = state j
  expr i (var j)                e′ with i Fin.≟ j
  ...                              | yes refl = Cast.expr (sym (Vecₚ.insert-lookup _ i _)) e′
  ...                              | no i≢j   = Cast.expr (punchOut-insert _ i≢j _) (var (punchOut i≢j))
  expr i (e ≟ e₁)               e′ = expr i e e′ ≟ expr i e₁ e′
  expr i (e <? e₁)              e′ = expr i e e′ <? expr i e₁ e′
  expr i (inv e)                e′ = expr i e e′
  expr i (e && e₁)              e′ = expr i e e′ && expr i e₁ e′
  expr i (e || e₁)              e′ = expr i e e′ || expr i e₁ e′
  expr i (not e)                e′ = not (expr i e e′)
  expr i (e and e₁)             e′ = expr i e e′ and expr i e₁ e′
  expr i (e or e₁)              e′ = expr i e e′ or expr i e₁ e′
  expr i [ e ]                  e′ = [ expr i e e′ ]
  expr i (unbox e)              e′ = unbox (expr i e e′)
  expr i (merge e e₁ e₂)        e′ = merge (expr i e e′) (expr i e₁ e′) (expr i e₂ e′)
  expr i (slice e e₁)           e′ = slice (expr i e e′) (expr i e₁ e′)
  expr i (cut e e₁)             e′ = cut (expr i e e′) (expr i e₁ e′)
  expr i (cast eq e)            e′ = cast eq (expr i e e′)
  expr i (- e)                  e′ = - expr i e e′
  expr i (e + e₁)               e′ = expr i e e′ + expr i e₁ e′
  expr i (e * e₁)               e′ = expr i e e′ * expr i e₁ e′
  expr i (e ^ x)                e′ = expr i e e′ ^ x
  expr i (e >> n)               e′ = expr i e e′ >> n
  expr i (rnd e)                e′ = rnd (expr i e e′)
  expr i (fin f e)              e′ = fin f (expr i e e′)
  expr i (asInt e)              e′ = asInt (expr i e e′)
  expr i nil                    e′ = nil
  expr i (cons e e₁)            e′ = cons (expr i e e′) (expr i e₁ e′)
  expr i (head e)               e′ = head (expr i e e′)
  expr i (tail e)               e′ = tail (expr i e e′)
  expr i (call f es)            e′ = call f (exprs i es e′)
  expr i (if e then e₁ else e₂) e′ = if expr i e e′ then expr i e₁ e′ else expr i e₂ e′

  exprs i []       e′ = []
  exprs i (e ∷ es) e′ = expr i e e′ ∷ exprs i es e′

  expr-depth  : ∀ i (e : Expression Σ _ t) (e′ : Expression Σ Γ t′) → CallDepth.expr (expr i e e′) ≤ CallDepth.expr e ⊔ CallDepth.expr e′
  exprs-depth : ∀ i (es : All (Expression Σ _) ts) (e′ : Expression Σ Γ t′) → CallDepth.exprs (exprs i es e′) ≤ CallDepth.exprs es ⊔ CallDepth.expr e′

  expr-depth i (lit x) e′                = z≤n
  expr-depth i (state j) e′              = z≤n
  expr-depth i (var j) e′                with i Fin.≟ j
  ...                                    | yes refl = ℕₚ.≤-reflexive (Cast.expr-depth (sym (Vecₚ.insert-lookup _ i _)) e′)
  ...                                    | no i≢j   = ℕₚ.≤-trans (ℕₚ.≤-reflexive (Cast.expr-depth (punchOut-insert _ i≢j _) (var (punchOut i≢j)))) z≤n
  expr-depth i (e ≟ e₁) e′               = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e <? e₁) e′              = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (inv e) e′                = expr-depth i e e′
  expr-depth i (e && e₁) e′              = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e || e₁) e′              = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (not e) e′                = expr-depth i e e′
  expr-depth i (e and e₁) e′             = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e or e₁) e′              = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i [ e ] e′                  = expr-depth i e e′
  expr-depth i (unbox e) e′              = expr-depth i e e′
  expr-depth i (merge e e₁ e₂) e′        = join-lubs (CallDepth.expr e′) 3 (expr-depth i e e′ , expr-depth i e₁ e′ , expr-depth i e₂ e′)
  expr-depth i (slice e e₁) e′           = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (cut e e₁) e′             = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (cast eq e) e′            = expr-depth i e e′
  expr-depth i (- e) e′                  = expr-depth i e e′
  expr-depth i (e + e₁) e′               = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e * e₁) e′               = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e ^ x) e′                = expr-depth i e e′
  expr-depth i (e >> n) e′               = expr-depth i e e′
  expr-depth i (rnd e) e′                = expr-depth i e e′
  expr-depth i (fin f e) e′              = expr-depth i e e′
  expr-depth i (asInt e) e′              = expr-depth i e e′
  expr-depth i nil e′                    = z≤n
  expr-depth i (cons e e₁) e′            = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (head e) e′               = expr-depth i e e′
  expr-depth i (tail e) e′               = expr-depth i e e′
  expr-depth i (call f es) e′            = join-lubs (CallDepth.expr e′) 2 (exprs-depth i es e′ , ℕₚ.m≤m⊔n _ (CallDepth.expr e′))
  expr-depth i (if e then e₁ else e₂) e′ = join-lubs (CallDepth.expr e′) 3 (expr-depth i e e′ , expr-depth i e₁ e′ , expr-depth i e₂ e′)

  exprs-depth i []       e′ = z≤n
  exprs-depth i (e ∷ es) e′ = join-lubs (CallDepth.expr e′) 2 (exprs-depth i es e′ , expr-depth i e e′)

module Weaken where
  expr  : ∀ i t′ → Expression Σ Γ t → Expression Σ (insert Γ i t′) t
  exprs : ∀ i t′ → All (Expression Σ Γ) ts → All (Expression Σ (insert Γ i t′)) ts

  expr i t′ (lit x)                = lit x
  expr i t′ (state j)              = state j
  expr i t′ (var j)                = Cast.expr (Vecₚ.insert-punchIn _ i t′ j) (var (punchIn i j))
  expr i t′ (e ≟ e₁)               = expr i t′ e ≟ expr i t′ e₁
  expr i t′ (e <? e₁)              = expr i t′ e <? expr i t′ e₁
  expr i t′ (inv e)                = inv (expr i t′ e)
  expr i t′ (e && e₁)              = expr i t′ e && expr i t′ e₁
  expr i t′ (e || e₁)              = expr i t′ e || expr i t′ e₁
  expr i t′ (not e)                = not (expr i t′ e)
  expr i t′ (e and e₁)             = expr i t′ e and expr i t′ e₁
  expr i t′ (e or e₁)              = expr i t′ e or expr i t′ e₁
  expr i t′ [ e ]                  = [ expr i t′ e ]
  expr i t′ (unbox e)              = unbox (expr i t′ e)
  expr i t′ (merge e e₁ e₂)        = merge (expr i t′ e) (expr i t′ e₁) (expr i t′ e₂)
  expr i t′ (slice e e₁)           = slice (expr i t′ e) (expr i t′ e₁)
  expr i t′ (cut e e₁)             = cut (expr i t′ e) (expr i t′ e₁)
  expr i t′ (cast eq e)            = cast eq (expr i t′ e)
  expr i t′ (- e)                  = - expr i t′ e
  expr i t′ (e + e₁)               = expr i t′ e + expr i t′ e₁
  expr i t′ (e * e₁)               = expr i t′ e * expr i t′ e₁
  expr i t′ (e ^ x)                = expr i t′ e ^ x
  expr i t′ (e >> n)               = expr i t′ e >> n
  expr i t′ (rnd e)                = rnd (expr i t′ e)
  expr i t′ (fin f e)              = fin f (expr i t′ e)
  expr i t′ (asInt e)              = asInt (expr i t′ e)
  expr i t′ nil                    = nil
  expr i t′ (cons e e₁)            = cons (expr i t′ e) (expr i t′ e₁)
  expr i t′ (head e)               = head (expr i t′ e)
  expr i t′ (tail e)               = tail (expr i t′ e)
  expr i t′ (call f es)            = call f (exprs i t′ es)
  expr i t′ (if e then e₁ else e₂) = if expr i t′ e then expr i t′ e₁ else expr i t′ e₂

  exprs i t′ []       = []
  exprs i t′ (e ∷ es) = expr i t′ e ∷ exprs i t′ es

  locRef : ∀ i t′ → LocalReference Σ Γ t → LocalReference Σ (insert Γ i t′) t
  locRef i t′ (var j)            = Cast.locRef (Vecₚ.insert-punchIn _ i t′ j) (var (punchIn i j))
  locRef i t′ [ ref ]            = [ locRef i t′ ref ]
  locRef i t′ (unbox ref)        = unbox (locRef i t′ ref)
  locRef i t′ (merge ref ref₁ e) = merge (locRef i t′ ref) (locRef i t′ ref₁) (expr i t′ e)
  locRef i t′ (slice ref e)      = slice (locRef i t′ ref) (expr i t′ e)
  locRef i t′ (cut ref e)        = cut (locRef i t′ ref) (expr i t′ e)
  locRef i t′ (cast eq ref)      = cast eq (locRef i t′ ref)
  locRef i t′ nil                = nil
  locRef i t′ (cons ref ref₁)    = cons (locRef i t′ ref) (locRef i t′ ref₁)
  locRef i t′ (head ref)         = head (locRef i t′ ref)
  locRef i t′ (tail ref)         = tail (locRef i t′ ref)

  locStmt : ∀ i t′ → LocalStatement Σ Γ → LocalStatement Σ (insert Γ i t′)
  locStmt i t′ (s ∙ s₁)              = locStmt i t′ s ∙ locStmt i t′ s₁
  locStmt i t′ skip                  = skip
  locStmt i t′ (ref ≔ val)           = locRef i t′ ref ≔ expr i t′ val
  locStmt i t′ (declare e s)         = declare (expr i t′ e) (locStmt (suc i) t′ s)
  locStmt i t′ (if x then s)         = if expr i t′ x then locStmt i t′ s
  locStmt i t′ (if x then s else s₁) = if expr i t′ x then locStmt i t′ s else locStmt i t′ s₁
  locStmt i t′ (for n s)             = for n (locStmt (suc i) t′ s)

  homo-!! : ∀ i t′ (ref : LocalReference Σ Γ t) → expr i t′ (!! ref) ≡ !! (locRef i t′ ref)
  homo-!! i t′ (var j)            = Cast.homo-!! (Vecₚ.insert-punchIn _ i t′ j) (var (punchIn i j))
  homo-!! i t′ [ ref ]            = cong [_] (homo-!! i t′ ref)
  homo-!! i t′ (unbox ref)        = cong unbox (homo-!! i t′ ref)
  homo-!! i t′ (merge ref ref₁ e) = cong₂ (λ x y → merge x y _) (homo-!! i t′ ref) (homo-!! i t′ ref₁)
  homo-!! i t′ (slice ref e)      = cong (λ x → slice x _) (homo-!! i t′ ref)
  homo-!! i t′ (cut ref e)        = cong (λ x → cut x _) (homo-!! i t′ ref)
  homo-!! i t′ (cast eq ref)      = cong (cast eq) (homo-!! i t′ ref)
  homo-!! i t′ nil                = refl
  homo-!! i t′ (cons ref ref₁)    = cong₂ cons (homo-!! i t′ ref) (homo-!! i t′ ref₁)
  homo-!! i t′ (head ref)         = cong head (homo-!! i t′ ref)
  homo-!! i t′ (tail ref)         = cong tail (homo-!! i t′ ref)

  expr-depth : ∀ i t′ (e : Expression Σ Γ t) → CallDepth.expr (expr i t′ e) ≡ CallDepth.expr e
  exprs-depth : ∀ i t′ (es : All (Expression Σ Γ) ts) → CallDepth.exprs (exprs i t′ es) ≡ CallDepth.exprs es

  expr-depth i t′ (lit x)                = refl
  expr-depth i t′ (state j)              = refl
  expr-depth i t′ (var j)                = Cast.expr-depth (Vecₚ.insert-punchIn _ i t′ j) (var (punchIn i j))
  expr-depth i t′ (e ≟ e₁)               = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (e <? e₁)              = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (inv e)                = expr-depth i t′ e
  expr-depth i t′ (e && e₁)              = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (e || e₁)              = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (not e)                = expr-depth i t′ e
  expr-depth i t′ (e and e₁)             = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (e or e₁)              = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ [ e ]                  = expr-depth i t′ e
  expr-depth i t′ (unbox e)              = expr-depth i t′ e
  expr-depth i t′ (merge e e₁ e₂)        = congₙ 3 (λ a b c → a ⊔ b ⊔ c) (expr-depth i t′ e) (expr-depth i t′ e₁) (expr-depth i t′ e₂)
  expr-depth i t′ (slice e e₁)           = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (cut e e₁)             = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (cast eq e)            = expr-depth i t′ e
  expr-depth i t′ (- e)                  = expr-depth i t′ e
  expr-depth i t′ (e + e₁)               = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (e * e₁)               = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (e ^ x)                = expr-depth i t′ e
  expr-depth i t′ (e >> n)               = expr-depth i t′ e
  expr-depth i t′ (rnd e)                = expr-depth i t′ e
  expr-depth i t′ (fin f e)              = expr-depth i t′ e
  expr-depth i t′ (asInt e)              = expr-depth i t′ e
  expr-depth i t′ nil                    = refl
  expr-depth i t′ (cons e e₁)            = cong₂ _⊔_ (expr-depth i t′ e) (expr-depth i t′ e₁)
  expr-depth i t′ (head e)               = expr-depth i t′ e
  expr-depth i t′ (tail e)               = expr-depth i t′ e
  expr-depth i t′ (call f es)            = cong (_⊔ _) (exprs-depth i t′ es)
  expr-depth i t′ (if e then e₁ else e₂) = congₙ 3 (λ a b c → a ⊔ b ⊔ c) (expr-depth i t′ e) (expr-depth i t′ e₁) (expr-depth i t′ e₂)

  exprs-depth i t′ []       = refl
  exprs-depth i t′ (e ∷ es) = cong₂ _⊔_ (exprs-depth i t′ es) (expr-depth i t′ e)

  locRef-depth : ∀ i t′ (ref : LocalReference Σ Γ t) → CallDepth.locRef (locRef i t′ ref) ≡ CallDepth.locRef ref
  locRef-depth i t′ ref = begin-equality
    CallDepth.locRef (locRef i t′ ref)    ≡˘⟨ CallDepth.homo-!! (locRef i t′ ref) ⟩
    CallDepth.expr (!! (locRef i t′ ref)) ≡˘⟨ cong CallDepth.expr (homo-!! i t′ ref) ⟩
    CallDepth.expr (expr i t′ (!! ref))   ≡⟨  expr-depth i t′ (!! ref) ⟩
    CallDepth.expr (!! ref)               ≡⟨  CallDepth.homo-!! ref ⟩
    CallDepth.locRef ref                  ∎

  locStmt-depth : ∀ i t′ (s : LocalStatement Σ Γ) → CallDepth.locStmt (locStmt i t′ s) ≡ CallDepth.locStmt s
  locStmt-depth i t′ (s ∙ s₁)              = cong₂ _⊔_ (locStmt-depth i t′ s) (locStmt-depth i t′ s₁)
  locStmt-depth i t′ skip                  = refl
  locStmt-depth i t′ (ref ≔ val)           = cong₂ _⊔_ (locRef-depth i t′ ref) (expr-depth i t′ val)
  locStmt-depth i t′ (declare e s)         = cong₂ _⊔_ (locStmt-depth (suc i) t′ s) (expr-depth i t′ e)
  locStmt-depth i t′ (if x then s)         = cong₂ _⊔_ (locStmt-depth i t′ s) (expr-depth i t′ x)
  locStmt-depth i t′ (if x then s else s₁) = congₙ 3 (λ a b c → a ⊔ b ⊔ c) (locStmt-depth i t′ s) (locStmt-depth i t′ s₁) (expr-depth i t′ x)
  locStmt-depth i t′ (for n s)             = locStmt-depth (suc i) t′ s

module Subst where
  expr : ∀ i → Expression Σ Γ t → Expression Σ Γ (lookup Γ i) → Expression Σ Γ t
  exprs : ∀ i → All (Expression Σ Γ) ts → Expression Σ Γ (lookup Γ i) → All (Expression Σ Γ) ts

  expr i (lit x)                e′ = lit x
  expr i (state j)              e′ = state j
  expr i (var j)                e′ with i Fin.≟ j
  ...                              | yes refl = e′
  ...                              | no i≢j   = var j
  expr i (e ≟ e₁)               e′ = expr i e e′ ≟ expr i e₁ e′
  expr i (e <? e₁)              e′ = expr i e e′ <? expr i e₁ e′
  expr i (inv e)                e′ = inv (expr i e e′)
  expr i (e && e₁)              e′ = expr i e e′ && expr i e₁ e′
  expr i (e || e₁)              e′ = expr i e e′ || expr i e₁ e′
  expr i (not e)                e′ = not (expr i e e′)
  expr i (e and e₁)             e′ = expr i e e′ and expr i e₁ e′
  expr i (e or e₁)              e′ = expr i e e′ or expr i e₁ e′
  expr i [ e ]                  e′ = [ expr i e e′ ]
  expr i (unbox e)              e′ = unbox (expr i e e′)
  expr i (merge e e₁ e₂)        e′ = merge (expr i e e′) (expr i e₁ e′) (expr i e₂ e′)
  expr i (slice e e₁)           e′ = slice (expr i e e′) (expr i e₁ e′)
  expr i (cut e e₁)             e′ = cut (expr i e e′) (expr i e₁ e′)
  expr i (cast eq e)            e′ = cast eq (expr i e e′)
  expr i (- e)                  e′ = - expr i e e′
  expr i (e + e₁)               e′ = expr i e e′ + expr i e₁ e′
  expr i (e * e₁)               e′ = expr i e e′ * expr i e₁ e′
  expr i (e ^ x)                e′ = expr i e e′ ^ x
  expr i (e >> n)               e′ = expr i e e′ >> n
  expr i (rnd e)                e′ = rnd (expr i e e′)
  expr i (fin f e)              e′ = fin f (expr i e e′)
  expr i (asInt e)              e′ = asInt (expr i e e′)
  expr i nil                    e′ = nil
  expr i (cons e e₁)            e′ = cons (expr i e e′) (expr i e₁ e′)
  expr i (head e)               e′ = head (expr i e e′)
  expr i (tail e)               e′ = tail (expr i e e′)
  expr i (call f es)            e′ = call f (exprs i es e′)
  expr i (if e then e₁ else e₂) e′ = if expr i e e′ then expr i e₁ e′ else expr i e₂ e′

  exprs i []       e′ = []
  exprs i (e ∷ es) e′ = expr i e e′ ∷ exprs i es e′

  expr-depth  : ∀ i (e : Expression Σ Γ t) e′ → CallDepth.expr (expr i e e′) ≤ CallDepth.expr e ⊔ CallDepth.expr e′
  exprs-depth : ∀ i (es : All (Expression Σ Γ) ts) e′ → CallDepth.exprs (exprs i es e′) ≤ CallDepth.exprs es ⊔ CallDepth.expr e′

  expr-depth i (lit x)                e′ = z≤n
  expr-depth i (state j)              e′ = z≤n
  expr-depth i (var j)                e′ with i Fin.≟ j
  ...                                    | yes refl = ℕₚ.≤-refl
  ...                                    | no i≢j   = z≤n
  expr-depth i (e ≟ e₁)               e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e <? e₁)              e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (inv e)                e′ = expr-depth i e e′
  expr-depth i (e && e₁)              e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e || e₁)              e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (not e)                e′ = expr-depth i e e′
  expr-depth i (e and e₁)             e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e or e₁)              e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i [ e ]                  e′ = expr-depth i e e′
  expr-depth i (unbox e)              e′ = expr-depth i e e′
  expr-depth i (merge e e₁ e₂)        e′ = join-lubs (CallDepth.expr e′) 3 (expr-depth i e e′ , expr-depth i e₁ e′ , expr-depth i e₂ e′)
  expr-depth i (slice e e₁)           e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (cut e e₁)             e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (cast eq e)            e′ = expr-depth i e e′
  expr-depth i (- e)                  e′ = expr-depth i e e′
  expr-depth i (e + e₁)               e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e * e₁)               e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (e ^ x)                e′ = expr-depth i e e′
  expr-depth i (e >> n)               e′ = expr-depth i e e′
  expr-depth i (rnd e)                e′ = expr-depth i e e′
  expr-depth i (fin f e)              e′ = expr-depth i e e′
  expr-depth i (asInt e)              e′ = expr-depth i e e′
  expr-depth i nil                    e′ = z≤n
  expr-depth i (cons e e₁)            e′ = join-lubs (CallDepth.expr e′) 2 (expr-depth i e e′ , expr-depth i e₁ e′)
  expr-depth i (head e)               e′ = expr-depth i e e′
  expr-depth i (tail e)               e′ = expr-depth i e e′
  expr-depth i (call f es)            e′ = join-lubs (CallDepth.expr e′) 2 (exprs-depth i es e′ , ℕₚ.m≤m⊔n _ (CallDepth.expr e′))
  expr-depth i (if e then e₁ else e₂) e′ = join-lubs (CallDepth.expr e′) 3 (expr-depth i e e′ , expr-depth i e₁ e′ , expr-depth i e₂ e′)

  exprs-depth i []       e′ = z≤n
  exprs-depth i (e ∷ es) e′ = join-lubs (CallDepth.expr e′) 2 (exprs-depth i es e′ , expr-depth i e e′)

module SubstAll where
  expr : Expression Σ Γ t → All (Expression Σ Δ) Γ → Expression Σ Δ t
  exprs : All (Expression Σ Γ) ts → All (Expression Σ Δ) Γ → All (Expression Σ Δ) ts

  expr (lit x)                es′ = lit x
  expr (state j)              es′ = state j
  expr (var j)                es′ = All.lookup j es′
  expr (e ≟ e₁)               es′ = expr e es′ ≟ expr e₁ es′
  expr (e <? e₁)              es′ = expr e es′ <? expr e₁ es′
  expr (inv e)                es′ = inv (expr e es′)
  expr (e && e₁)              es′ = expr e es′ && expr e₁ es′
  expr (e || e₁)              es′ = expr e es′ || expr e₁ es′
  expr (not e)                es′ = not (expr e es′)
  expr (e and e₁)             es′ = expr e es′ and expr e₁ es′
  expr (e or e₁)              es′ = expr e es′ or expr e₁ es′
  expr [ e ]                  es′ = [ expr e es′ ]
  expr (unbox e)              es′ = unbox (expr e es′)
  expr (merge e e₁ e₂)        es′ = merge (expr e es′) (expr e₁ es′) (expr e₂ es′)
  expr (slice e e₁)           es′ = slice (expr e es′) (expr e₁ es′)
  expr (cut e e₁)             es′ = cut (expr e es′) (expr e₁ es′)
  expr (cast eq e)            es′ = cast eq (expr e es′)
  expr (- e)                  es′ = - expr e es′
  expr (e + e₁)               es′ = expr e es′ + expr e₁ es′
  expr (e * e₁)               es′ = expr e es′ * expr e₁ es′
  expr (e ^ x)                es′ = expr e es′ ^ x
  expr (e >> n)               es′ = expr e es′ >> n
  expr (rnd e)                es′ = rnd (expr e es′)
  expr (fin f e)              es′ = fin f (expr e es′)
  expr (asInt e)              es′ = asInt (expr e es′)
  expr nil                    es′ = nil
  expr (cons e e₁)            es′ = cons (expr e es′) (expr e₁ es′)
  expr (head e)               es′ = head (expr e es′)
  expr (tail e)               es′ = tail (expr e es′)
  expr (call f es)            es′ = call f (exprs es es′)
  expr (if e then e₁ else e₂) es′ = if expr e es′ then expr e₁ es′ else expr e₂ es′

  exprs []       es′ = []
  exprs (e ∷ es) es′ = expr e es′ ∷ exprs es es′

  expr-depth : ∀ (e : Expression Σ Γ t) (es′ : All (Expression Σ Δ) Γ) → CallDepth.expr (expr e es′) ≤ CallDepth.expr e ⊔ CallDepth.exprs es′
  exprs-depth : ∀ (es : All (Expression Σ Γ) ts) (es′ : All (Expression Σ Δ) Γ) → CallDepth.exprs (exprs es es′) ≤ CallDepth.exprs es ⊔ CallDepth.exprs es′

  expr-depth (lit x)                es′ = z≤n
  expr-depth (state j)              es′ = z≤n
  expr-depth (var j)                es′ = CallDepth.lookup-≤ j es′
  expr-depth (e ≟ e₁)               es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (e <? e₁)              es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (inv e)                es′ = expr-depth e es′
  expr-depth (e && e₁)              es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (e || e₁)              es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (not e)                es′ = expr-depth e es′
  expr-depth (e and e₁)             es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (e or e₁)              es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth [ e ]                  es′ = expr-depth e es′
  expr-depth (unbox e)              es′ = expr-depth e es′
  expr-depth (merge e e₁ e₂)        es′ = join-lubs (CallDepth.exprs es′) 3 (expr-depth e es′ , expr-depth e₁ es′ , expr-depth e₂ es′)
  expr-depth (slice e e₁)           es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (cut e e₁)             es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (cast eq e)            es′ = expr-depth e es′
  expr-depth (- e)                  es′ = expr-depth e es′
  expr-depth (e + e₁)               es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (e * e₁)               es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (e ^ x)                es′ = expr-depth e es′
  expr-depth (e >> n)               es′ = expr-depth e es′
  expr-depth (rnd e)                es′ = expr-depth e es′
  expr-depth (fin f e)              es′ = expr-depth e es′
  expr-depth (asInt e)              es′ = expr-depth e es′
  expr-depth nil                    es′ = z≤n
  expr-depth (cons e e₁)            es′ = join-lubs (CallDepth.exprs es′) 2 (expr-depth e es′ , expr-depth e₁ es′)
  expr-depth (head e)               es′ = expr-depth e es′
  expr-depth (tail e)               es′ = expr-depth e es′
  expr-depth (call f es)            es′ = join-lubs (CallDepth.exprs es′) 2 (exprs-depth es es′ , ℕₚ.m≤m⊔n _ (CallDepth.exprs es′))
  expr-depth (if e then e₁ else e₂) es′ = join-lubs (CallDepth.exprs es′) 3 (expr-depth e es′ , expr-depth e₁ es′ , expr-depth e₂ es′)

  exprs-depth []       es′ = z≤n
  exprs-depth (e ∷ es) es′ = join-lubs (CallDepth.exprs es′) 2 (exprs-depth es es′ , expr-depth e es′)

module Update where
  expr : LocalReference Σ Γ t → Expression Σ Γ t → Expression Σ Γ t′ → Expression Σ Γ t′
  expr (var i)            val e′ = Subst.expr i e′ val
  expr [ ref ]            val e′ = expr ref (unbox val) e′
  expr (unbox ref)        val e′ = expr ref [ val ] e′
  expr (merge ref ref₁ e) val e′ = expr ref₁ (cut val e) (expr ref (slice val e) e′)
  expr (slice ref e)      val e′ = expr ref (merge val (cut (!! ref) e) e) e′
  expr (cut ref e)        val e′ = expr ref (merge (slice (!! ref) e) val e) e′
  expr (cast eq ref)      val e′ = expr ref (cast (sym eq) val) e′
  expr nil                val e′ = e′
  expr (cons ref ref₁)    val e′ = expr ref₁ (tail val) (expr ref (head val) e′)
  expr (head ref)         val e′ = expr ref (cons val (tail (!! ref))) e′
  expr (tail ref)         val e′ = expr ref (cons (head (!! ref)) val) e′

  expr-depth : ∀ (ref : LocalReference Σ Γ t) val (e′ : Expression Σ Γ t′) → CallDepth.expr (expr ref val e′) ≤ CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr val)
  expr-depth (var i)            val e′ = Subst.expr-depth i e′ val
  expr-depth [ ref ]            val e′ = expr-depth ref (unbox val) e′
  expr-depth (unbox ref)        val e′ = expr-depth ref [ val ] e′
  expr-depth (merge ref ref₁ e) val e′ = begin
    CallDepth.expr (expr ref₁ (cut val e) (expr ref (slice val e) e′))
      ≤⟨ expr-depth ref₁ _ _ ⟩
    CallDepth.expr (expr ref (slice val e) e′) ⊔ (CallDepth.locRef ref₁ ⊔ (CallDepth.expr val ⊔ CallDepth.expr e))
      ≤⟨ ℕₚ.⊔-monoˡ-≤ _ (expr-depth ref (slice val e) e′) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr val ⊔ CallDepth.expr e)) ⊔ (CallDepth.locRef ref₁ ⊔ (CallDepth.expr val ⊔ CallDepth.expr e))
      ≡⟨ solve-⊔ 5 (λ a b c d e → (a ⊕ (b ⊕ (e ⊕ d))) ⊕ (c ⊕ (e ⊕ d)) ⊜ a ⊕ (((b ⊕ c) ⊕ d) ⊕ e)) refl (CallDepth.expr e′) (CallDepth.locRef ref) _ _ _ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.locRef ref₁ ⊔ CallDepth.expr e ⊔ CallDepth.expr val)
      ∎
  expr-depth (slice ref e)      val e′ = begin
    CallDepth.expr (expr ref (merge val (cut (!! ref) e) e) e′)
      ≤⟨ expr-depth ref (merge val (cut (!! ref) e) e) e′ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr val ⊔ (CallDepth.expr (!! ref) ⊔ CallDepth.expr e) ⊔ CallDepth.expr e))
      ≡⟨ cong (λ x → CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr val ⊔ (x ⊔ _) ⊔ _))) (CallDepth.homo-!! ref) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr val ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr e) ⊔ CallDepth.expr e))
      ≡⟨ cong (CallDepth.expr e′ ⊔_) $ solve-⊔ 3 (λ a b c → a ⊕ ((c ⊕ (a ⊕ b)) ⊕ b) ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.locRef ref) _ _ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr e ⊔ CallDepth.expr val)
      ∎
  expr-depth (cut ref e)        val e′ = begin
    CallDepth.expr (expr ref (merge (slice (!! ref) e) val e) e′)
      ≤⟨ expr-depth ref (merge (slice (!! ref) e) val e) e′ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr (!! ref) ⊔ CallDepth.expr e ⊔ CallDepth.expr val ⊔ CallDepth.expr e))
      ≡⟨ cong (λ x → CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (x ⊔ _ ⊔ _ ⊔ _))) (CallDepth.homo-!! ref) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr e ⊔ CallDepth.expr val ⊔ CallDepth.expr e))
      ≡⟨ cong (CallDepth.expr e′ ⊔_) $ solve-⊔ 3 (λ a b c → a ⊕ (((a ⊕ b) ⊕ c) ⊕ b) ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.locRef ref) _ _ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr e ⊔ CallDepth.expr val)
      ∎
  expr-depth (cast eq ref)      val e′ = expr-depth ref (cast (sym eq) val) e′
  expr-depth nil                val e′ = ℕₚ.m≤m⊔n (CallDepth.expr e′) _
  expr-depth (cons ref ref₁)    val e′ = begin
    CallDepth.expr (expr ref₁ (tail val) (expr ref (head val) e′))
      ≤⟨ expr-depth ref₁ (tail val) (expr ref (head val) e′) ⟩
    CallDepth.expr (expr ref (head val) e′) ⊔ (CallDepth.locRef ref₁ ⊔ CallDepth.expr val)
      ≤⟨ ℕₚ.⊔-monoˡ-≤ _ (expr-depth ref (head val) e′) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr val) ⊔ (CallDepth.locRef ref₁ ⊔ CallDepth.expr val)
      ≡⟨ solve-⊔ 4 (λ a b c d → (a ⊕ (b ⊕ d)) ⊕ (c ⊕ d) ⊜ a ⊕ ((b ⊕ c) ⊕ d)) refl (CallDepth.expr e′) (CallDepth.locRef ref) _ _ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.locRef ref₁ ⊔ CallDepth.expr val)
      ∎
  expr-depth (head ref)         val e′ = begin
    CallDepth.expr (expr ref (cons val (tail (!! ref))) e′)
      ≤⟨ expr-depth ref (cons val (tail (!! ref))) e′ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr val ⊔ CallDepth.expr (!! ref)))
      ≡⟨ cong (λ x → CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr val ⊔ x))) (CallDepth.homo-!! ref) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr val ⊔ CallDepth.locRef ref))
      ≡⟨ cong (CallDepth.expr e′ ⊔_) (solve-⊔ 2 (λ a b → a ⊕ (b ⊕ a) ⊜ a ⊕ b) refl (CallDepth.locRef ref) _) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr val)
      ∎
  expr-depth (tail ref)         val e′ = begin
    CallDepth.expr (expr ref (cons (head (!! ref)) val) e′)
      ≤⟨ expr-depth ref (cons (head (!! ref)) val) e′ ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.expr (!! ref) ⊔ CallDepth.expr val))
      ≡⟨ cong (λ x → CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (x ⊔ _))) (CallDepth.homo-!! ref) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr val))
      ≡⟨ cong (CallDepth.expr e′ ⊔_) (solve-⊔ 2 (λ a b → a ⊕ (a ⊕ b) ⊜ a ⊕ b) refl (CallDepth.locRef ref) _) ⟩
    CallDepth.expr e′ ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr val)
      ∎

module Inline where
  private
    elses : LocalStatement Σ Γ → ℕ
    elses (s ∙ s₁)              = elses s ℕ.+ elses s₁
    elses skip                  = 0
    elses (ref ≔ val)           = 0
    elses (declare e s)         = elses s
    elses (if x then s)         = elses s
    elses (if x then s else s₁) = 1 ℕ.+ elses s ℕ.+ elses s₁
    elses (for n s)             = elses s

    structure : LocalStatement Σ Γ → ℕ
    structure (s ∙ s₁)              = 1 ℕ.+ structure s ℕ.+ structure s₁
    structure skip                  = 0
    structure (ref ≔ val)           = 0
    structure (declare e s)         = structure s
    structure (if x then s)         = 1 ℕ.+ 3 ℕ.* structure s
    structure (if x then s else s₁) = 1 ℕ.+ 3 ℕ.* structure s ℕ.+ structure s₁
    structure (for n s)             = 1 ℕ.+ structure s

    scope : LocalStatement Σ Γ → ℕ
    scope (s ∙ s₁)              = 0
    scope skip                  = 0
    scope (ref ≔ val)           = 0
    scope (declare e s)         = 1 ℕ.+ scope s
    scope (if x then s)         = 2 ℕ.* scope s
    scope (if x then s else s₁) = 0
    scope (for n s)             = 0

    weaken-elses : ∀ i t′ (s : LocalStatement Σ Γ) → elses (Weaken.locStmt i t′ s) ≡ elses s
    weaken-elses i t′ (s ∙ s₁)              = cong₂ ℕ._+_ (weaken-elses i t′ s) (weaken-elses i t′ s₁)
    weaken-elses i t′ skip                  = refl
    weaken-elses i t′ (ref ≔ val)           = refl
    weaken-elses i t′ (declare e s)         = weaken-elses (suc i) t′ s
    weaken-elses i t′ (if x then s)         = weaken-elses i t′ s
    weaken-elses i t′ (if x then s else s₁) = cong₂ (λ m n → 1 ℕ.+ m ℕ.+ n) (weaken-elses i t′ s) (weaken-elses i t′ s₁)
    weaken-elses i t′ (for n s)             = weaken-elses (suc i) t′ s

    weaken-structure : ∀ i t′ (s : LocalStatement Σ Γ) → structure (Weaken.locStmt i t′ s) ≡ structure s
    weaken-structure i t′ (s ∙ s₁)              = cong₂ (λ m n → 1 ℕ.+ m ℕ.+ n) (weaken-structure i t′ s) (weaken-structure i t′ s₁)
    weaken-structure i t′ skip                  = refl
    weaken-structure i t′ (ref ≔ val)           = refl
    weaken-structure i t′ (declare e s)         = weaken-structure (suc i) t′ s
    weaken-structure i t′ (if x then s)         = cong (λ m → 1 ℕ.+ 3 ℕ.* m) (weaken-structure i t′ s)
    weaken-structure i t′ (if x then s else s₁) = cong₂ (λ m n → 1 ℕ.+ 3 ℕ.* m ℕ.+ n) (weaken-structure i t′ s) (weaken-structure i t′ s₁)
    weaken-structure i t′ (for n s)             = cong suc (weaken-structure (suc i) t′ s)

    weaken-scope : ∀ i t′ (s : LocalStatement Σ Γ) → scope (Weaken.locStmt i t′ s) ≡ scope s
    weaken-scope i t′ (s ∙ s₁)              = refl
    weaken-scope i t′ skip                  = refl
    weaken-scope i t′ (ref ≔ val)           = refl
    weaken-scope i t′ (declare e s)         = cong suc (weaken-scope (suc i) t′ s)
    weaken-scope i t′ (if x then s)         = cong (2 ℕ.*_) (weaken-scope i t′ s)
    weaken-scope i t′ (if x then s else s₁) = refl
    weaken-scope i t′ (for n s)             = refl

    RecItem : Vec Type n → Set
    RecItem Σ = ∃ λ n → ∃ λ (Γ : Vec Type n) → LocalStatement Σ Γ

    P : ∀ (Σ : Vec Type n) → RecItem Σ → Set
    P Σ (_ , Γ , s) = ∀ {t} (e : Expression Σ Γ t) → ∃ λ (e′ : Expression Σ Γ t) → CallDepth.expr e′ ≤ CallDepth.locStmt s ⊔ CallDepth.expr e

    index : RecItem Σ → ℕ × ℕ × ℕ
    index = < elses , < structure , scope > > ∘ proj₂ ∘ proj₂

    infix 4 _≺_

    _≺_ : RecItem Σ → RecItem Σ → Set
    _≺_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_) on index

    ≺-wellFounded : WellFounded (_≺_ {Σ = Σ})
    ≺-wellFounded = On.wellFounded index (×-wellFounded ℕᵢ.<-wellFounded (×-wellFounded ℕᵢ.<-wellFounded ℕᵢ.<-wellFounded))

    ≤∧<⇒≺ : ∀ (item item₁ : RecItem Σ) → (_≤_ on proj₁ ∘ index) item item₁ → (×-Lex _≡_ _<_ _<_ on proj₂ ∘ index) item item₁ → item ≺ item₁
    ≤∧<⇒≺ item item₁ ≤₁ <₂ with proj₁ (index item) ℕₚ.<? proj₁ (index item₁)
    ... | yes <₁ = inj₁ <₁
    ... | no ≮₁  = inj₂ (ℕₚ.≤∧≮⇒≡ ≤₁ ≮₁ , <₂)

    pushIf : Expression Σ Γ bool → LocalStatement Σ Γ → LocalStatement Σ Γ
    pushIf e′ (s ∙ s₁)              = declare e′ (if var 0F then Weaken.locStmt 0F _ s ∙ if var 0F then Weaken.locStmt 0F _ s₁)
    pushIf e′ skip                  = skip
    pushIf e′ (ref ≔ val)           = ref ≔ (if e′ then val else !! ref)
    pushIf e′ (declare e s)         = declare e (if Weaken.expr 0F _ e′ then s)
    pushIf e′ (if x then s)         = if e′ && x then s
    pushIf e′ (if x then s else s₁) = declare (tup (e′ ∷ x ∷ [])) (if head (var 0F) && head (tail (var 0F)) then Weaken.locStmt 0F _ s ∙ if head (var 0F) && inv (head (tail (var 0F))) then Weaken.locStmt 0F _ s₁)
    pushIf e′ (for n s)             = declare e′ (for n (if var 1F then Weaken.locStmt 1F _ s))

    pushIf≺if‿then : ∀ (e : Expression Σ Γ bool) s → (-, -, pushIf e s) ≺ (-, -, (if e then s))
    pushIf≺if‿then e′ (s ∙ s₁)              = inj₂
      ( cong₂ ℕ._+_ (weaken-elses 0F bool s) (weaken-elses 0F bool s₁)
      , inj₁ (begin-strict
          1 ℕ.+ (1 ℕ.+ 3 ℕ.* structure (Weaken.locStmt 0F bool s)) ℕ.+ (1 ℕ.+ 3 ℕ.* structure (Weaken.locStmt 0F bool s₁))
            ≡⟨ cong₂ (λ m n → 1 ℕ.+ (1 ℕ.+ 3 ℕ.* m) ℕ.+ (1 ℕ.+ 3 ℕ.* n)) (weaken-structure 0F bool s) (weaken-structure 0F bool s₁) ⟩
          1 ℕ.+ (1 ℕ.+ 3 ℕ.* structure s) ℕ.+ (1 ℕ.+ 3 ℕ.* structure s₁)
            <⟨ ℕₚ.n<1+n _ ⟩
          2 ℕ.+ (1 ℕ.+ 3 ℕ.* structure s) ℕ.+ (1 ℕ.+ 3 ℕ.* structure s₁)
            ≡⟨ solve-+ 2
                 (λ a b →
                    con 2 :+ (con 1 :+ con 3 :* a) :+ (con 1 :+ con 3 :* b) :=
                    con 1 :+ con 3 :* (con 1 :+ a :+ b))
                 refl (structure s) (structure s₁) ⟩
          1 ℕ.+ 3 ℕ.* (1 ℕ.+ structure s ℕ.+ structure s₁)
            ∎)
      )
    pushIf≺if‿then e′ skip                  = inj₂ (refl , inj₁ ℕₚ.0<1+n)
    pushIf≺if‿then e′ (ref ≔ val)           = inj₂ (refl , inj₁ ℕₚ.0<1+n)
    pushIf≺if‿then e′ (declare e s)         = inj₂ (refl , inj₂ (refl , (begin-strict
      1 ℕ.+  2 ℕ.* scope s
        <⟨ ℕₚ.n<1+n _ ⟩
      2 ℕ.+  2 ℕ.* scope s
        ≡⟨ solve-+ 1 (λ a → con 2 :+ con 2 :* a := con 2 :* (con 1 :+ a)) refl (scope s) ⟩
      2 ℕ.* (1 ℕ.+ scope s)
        ∎)))
    pushIf≺if‿then e′ (if x then s)         = inj₂ (refl , (inj₁ (begin-strict
      1 ℕ.+ 3 ℕ.* structure s
        <⟨ ℕₚ.m<n+m _ {3 ℕ.+ 6 ℕ.* structure s} ℕₚ.0<1+n ⟩
      3 ℕ.+ 6 ℕ.* structure s ℕ.+ (1 ℕ.+ 3 ℕ.* structure s)
        ≡⟨ solve-+
             1
             (λ a → (con 3 :+ con 6 :* a) :+ (con 1 :+ con 3 :* a)
                 := con 1 :+ con 3 :* (con 1 :+ con 3 :* a))
             refl
             (structure s) ⟩
      1 ℕ.+ 3 ℕ.* (1 ℕ.+ 3 ℕ.* structure s)
        ∎)))
    pushIf≺if‿then e′ (if x then s else s₁) = inj₁ (begin-strict
      elses (Weaken.locStmt 0F (tuple (bool ∷ bool ∷ [])) s) ℕ.+ elses (Weaken.locStmt 0F (tuple (bool ∷ bool ∷ [])) s₁)
        ≡⟨ cong₂ ℕ._+_ (weaken-elses 0F _ s) (weaken-elses 0F _ s₁) ⟩
      elses s ℕ.+ elses s₁
        <⟨ ℕₚ.n<1+n _ ⟩
      1 ℕ.+ elses s ℕ.+ elses s₁
        ∎)
    pushIf≺if‿then e′ (for n s)             = inj₂
      ( weaken-elses 1F bool s
      , inj₁ (begin-strict
          2 ℕ.+ 3 ℕ.* structure (Weaken.locStmt 1F bool s)
            ≡⟨ cong (λ m → 2 ℕ.+ 3 ℕ.* m) (weaken-structure 1F bool s) ⟩
          2 ℕ.+ 3 ℕ.* structure s
            <⟨ ℕₚ.m<n+m _ {2} ℕₚ.0<1+n ⟩
          4 ℕ.+ 3 ℕ.* structure s
            ≡⟨ solve-+ 1 (λ a → con 4 :+ con 3 :* a := con 1 :+ con 3 :* (con 1 :+ a)) refl (structure s) ⟩
          1 ℕ.+ 3 ℕ.* (1 ℕ.+ structure s)
            ∎)
      )

    pushIf-depth : ∀ (e : Expression Σ Γ bool) s → CallDepth.locStmt (pushIf e s) ≤ CallDepth.locStmt (if e then s)
    pushIf-depth e′ (s ∙ s₁)              = begin
      CallDepth.locStmt (Weaken.locStmt 0F bool s) ⊔ 0 ⊔ (CallDepth.locStmt (Weaken.locStmt 0F bool s₁) ⊔ 0) ⊔ CallDepth.expr e′
        ≡⟨ cong₂ (λ m n → m ⊔ _ ⊔ (n ⊔ _) ⊔ _) (Weaken.locStmt-depth 0F bool s) (Weaken.locStmt-depth 0F bool s₁) ⟩
      CallDepth.locStmt s ⊔ 0 ⊔ (CallDepth.locStmt s₁ ⊔ 0) ⊔ CallDepth.expr e′
        ≡⟨ solve-⊔ 3 (λ a b c → ((a ⊕ ε) ⊕ (b ⊕ ε)) ⊕ c ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.locStmt s) _ _ ⟩
      CallDepth.locStmt s ⊔ CallDepth.locStmt s₁ ⊔ CallDepth.expr e′
        ∎
    pushIf-depth e′ skip                  = z≤n
    pushIf-depth e′ (ref ≔ val)           = begin
      CallDepth.locRef ref ⊔ (CallDepth.expr e′ ⊔ CallDepth.expr val ⊔ CallDepth.expr (!! ref))
        ≡⟨ cong (λ x → CallDepth.locRef ref ⊔ (CallDepth.expr e′ ⊔ CallDepth.expr val ⊔ x)) (CallDepth.homo-!! ref) ⟩
      CallDepth.locRef ref ⊔ (CallDepth.expr e′ ⊔ CallDepth.expr val ⊔ CallDepth.locRef ref)
        ≡⟨ solve-⊔ 3 (λ a b c → a ⊕ ((c ⊕ b) ⊕ a) ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.locRef ref) _ _ ⟩
      CallDepth.locRef ref ⊔ CallDepth.expr val ⊔ CallDepth.expr e′
        ∎
    pushIf-depth e′ (declare {t = t} e s) = begin
      CallDepth.locStmt s ⊔ CallDepth.expr (Weaken.expr 0F t e′) ⊔ CallDepth.expr e
        ≡⟨ cong (λ x → CallDepth.locStmt s ⊔ x ⊔ _) (Weaken.expr-depth 0F t e′) ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr e′ ⊔ CallDepth.expr e
        ≡⟨ solve-⊔ 3 (λ a b c → (a ⊕ c) ⊕ b ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.locStmt s) _ _ ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr e ⊔ CallDepth.expr e′
        ∎
    pushIf-depth e′ (if x then s)         = ℕₚ.≤-reflexive (solve-⊔ 3 (λ a b c → a ⊕ (c ⊕ b) ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.locStmt s) _ _)
    pushIf-depth e′ (if x then s else s₁) = begin
      CallDepth.locStmt (Weaken.locStmt 0F (tuple (bool ∷ bool ∷ [])) s) ⊔ 0 ⊔ (CallDepth.locStmt (Weaken.locStmt 0F (tuple (bool ∷ bool ∷ [])) s₁) ⊔ 0) ⊔ (CallDepth.expr e′ ⊔ (CallDepth.expr x ⊔ 0))
        ≡⟨ cong₂ (λ m n → m ⊔ 0 ⊔ (n ⊔ 0) ⊔ _) (Weaken.locStmt-depth 0F _ s) (Weaken.locStmt-depth 0F _ s₁) ⟩
      CallDepth.locStmt s ⊔ 0 ⊔ (CallDepth.locStmt s₁ ⊔ 0) ⊔ (CallDepth.expr e′ ⊔ (CallDepth.expr x ⊔ 0))
        ≡⟨ solve-⊔ 4 (λ a b c d → ((a ⊕ ε) ⊕ (b ⊕ ε)) ⊕ (d ⊕ (c ⊕ ε)) ⊜ ((a ⊕ b) ⊕ c) ⊕ d) refl (CallDepth.locStmt s) _ _ _ ⟩
      CallDepth.locStmt s ⊔ CallDepth.locStmt s₁ ⊔ CallDepth.expr x ⊔ CallDepth.expr e′
        ∎
    pushIf-depth e′ (for n s)             = begin
      CallDepth.locStmt (Weaken.locStmt 1F bool s) ⊔ 0 ⊔ CallDepth.expr e′
        ≡⟨ cong (λ x → x ⊔ _ ⊔ _) (Weaken.locStmt-depth 1F bool s) ⟩
      CallDepth.locStmt s ⊔ 0 ⊔ CallDepth.expr e′
        ≡⟨ cong (_⊔ _) (ℕₚ.⊔-identityʳ (CallDepth.locStmt s)) ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr e′
        ∎

    s≺s∙s₁ : ∀ (s s₁ : LocalStatement Σ Γ) → (-, -, s) ≺ (-, -, (s ∙ s₁))
    s≺s∙s₁ s s₁ = ≤∧<⇒≺ (-, -, s) (-, -, (s ∙ s₁)) (ℕₚ.m≤m+n (elses s) _) (inj₁ (ℕₚ.m≤m+n (suc (structure s)) _))

    s₁≺s∙s₁ : ∀ (s s₁ : LocalStatement Σ Γ) → (-, -, s₁) ≺ (-, -, (s ∙ s₁))
    s₁≺s∙s₁ s s₁ = ≤∧<⇒≺ (-, -, s₁) (-, -, (s ∙ s₁)) (ℕₚ.m≤n+m _ (elses s)) (inj₁ (ℕₚ.m<n+m _ ℕₚ.0<1+n))

    pushIfElse : Expression Σ Γ bool → LocalStatement Σ Γ → LocalStatement Σ Γ → LocalStatement Σ Γ
    pushIfElse e s s₁ = declare e (if var 0F then Weaken.locStmt 0F _ s ∙ if inv (var 0F) then Weaken.locStmt 0F _ s₁)

    pushIfElse≺if‿then‿else : ∀ (e : Expression Σ Γ bool) s s₁ → (-, -, pushIfElse e s s₁) ≺ (-, -, (if e then s else s₁))
    pushIfElse≺if‿then‿else e s s₁ = inj₁ (begin-strict
      elses (Weaken.locStmt 0F bool s) ℕ.+ elses (Weaken.locStmt 0F bool s₁)
        ≡⟨ cong₂ ℕ._+_ (weaken-elses 0F bool s) (weaken-elses 0F bool s₁) ⟩
      elses s ℕ.+ elses s₁
        <⟨ ℕₚ.n<1+n _ ⟩
      1 ℕ.+ elses s ℕ.+ elses s₁
        ∎)

    helper : ∀ item → Wf.WfRec _≺_ (P Σ) item → P Σ item
    proj₁ (helper (_ , _ , (s ∙ s₁))              rec e) = proj₁ (rec (-, -, s) (s≺s∙s₁ s s₁) (proj₁ (rec (-, -, s₁) (s₁≺s∙s₁ s s₁) e)))
    proj₁ (helper (_ , _ , skip)                  rec e) = e
    proj₁ (helper (_ , _ , (ref ≔ val))           rec e) = Update.expr ref val e
    proj₁ (helper (_ , _ , declare x s)           rec e) = Elim.expr 0F (proj₁ (rec (-, -, s) (inj₂ (refl , inj₂ (refl , ℕₚ.n<1+n _))) (Weaken.expr 0F _ e))) x
    proj₁ (helper (_ , _ , (if x then s))         rec e) = proj₁ (rec (-, -, pushIf x s) (pushIf≺if‿then x s) e)
    proj₁ (helper (_ , _ , (if x then s else s₁)) rec e) = proj₁ (rec (-, -, pushIfElse x s s₁) (pushIfElse≺if‿then‿else x s s₁) e)
    proj₁ (helper (_ , _ , for n s)               rec e) = Vec.foldr (λ _ → Expression _ _ _) (λ i e → proj₁ (rec (-, -, declare (lit i) s) (inj₂ (refl , inj₁ (ℕₚ.n<1+n (structure s)))) e)) e (Vec.allFin n)
    proj₂ (helper (_ , _ , (s ∙ s₁))              rec e) = begin
      CallDepth.expr (proj₁ outer)
        ≤⟨  proj₂ outer ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr (proj₁ inner)
        ≤⟨  ℕₚ.⊔-monoʳ-≤ (CallDepth.locStmt s) (proj₂ inner) ⟩
      CallDepth.locStmt s ⊔ (CallDepth.locStmt s₁ ⊔ CallDepth.expr e)
        ≡˘⟨ ℕₚ.⊔-assoc (CallDepth.locStmt s) _ _ ⟩
      CallDepth.locStmt s ⊔ CallDepth.locStmt s₁ ⊔ CallDepth.expr e
        ∎
      where
      inner = rec (-, -, s₁) (s₁≺s∙s₁ s s₁) e
      outer = rec (-, -, s) (s≺s∙s₁ s s₁) (proj₁ inner)
    proj₂ (helper (_ , _ , skip)                  rec e) = ℕₚ.≤-refl
    proj₂ (helper (_ , _ , (ref ≔ val))           rec e) = begin
      CallDepth.expr (Update.expr ref val e)
        ≤⟨ Update.expr-depth ref val e ⟩
      CallDepth.expr e ⊔ (CallDepth.locRef ref ⊔ CallDepth.expr val)
        ≡⟨ ℕₚ.⊔-comm (CallDepth.expr e) _ ⟩
      CallDepth.locRef ref ⊔ CallDepth.expr val ⊔ CallDepth.expr e
        ∎
    proj₂ (helper (_ , _ , declare x s)           rec e) = begin
      CallDepth.expr (Elim.expr 0F (proj₁ inner) x)
        ≤⟨ Elim.expr-depth 0F (proj₁ inner) x ⟩
      CallDepth.expr (proj₁ inner) ⊔ CallDepth.expr x
        ≤⟨ ℕₚ.⊔-monoˡ-≤ _ (proj₂ inner) ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr (Weaken.expr 0F _ e) ⊔ CallDepth.expr x
        ≡⟨ cong (λ x → CallDepth.locStmt s ⊔ x ⊔ _) (Weaken.expr-depth 0F _ e) ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr e ⊔ CallDepth.expr x
        ≡⟨ solve-⊔ 3 (λ a b c → (a ⊕ c) ⊕ b ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.locStmt s) _ _ ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr x ⊔ CallDepth.expr e
        ∎
      where inner = rec (-, -, s) _ (Weaken.expr 0F _ e)
    proj₂ (helper (_ , _ , (if x then s))         rec e) = begin
      CallDepth.expr (proj₁ inner)
        ≤⟨ proj₂ inner ⟩
      CallDepth.locStmt (pushIf x s) ⊔ CallDepth.expr e
        ≤⟨ ℕₚ.⊔-monoˡ-≤ _ (pushIf-depth x s) ⟩
      CallDepth.locStmt s ⊔ CallDepth.expr x ⊔ CallDepth.expr e
        ∎
      where inner = rec (-, -, pushIf x s) (pushIf≺if‿then x s) e
    proj₂ (helper (_ , _ , (if x then s else s₁)) rec e) = begin
      CallDepth.expr (proj₁ inner)
        ≤⟨ proj₂ inner ⟩
      CallDepth.locStmt (Weaken.locStmt 0F bool s) ⊔ 0 ⊔ (CallDepth.locStmt (Weaken.locStmt 0F bool s₁) ⊔ 0) ⊔ CallDepth.expr x ⊔ CallDepth.expr e
        ≡⟨ cong₂ (λ m n → m ⊔ 0 ⊔ (n ⊔ 0) ⊔ _ ⊔ _) (Weaken.locStmt-depth 0F bool s) (Weaken.locStmt-depth 0F bool s₁) ⟩
      CallDepth.locStmt s ⊔ 0 ⊔ (CallDepth.locStmt s₁ ⊔ 0) ⊔ CallDepth.expr x ⊔ CallDepth.expr e
        ≡⟨ cong (λ x → x ⊔ _ ⊔ _) (solve-⊔ 2 (λ a b → (a ⊕ ε) ⊕ (b ⊕ ε) ⊜ a ⊕ b) refl (CallDepth.locStmt s) _) ⟩
      CallDepth.locStmt s ⊔ CallDepth.locStmt s₁ ⊔ CallDepth.expr x ⊔ CallDepth.expr e
        ∎
      where inner = rec (-, -, pushIfElse x s s₁) (pushIfElse≺if‿then‿else x s s₁) e
    proj₂ (helper (_ , _ , for n s)               rec e) = foldr-lubs
      _
      e
      (λ e′ → CallDepth.expr e′ ≤ CallDepth.locStmt s ⊔ CallDepth.expr e)
      (ℕₚ.m≤n⊔m (CallDepth.locStmt s) _)
      (λ i {e′} e′≤s⊔e → begin
        CallDepth.expr (proj₁ (rec (-, -, declare (lit i) s) _ e′))
          ≤⟨ proj₂ (rec (-, -, declare (lit i) s) _ e′) ⟩
        CallDepth.locStmt s ⊔ 0 ⊔ CallDepth.expr e′
          ≤⟨ ℕₚ.⊔-monoʳ-≤ (CallDepth.locStmt s ⊔ _) e′≤s⊔e ⟩
        CallDepth.locStmt s ⊔ 0 ⊔ (CallDepth.locStmt s ⊔ CallDepth.expr e)
          ≡⟨ solve-⊔ 2 (λ a b → (a ⊕ ε) ⊕ (a ⊕ b) ⊜ a ⊕ b) refl (CallDepth.locStmt s) _ ⟩
        CallDepth.locStmt s ⊔ CallDepth.expr e
          ∎)
      (Vec.allFin n)

    helper′ : ∀ (s : LocalStatement Σ Γ) (e : Expression Σ Γ t) → ∃ λ (e′ : Expression Σ Γ t) → CallDepth.expr e′ ≤ CallDepth.locStmt s ⊔ CallDepth.expr e
    helper′ s = Wf.All.wfRec ≺-wellFounded _ (P _) helper (-, -, s)

  fun : Function Σ Δ ret → All (Expression Σ Γ) Δ → Expression Σ Γ ret
  fun (declare e f) es = fun f (SubstAll.expr e es ∷ es)
  fun (s ∙return e) es = SubstAll.expr (proj₁ (helper′ s e)) es

  fun-depth : ∀ (f : Function Σ Δ ret) (es : All (Expression Σ Γ) Δ) → CallDepth.expr (fun f es) ≤ CallDepth.fun f ⊔ CallDepth.exprs es
  fun-depth (declare e f) es = begin
    CallDepth.expr (fun f (SubstAll.expr e es ∷ es))
      ≤⟨ fun-depth f (SubstAll.expr e es ∷ es) ⟩
    CallDepth.fun f ⊔ (CallDepth.exprs es ⊔ CallDepth.expr (SubstAll.expr e es))
      ≤⟨ ℕₚ.⊔-monoʳ-≤ (CallDepth.fun f) (ℕₚ.⊔-monoʳ-≤ (CallDepth.exprs es) (SubstAll.expr-depth e es)) ⟩
    CallDepth.fun f ⊔ (CallDepth.exprs es ⊔ (CallDepth.expr e ⊔ CallDepth.exprs es))
      ≡⟨ solve-⊔ 3 (λ a b c → a ⊕ (c ⊕ (b ⊕ c)) ⊜ (a ⊕ b) ⊕ c) refl (CallDepth.fun f) _ _ ⟩
    CallDepth.fun f ⊔ CallDepth.expr e ⊔ CallDepth.exprs es
      ∎
  fun-depth (s ∙return e) es = begin
    CallDepth.expr (SubstAll.expr (proj₁ (helper′ s e)) es)
      ≤⟨ SubstAll.expr-depth (proj₁ (helper′ s e)) es ⟩
    CallDepth.expr (proj₁ (helper′ s e)) ⊔ CallDepth.exprs es
      ≤⟨ ℕₚ.⊔-monoˡ-≤ _ (proj₂ (helper′ s e)) ⟩
    CallDepth.locStmt s ⊔ CallDepth.expr e ⊔ CallDepth.exprs es
      ∎

module Flatten where
  private
    structure : Expression Σ Γ t → ℕ
    structures : All (Expression Σ Γ) ts → ℕ
    structure (lit x)                = suc (Σ[ 0 ] _)
    structure (state i)              = suc (Σ[ 0 ] _)
    structure (var i)                = suc (Σ[ 0 ] _)
    structure (e ≟ e₁)               = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (e <? e₁)              = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (inv e)                = suc (Σ[ 1 ] structure e)
    structure (e && e₁)              = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (e || e₁)              = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (not e)                = suc (Σ[ 1 ] structure e)
    structure (e and e₁)             = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (e or e₁)              = suc (Σ[ 2 ] (structure e , structure e₁))
    structure ([ e ])                = suc (Σ[ 1 ] structure e)
    structure (unbox e)              = suc (Σ[ 1 ] structure e)
    structure (merge e e₁ e₂)        = suc (Σ[ 3 ] (structure e , structure e₁ , structure e₂))
    structure (slice e e₁)           = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (cut e e₁)             = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (cast eq e)            = suc (Σ[ 1 ] structure e)
    structure (- e)                  = suc (Σ[ 1 ] structure e)
    structure (e + e₁)               = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (e * e₁)               = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (e ^ x)                = suc (Σ[ 1 ] structure e)
    structure (e >> n)               = suc (Σ[ 1 ] structure e)
    structure (rnd e)                = suc (Σ[ 1 ] structure e)
    structure (fin f e)              = suc (Σ[ 1 ] structure e)
    structure (asInt e)              = suc (Σ[ 1 ] structure e)
    structure (nil)                  = suc (Σ[ 0 ] _)
    structure (cons e e₁)            = suc (Σ[ 2 ] (structure e , structure e₁))
    structure (head e)               = suc (Σ[ 1 ] structure e)
    structure (tail e)               = suc (Σ[ 1 ] structure e)
    structure (call f es)            = structures es
    structure (if e then e₁ else e₂) = suc (Σ[ 3 ] (structure e , structure e₁ , structure e₂))

    structures []       = 1
    structures (e ∷ es) = structures es ℕ.+ structure e

    structures>0 : ∀ (es : All (Expression Σ Γ) ts) → 0 < structures es
    structures>0 []       = ℕₚ.0<1+n
    structures>0 (e ∷ es) = ℕₚ.<-transˡ (structures>0 es) (ℕₚ.m≤m+n _ _)

    structure-∷ˡ-< : ∀ (e : Expression Σ Γ t) (es : All (Expression Σ Γ) ts) → structure e < structures (e ∷ es)
    structure-∷ˡ-< e es = ℕₚ.m<n+m _ (structures>0 es)

    structure-∷ʳ-≤ : ∀ (e : Expression Σ Γ t) (es : All (Expression Σ Γ) ts) → structures es ≤ structures (e ∷ es)
    structure-∷ʳ-≤ e es = ℕₚ.m≤m+n _ _

    RecItem : Vec Type m → Vec Type n → Set
    RecItem Σ Γ = ∃ (Expression Σ Γ)

    RecItems : Vec Type m → Vec Type n → Set
    RecItems Σ Γ = ∃ λ n → ∃ (All (Expression Σ Γ) {n})

    P : ∀ (Σ : Vec Type m) (Γ : Vec Type n) → RecItem Σ Γ → Set
    P Σ Γ (t , e) = ∃ λ (e′ : Expression Σ Γ t) → CallDepth.expr e′ ≡ 0

    Ps : ∀ (Σ : Vec Type k) (Γ : Vec Type m) → RecItems Σ Γ → Set
    Ps Σ Γ (n , ts , es) = ∃ λ (es′ : All (Expression Σ Γ) ts) → CallDepth.exprs es′ ≡ 0

    index : RecItem Σ Γ → ℕ × ℕ
    index = < CallDepth.expr , structure > ∘ proj₂
    index′ : RecItems Σ Γ → ℕ × ℕ
    index′ = < CallDepth.exprs , structures > ∘ proj₂ ∘ proj₂

    infix 4 _≺_ _≺′_ _≺′′_

    _≺_ : RecItem Σ Γ → RecItem Σ Γ → Set
    _≺_ = ×-Lex _≡_ _<_ _<_ on index

    _≺′_ : RecItem Σ Γ → RecItems Σ Γ → Set
    item ≺′ items = ×-Lex _≡_ _<_ _<_ (index item) (index′ items)

    _≺′′_ : RecItems Σ Γ → RecItems Σ Γ → Set
    _≺′′_ = ×-Lex _≡_ _<_ _≤_ on index′

    ≺-wellFounded : WellFounded (_≺_ {Σ = Σ} {Γ = Γ})
    ≺-wellFounded = On.wellFounded index (×-wellFounded ℕᵢ.<-wellFounded ℕᵢ.<-wellFounded)

    ≤∧<⇒≺ : ∀ (item item₁ : RecItem Σ Γ) → (_≤_ on proj₁ ∘ index) item item₁ → (_<_ on proj₂ ∘ index) item item₁ → item ≺ item₁
    ≤∧<⇒≺ item item₁ ≤₁ <₂ with proj₁ (index item) ℕₚ.<? proj₁ (index item₁)
    ... | yes <₁ = inj₁ <₁
    ... | no ≮₁  = inj₂ (ℕₚ.≤∧≮⇒≡ ≤₁ ≮₁ , <₂)

    ≤∧<⇒≺′ : ∀ (item : RecItem Σ Γ) items → proj₁ (index item) ≤ proj₁ (index′ items) → proj₂ (index item) < proj₂ (index′ items) → item ≺′ items
    ≤∧<⇒≺′ item items ≤₁ <₂ with proj₁ (index item) ℕₚ.<? proj₁ (index′ items)
    ... | yes <₁ = inj₁ <₁
    ... | no ≮₁  = inj₂ (ℕₚ.≤∧≮⇒≡ ≤₁ ≮₁ , <₂)

    ≤∧≤⇒≺′′ : ∀ (items items₁ : RecItems Σ Γ) → (_≤_ on proj₁ ∘ index′) items items₁ → (_≤_ on proj₂ ∘ index′) items items₁ → items ≺′′ items₁
    ≤∧≤⇒≺′′ items items₁ ≤₁ ≤₂ with proj₁ (index′ items) ℕₚ.<? proj₁ (index′ items₁)
    ... | yes <₁ = inj₁ <₁
    ... | no ≮₁  = inj₂ (ℕₚ.≤∧≮⇒≡ ≤₁ ≮₁ , ≤₂)

    ≺′-≺′′-trans : ∀ (item : RecItem Σ Γ) items items₁ → item ≺′ items → items ≺′′ items₁ → item ≺′ items₁
    ≺′-≺′′-trans _ _ _ (inj₁ <₁)        (inj₁ <₂)        = inj₁ (ℕₚ.<-trans <₁ <₂)
    ≺′-≺′′-trans _ _ _ (inj₁ <₁)        (inj₂ (≡₂ , _))  = inj₁ (proj₁ ℕₚ.<-resp₂-≡ ≡₂ <₁)
    ≺′-≺′′-trans _ _ _ (inj₂ (≡₁ , _))  (inj₁ <₂)        = inj₁ (proj₂ ℕₚ.<-resp₂-≡ (sym ≡₁) <₂)
    ≺′-≺′′-trans _ _ _ (inj₂ (≡₁ , <₁)) (inj₂ (≡₂ , ≤₂)) = inj₂ (trans ≡₁ ≡₂ , ℕₚ.<-transˡ <₁ ≤₂)

    ≺′′-trans : ∀ (items items₁ items₂ : RecItems Σ Γ) → items ≺′′ items₁ → items₁ ≺′′ items₂ → items ≺′′ items₂
    ≺′′-trans _ _ _ (inj₁ <₁)        (inj₁ <₂)        = inj₁ (ℕₚ.<-trans <₁ <₂)
    ≺′′-trans _ _ _ (inj₁ <₁)        (inj₂ (≡₂ , _))  = inj₁ (proj₁ ℕₚ.<-resp₂-≡ ≡₂ <₁)
    ≺′′-trans _ _ _ (inj₂ (≡₁ , _))  (inj₁ <₂)        = inj₁ (proj₂ ℕₚ.<-resp₂-≡ (sym ≡₁) <₂)
    ≺′′-trans _ _ _ (inj₂ (≡₁ , ≤₁)) (inj₂ (≡₂ , ≤₂)) = inj₂ (trans ≡₁ ≡₂ , ℕₚ.≤-trans ≤₁ ≤₂)

    ∷ˡ-≺′ : ∀ (e : Expression Σ Γ t) (es : All (Expression Σ Γ) ts) → (-, e) ≺′ (-, -, e ∷ es)
    ∷ˡ-≺′ e es = ≤∧<⇒≺′ (-, e) (-, -, e ∷ es) (CallDepth.∷ˡ-≤ e es) (structure-∷ˡ-< e es)

    ∷ʳ-≺′′ : ∀ (e : Expression Σ Γ t) (es : All (Expression Σ Γ) ts) → (-, -, es) ≺′′ (-, -, e ∷ es)
    ∷ʳ-≺′′ e es = ≤∧≤⇒≺′′ (-, -, es) (-, -, e ∷ es) (CallDepth.∷ʳ-≤ e es) (structure-∷ʳ-≤ e es)

    toVecᵣ : ∀ {ts : Vec Type n} → All (Expression Σ Γ) ts → RecItem Σ Γ Vecᵣ.^ n
    toVecᵣ []       = _
    toVecᵣ (e ∷ es) = Vecᵣ.cons _ (-, e) (toVecᵣ es)

    toSets : Vec Type m → Vec Type n → Vec Type o → Sets o 0ℓs
    toSets Σ Γ []       = _
    toSets Σ Γ (t ∷ ts) = Expression Σ Γ t , toSets Σ Γ ts

    toProduct : ∀ {ts : Vec Type n} → All (Expression Σ Γ) ts → Product n (toSets Σ Γ ts)
    toProduct []            = _
    toProduct (e ∷ [])      = e
    toProduct (e ∷ e₁ ∷ es) = e , toProduct (e₁ ∷ es)

    rec-helper : ∀ {Σ : Vec Type k} {Γ : Vec Type m} {ts : Vec Type n}
              i (es : All (Expression Σ Γ) ts) (f : toSets Σ Γ ts ⇉ Expression Σ Γ t) →
            (⨆[ n ] Vecᵣ.map (proj₁ ∘ index) n (toVecᵣ es) , suc (Σ[ n ] Vecᵣ.map (proj₂ ∘ index) n (toVecᵣ es))) ≡ index (-, uncurryₙ n f (toProduct es)) →
            Vecᵣ.lookup i (toVecᵣ es) ≺ (-, uncurryₙ n f (toProduct es))
    rec-helper {n = n} i es f eq = ≤∧<⇒≺
      (Vecᵣ.lookup i (toVecᵣ es))
      (-, uncurryₙ n f (toProduct es))
      (begin
        proj₁ (index (Vecᵣ.lookup i (toVecᵣ es)))              ≡˘⟨ lookupᵣ-map i (toVecᵣ es) ⟩
        Vecᵣ.lookup i (Vecᵣ.map (proj₁ ∘ index) _ (toVecᵣ es)) ≤⟨  lookup-⨆-≤ i (Vecᵣ.map (proj₁ ∘ index) _ (toVecᵣ es)) ⟩
        ⨆[ n ] Vecᵣ.map (proj₁ ∘ index) _ (toVecᵣ es)          ≡⟨  cong proj₁ eq ⟩
        CallDepth.expr (uncurryₙ n f (toProduct es))           ∎)
      (begin-strict
        proj₂ (index (Vecᵣ.lookup i (toVecᵣ es)))              ≡˘⟨ lookupᵣ-map i (toVecᵣ es) ⟩
        Vecᵣ.lookup i (Vecᵣ.map (proj₂ ∘ index) _ (toVecᵣ es)) ≤⟨  lookup-Σ-≤ i (Vecᵣ.map (proj₂ ∘ index) _ (toVecᵣ es)) ⟩
        Σ[ n ] Vecᵣ.map (proj₂ ∘ index) _ (toVecᵣ es)          <⟨  ℕₚ.n<1+n _ ⟩
        suc (Σ[ n ] Vecᵣ.map (proj₂ ∘ index) _ (toVecᵣ es))    ≡⟨  cong proj₂ eq ⟩
        structure (uncurryₙ n f (toProduct es))                ∎)

    helper : ∀ item → Wf.WfRec _≺_ (P Σ Γ) item → P Σ Γ item
    helper′ : ∀ items → (∀ item → item ≺′ items → P Σ Γ item) → (∀ items₁ → items₁ ≺′′ items → Ps Σ Γ items₁) → Ps Σ Γ items
    helper (_ , lit x)                  rec = lit x , refl
    helper (_ , state i)                rec = state i , refl
    helper (_ , var i)                  rec = var i , refl
    helper (_ , (e ≟ e₁))               rec = (proj₁ e′ ≟ proj₁ e₁′) , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _≟_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _≟_ refl)
    helper (_ , (e <? e₁))              rec = (proj₁ e′ <? proj₁ e₁′) , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _<?_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _<?_ refl)
    helper (_ , inv e)                  rec = inv (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) inv refl)
    helper (_ , e && e₁)                rec = proj₁ e′ && proj₁ e₁′ , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _&&_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _&&_ refl)
    helper (_ , e || e₁)                rec = proj₁ e′ || proj₁ e₁′ , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _||_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _||_ refl)
    helper (_ , not e)                  rec = not (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) not refl)
    helper (_ , e and e₁)               rec = proj₁ e′ and proj₁ e₁′ , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _and_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _and_ refl)
    helper (_ , e or e₁)                rec = proj₁ e′ or proj₁ e₁′ , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _or_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _or_ refl)
    helper (_ , [ e ])                  rec = [ proj₁ e′ ] , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) [_] refl)
    helper (_ , unbox e)                rec = unbox (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) unbox refl)
    helper (_ , merge e e₁ e₂)          rec = merge (proj₁ e′) (proj₁ e₁′) (proj₁ e₂′) , congₙ 3 (λ a b c → a ⊔ b ⊔ c) (proj₂ e′) (proj₂ e₁′) (proj₂ e₂′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ e₂ ∷ []) merge refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ e₂ ∷ []) merge refl)
      e₂′ = rec (-, e₂) (rec-helper 2F (e ∷ e₁ ∷ e₂ ∷ []) merge refl)
    helper (_ , slice e e₁)             rec = slice (proj₁ e′) (proj₁ e₁′) , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) slice refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) slice refl)
    helper (_ , cut e e₁)               rec = cut (proj₁ e′) (proj₁ e₁′) , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) cut refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) cut refl)
    helper (_ , cast eq e)              rec = cast eq (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) (cast eq) refl)
    helper (_ , - e)                    rec = - proj₁ e′ , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) -_ refl)
    helper (_ , e + e₁)                 rec = proj₁ e′ + proj₁ e₁′ , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _+_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _+_ refl)
    helper (_ , e * e₁)                 rec = proj₁ e′ * proj₁ e₁′ , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) _*_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) _*_ refl)
    helper (_ , e ^ x)                  rec = proj₁ e′ ^ x , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) (_^ x) refl)
    helper (_ , e >> n)                 rec = proj₁ e′ >> n , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) (_>> n) refl)
    helper (_ , rnd e)                  rec = rnd (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) rnd refl)
    helper (_ , fin f e)                rec = fin f (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) (fin f) refl)
    helper (_ , asInt e)                rec = asInt (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) asInt refl)
    helper (_ , nil)                    rec = nil , refl
    helper (_ , cons e e₁)              rec = cons (proj₁ e′) (proj₁ e₁′) , cong₂ _⊔_ (proj₂ e′) (proj₂ e₁′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ []) cons refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ []) cons refl)
    helper (_ , head e)                 rec = head (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) head refl)
    helper (_ , tail e)                 rec = tail (proj₁ e′) , proj₂ e′
      where e′ = rec (-, e) (rec-helper 0F (e ∷ []) tail refl)
    helper (_ , call f es)              rec = rec
      (-, Inline.fun f (proj₁ es′))
      (inj₁ (begin-strict
        CallDepth.expr (Inline.fun f (proj₁ es′))     ≤⟨ Inline.fun-depth f (proj₁ es′) ⟩
        CallDepth.fun f ⊔ CallDepth.exprs (proj₁ es′) ≡⟨ cong (CallDepth.fun f ⊔_) (proj₂ es′) ⟩
        CallDepth.fun f ⊔ 0                           ≡⟨ ℕₚ.⊔-identityʳ _ ⟩
        CallDepth.fun f                               <⟨ ℕₚ.n<1+n _ ⟩
        suc (CallDepth.fun f)                         ≤⟨ ℕₚ.m≤n⊔m (CallDepth.exprs es) _ ⟩
        CallDepth.exprs es ⊔ suc (CallDepth.fun f)    ∎))
      where
      rec′ : ∀ item → item ≺′ (-, (-, es)) → P _ _ item
      rec′ item i≺es = rec item (lemma item i≺es)
        where
        lemma : ∀ item → item ≺′ (-, -, es) → item ≺ (-, call f es)
        lemma item (inj₁ <-depth)                 = inj₁ (begin-strict
          CallDepth.expr (proj₂ item) <⟨ <-depth ⟩
          CallDepth.exprs es          ≤⟨ ℕₚ.m≤m⊔n (CallDepth.exprs es) _ ⟩
          CallDepth.expr (call f es)  ∎)
        lemma item (inj₂ (≡-depth , <-structure)) = ≤∧<⇒≺ item (-, call f es)
          (begin
            CallDepth.expr (proj₂ item) ≡⟨ ≡-depth ⟩
            CallDepth.exprs es          ≤⟨ ℕₚ.m≤m⊔n (CallDepth.exprs es) _ ⟩
            CallDepth.expr (call f es)  ∎)
          <-structure

      rec′′ : ∀ items → items ≺′′ (-, (-, es)) → Ps _ _ items
      rec′′ (_ , _ , es′) = go es′
        where
        go : ∀ (es′ : All (Expression _ _) ts) → (-, -, es′) ≺′′ (-, -, es) → Ps _ _ (-, -, es′)
        go []        ≺′′ = [] , refl
        go (e ∷ es′) ≺′′ = proj₁ a ∷ proj₁ b , cong₂ _⊔_ (proj₂ b) (proj₂ a)
          where
          a = rec′ (-, e) (≺′-≺′′-trans (-, e) (-, -, e ∷ es′) (-, -, es) (∷ˡ-≺′ e es′) ≺′′)
          b = go es′ (≺′′-trans (-, -, es′) (-, -, e ∷ es′) (-, -, es) (∷ʳ-≺′′ e es′) ≺′′)

      es′ = helper′ (-, -, es) rec′ rec′′
    helper (_ , (if e then e₁ else e₂)) rec = (if proj₁ e′ then proj₁ e₁′ else proj₁ e₂′) , congₙ 3 (λ a b c → a ⊔ b ⊔ c) (proj₂ e′) (proj₂ e₁′) (proj₂ e₂′)
      where
      e′ = rec (-, e) (rec-helper 0F (e ∷ e₁ ∷ e₂ ∷ []) if_then_else_ refl)
      e₁′ = rec (-, e₁) (rec-helper 1F (e ∷ e₁ ∷ e₂ ∷ []) if_then_else_ refl)
      e₂′ = rec (-, e₂) (rec-helper 2F (e ∷ e₁ ∷ e₂ ∷ []) if_then_else_ refl)

    helper′ (_ , _ , [])     rec′ rec′′ = [] , refl
    helper′ (_ , _ , e ∷ es) rec′ rec′′ =
      proj₁ a ∷ proj₁ b , cong₂ _⊔_ (proj₂ b) (proj₂ a)
      where
      a = rec′ (-, e) (∷ˡ-≺′ e es)
      b = rec′′ (-, -, es) (∷ʳ-≺′′ e es)

  expr : Expression Σ Γ t → Expression Σ Γ t
  expr e = proj₁ (Wf.All.wfRec ≺-wellFounded _ (P _ _) helper (-, e))

  expr-depth : ∀ (e : Expression Σ Γ t) → CallDepth.expr (expr e) ≡ 0
  expr-depth e = proj₂ (Wf.All.wfRec ≺-wellFounded _ (P _ _) helper (-, e))
