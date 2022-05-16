------------------------------------------------------------------------
-- Agda Helium
--
-- Base definitions for the denotational semantics.
------------------------------------------------------------------------

{-# OPTIONS --safe --without-K #-}

open import Helium.Data.Pseudocode.Algebra using (RawPseudocode)

module Helium.Semantics.Denotational.Core
  {i₁ i₂ i₃ r₁ r₂ r₃}
  (rawPseudocode : RawPseudocode i₁ i₂ i₃ r₁ r₂ r₃)
  where

private
  open module C = RawPseudocode rawPseudocode

import Data.Bool as Bool
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (zero)
import Data.Integer as 𝕀
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; <_,_>; uncurry)
open import Data.Vec as Vec using (Vec; []; _∷_; map; zipWith)
open import Data.Vec.Relation.Unary.All using (All; []; _∷_)
open import Function
open import Helium.Data.Pseudocode.Core
open import Helium.Semantics.Core rawPseudocode
open import Level hiding (zero)
open import Relation.Binary.PropositionalEquality using (sym)
open import Relation.Nullary using (does)

private
  variable
    n : ℕ
    t : Type
    Σ Γ ts : Vec Type n


module Semantics (2≉0 : 2≉0) where
  expr      : Expression Σ Γ t → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ t ⟧ₜ
  exprs     : All (Expression Σ Γ) ts → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ ts ⟧ₜₛ
  ref       : Reference Σ Γ t → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ t ⟧ₜ
  locRef    : LocalReference Σ Γ t → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ t ⟧ₜ
  assign    : Reference Σ Γ t → ⟦ t ⟧ₜ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ
  locAssign : LocalReference Σ Γ t → ⟦ t ⟧ₜ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ
  stmt      : Statement Σ Γ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ
  locStmt   : LocalStatement Σ Γ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Γ ⟧ₜₛ
  fun       : Function Σ Γ t → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ t ⟧ₜ
  proc      : Procedure Σ Γ → ⟦ Σ ⟧ₜₛ × ⟦ Γ ⟧ₜₛ → ⟦ Σ ⟧ₜₛ

  expr (lit {t = t} x)        = const (Κ[ t ] x)
  expr {Σ = Σ} (state i)      = fetch i Σ ∘ proj₁
  expr {Γ = Γ} (var i)        = fetch i Γ ∘ proj₂
  expr (e ≟ e₁)               = lift ∘ does ∘ uncurry ≈-dec ∘ < expr e , expr e₁ >
  expr (e <? e₁)              = lift ∘ does ∘ uncurry <-dec ∘ < expr e , expr e₁ >
  expr (inv e)                = lift ∘ Bool.not ∘ lower ∘ expr e
  expr (e && e₁)              = lift ∘ uncurry (Bool._∧_ on lower) ∘ < expr e , expr e₁ >
  expr (e || e₁)              = lift ∘ uncurry (Bool._∨_ on lower) ∘ < expr e , expr e₁ >
  expr (not e)                = map (lift ∘ Bool.not ∘ lower) ∘ expr e
  expr (e and e₁)             = uncurry (zipWith (lift ∘₂ Bool._∧_ on lower)) ∘ < expr e , expr e₁ >
  expr (e or e₁)              = uncurry (zipWith (lift ∘₂ Bool._∨_ on lower)) ∘ < expr e , expr e₁ >
  expr [ e ]                  = (_∷ []) ∘ expr e
  expr (unbox e)              = Vec.head ∘ expr e
  expr (merge e e₁ e₂)        = uncurry (uncurry mergeVec) ∘ < < expr e , expr e₁ > , lower ∘ expr e₂ >
  expr (slice e e₁)           = uncurry sliceVec ∘ < expr e , lower ∘ expr e₁ >
  expr (cut e e₁)             = uncurry cutVec ∘ < expr e , lower ∘ expr e₁ >
  expr (cast eq e)            = castVec eq ∘ expr e
  expr (- e)                  = neg ∘ expr e
  expr (e + e₁)               = uncurry add ∘ < expr e , expr e₁ >
  expr (e * e₁)               = uncurry mul ∘ < expr e , expr e₁ >
  expr (e ^ x)                = flip pow x ∘ expr e
  expr (e >> n)               = lift ∘ flip (shift 2≉0) n ∘ lower ∘ expr e
  expr (rnd e)                = lift ∘ ⌊_⌋ ∘ lower ∘ expr e
  expr (fin {ms = ms} f e)    = lift ∘ f ∘ lowerFin ms ∘ expr e
  expr (asInt e)              = lift ∘ 𝕀⇒ℤ ∘ 𝕀.+_ ∘ Fin.toℕ ∘ lower ∘ expr e
  expr nil                    = const _
  expr (cons {ts = ts} e e₁)  = uncurry (cons′ ts) ∘ < expr e , expr e₁ >
  expr (head {ts = ts} e)     = head′ ts ∘ expr e
  expr (tail {ts = ts} e)     = tail′ ts ∘ expr e
  expr (call f es)            = fun f ∘ < proj₁ , exprs es >
  expr (if e then e₁ else e₂) = uncurry (uncurry Bool.if_then_else_) ∘ < < lower ∘ expr e , expr e₁ > , expr e₂ >

  exprs []            = const _
  exprs (e ∷ [])      = expr e
  exprs (e ∷ e₁ ∷ es) = < expr e , exprs (e₁ ∷ es) >

  ref {Σ = Σ} (state i)     = fetch i Σ ∘ proj₁
  ref {Γ = Γ} (var i)       = fetch i Γ ∘ proj₂
  ref [ r ]                 = (_∷ []) ∘ ref r
  ref (unbox r)             = Vec.head ∘ ref r
  ref (slice r e)           = uncurry sliceVec ∘ < ref r , lower ∘ expr e >
  ref (cut r e)             = uncurry cutVec ∘ < ref r , lower ∘ expr e >
  ref (cast eq r)           = castVec eq ∘ ref r
  ref (head {ts = ts} r)    = head′ ts ∘ ref r
  ref (tail {ts = ts} r)    = tail′ ts ∘ ref r

  locRef {Γ = Γ} (var i)       = fetch i Γ ∘ proj₂
  locRef [ r ]                 = (_∷ []) ∘ locRef r
  locRef (unbox r)             = Vec.head ∘ locRef r
  locRef (slice r e)           = uncurry sliceVec ∘ < locRef r , lower ∘ expr e >
  locRef (cut r e)             = uncurry cutVec ∘ < locRef r , lower ∘ expr e >
  locRef (cast eq r)           = castVec eq ∘ locRef r
  locRef (head {ts = ts} r)    = head′ ts ∘ locRef r
  locRef (tail {ts = ts} r)    = tail′ ts ∘ locRef r

  assign {Σ = Σ} (state i)     val = < updateAt i Σ val ∘ proj₁ , proj₂ >
  assign {Γ = Γ} (var i)       val = < proj₁ , updateAt i Γ val ∘ proj₂ >
  assign [ r ]                 val = assign r (Vec.head val)
  assign (unbox r)             val = assign r (val ∷ [])
  assign (slice r e)           val = uncurry (assign r) ∘ < uncurry (mergeVec val) ∘ < uncurry cutVec , proj₂ > ∘ < ref r , lower ∘ expr e > , id >
  assign (cut r e)             val = uncurry (assign r) ∘ < uncurry (flip mergeVec val) ∘ < uncurry sliceVec , proj₂ > ∘ < ref r , lower ∘ expr e > , id >
  assign (cast eq r)           val = assign r (castVec (sym eq) val)
  assign (head {ts = ts} r)    val = uncurry (assign r) ∘ < cons′ ts val ∘ ref (tail r) , id >
  assign (tail {ts = ts} r)    val = uncurry (assign r) ∘ < flip (cons′ ts) val ∘ ref (head r) , id >

  locAssign {Γ = Γ} (var i)       val = updateAt i Γ val ∘ proj₂
  locAssign [ r ]                 val = locAssign r (Vec.head val)
  locAssign (unbox r)             val = locAssign r (val ∷ [])
  locAssign (slice r e)           val = uncurry (locAssign r) ∘ < uncurry (mergeVec val) ∘ < uncurry cutVec , proj₂ > ∘ < locRef r , lower ∘ expr e > , id >
  locAssign (cut r e)             val = uncurry (locAssign r) ∘ < uncurry (flip mergeVec val) ∘ < uncurry sliceVec , proj₂ > ∘ < locRef r , lower ∘ expr e > , id >
  locAssign (cast eq r)           val = locAssign r (castVec (sym eq) val)
  locAssign (head {ts = ts} r)    val = uncurry (locAssign r) ∘ < cons′ ts val ∘ locRef (tail r) , id >
  locAssign (tail {ts = ts} r)    val = uncurry (locAssign r) ∘ < flip (cons′ ts) val ∘ locRef (head r) , id >

  stmt (s ∙ s₁)              = stmt s₁ ∘ stmt s
  stmt skip                  = id
  stmt (ref ≔ val)           = uncurry (assign ref) ∘ < expr val , id >
  stmt {Γ = Γ} (declare e s) = < proj₁ , tail′ Γ ∘ proj₂ > ∘ stmt s ∘ < proj₁ , uncurry (cons′ Γ) ∘ < expr e , proj₂ > >
  stmt (invoke p es)         = < proc p ∘ < proj₁ , exprs es > , proj₂ >
  stmt (if e then s)         = uncurry (uncurry Bool.if_then_else_) ∘ < < lower ∘ expr e , stmt s > , id >
  stmt (if e then s else s₁) = uncurry (uncurry Bool.if_then_else_) ∘ < < lower ∘ expr e , stmt s > , stmt s₁ >
  stmt {Γ = Γ} (for m s)     = Vec.foldl _ (flip λ i → (< proj₁ , tail′ Γ ∘ proj₂ > ∘ stmt s ∘ < proj₁ , cons′ Γ (lift i) ∘ proj₂ >) ∘_) id (Vec.allFin m)

  locStmt (s ∙ s₁)              = locStmt s₁ ∘ < proj₁ , locStmt s >
  locStmt skip                  = proj₂
  locStmt (ref ≔ val)           = uncurry (locAssign ref) ∘ < expr val , id >
  locStmt {Γ = Γ} (declare e s) = tail′ Γ ∘ locStmt s ∘ < proj₁ , uncurry (cons′ Γ) ∘ < expr e , proj₂ > >
  locStmt (if e then s)         = uncurry (uncurry Bool.if_then_else_) ∘ < < lower ∘ expr e , locStmt s > , proj₂ >
  locStmt (if e then s else s₁) = uncurry (uncurry Bool.if_then_else_) ∘ < < lower ∘ expr e , locStmt s > , locStmt s₁ >
  locStmt {Γ = Γ} (for m s)     = proj₂ ∘ Vec.foldl _ (flip λ i → (< proj₁ , tail′ Γ ∘ locStmt s > ∘ < proj₁ , cons′ Γ (lift i) ∘ proj₂ >) ∘_) id (Vec.allFin m)

  fun {Γ = Γ} (init e ∙ s end) = fetch zero (_ ∷ Γ) ∘ locStmt s ∘ < proj₁ , uncurry (cons′ Γ) ∘ < expr e , proj₂ > >

  proc (s ∙end) = proj₁ ∘ stmt s
