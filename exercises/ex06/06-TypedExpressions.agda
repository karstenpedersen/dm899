-- Lecture 6: Typed Expressions
module 06-TypedExpressions where

-- Chapter 8 of the book

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.Empty

data Type : Set where
  tyBool : Type
  tyNat : Type

data Expr : Set where
  z : Expr
  tt : Expr
  ff : Expr
  iszero : Expr → Expr
  succ : Expr → Expr
  pred : Expr → Expr
  -- Please add the missing constructor if
  if : Expr → Expr → Expr → Expr

-- Common names (see "Generalization of Declared Variables",
-- https://agda.readthedocs.io/en/stable/language/generalization-of-declared-variables.html)
private
  variable
    t t₁ t₂ t₃ : Expr
    τ τ₁ τ₂ : Type

data Nval : Expr → Set where
  zIsNval : Nval z
  succNval : Nval t → Nval (succ t)

data Val : Expr → Set where
  ttVal : Val tt
  ffVal : Val ff
  nval : Nval t → Val t


-- Typing Relation
data _∈_ : Expr → Type → Set where -- input: \in
  t-z : z ∈ tyNat
  t-tt : tt ∈ tyBool
  t-ff : ff ∈ tyBool
  t-iszero : t ∈ tyNat → iszero t ∈ tyBool
  -- Please add the missing constructors t-succ, t-pred, and t-if
  t-succ : t ∈ tyNat → succ t ∈ tyNat
  t-pred : t ∈ tyNat → pred t ∈ tyNat
  t-if : t ∈ tyBool → t₁ ∈ τ → t₂ ∈ τ → if t t₁ t₂ ∈ τ


-- Operational Semantics of Expressions
data _↦_ : Expr → Expr → Set where -- input: \mapsto or \r-|
  e-IsZeroZ : iszero z ↦ tt
  e-IsZeroS : Nval t → iszero (succ t) ↦ ff
  e-IsZ : t₁ ↦ t₂ → iszero t₁ ↦ iszero t₂
  -- Please add the missing constructors e-Succ, e-Pred, e-PredZ, e-predS,
  -- e-ifT, e-IfF, and e-If
  e-Succ : t₁ ↦ t₂ → succ t₁ ↦ t₂
  e-Pred : t₁ ↦ t₂ → pred t₁ ↦ t₂
  e-PredZ : pred z ↦ z
  e-PredS : Nval t → pred (succ t) ↦ t 
  e-IfT : if tt t₁ t₂ ↦ t₁
  e-IfF : if ff t₁ t₂ ↦ t₂
  e-If : t ↦ t₁ → if t t₂ t₃ ↦ if t₁ t₂ t₃


-- Short exercises
bad₁ : pred ff ↦ t₁ → ⊥
bad₁ (e-Pred ())

val₁ : Val (succ (succ z))
val₁ = nval (succNval (succNval zIsNval))


-- Theorem
-- Uniqueness of Types
∈-Uniq : t ∈ τ₁ → t ∈ τ₂ → τ₁ ≡ τ₂
∈-Uniq t-z t-z = refl
∈-Uniq t-tt t-tt = refl
∈-Uniq t-ff t-ff = refl
∈-Uniq (t-iszero h) (t-iszero k) = refl
∈-Uniq (t-succ h) (t-succ k) = refl
∈-Uniq (t-pred h) (t-pred k) = refl
∈-Uniq (t-if h h₁ h₂) (t-if k k₁ k₂) = ∈-Uniq h₁ k₁

-- Theorem
-- Progress
progress : t ∈ τ → Val(t) ⊎ Σ Expr (t ↦_) -- input: \Sigma
progress t-z = inj₁ (nval zIsNval)
progress t-tt = inj₁ ttVal
progress t-ff = inj₁ ffVal
progress (t-iszero {t'} h) with progress h
... | inj₁ (nval zIsNval) = inj₂ (tt , e-IsZeroZ)
... | inj₁ (nval (succNval x)) = inj₂ (ff , (e-IsZeroS x))
... | inj₂ (t'' , k) = inj₂ (iszero t'' , e-IsZ k)
progress (t-succ {t'} h) with progress h
... | inj₁ (nval zIsNval) = inj₁ (nval (succNval zIsNval))
... | inj₁ (nval (succNval x)) = inj₁ (nval (succNval (succNval x)))
... | inj₂ (t'' , k) = inj₂ (t'' , e-Succ k)
progress (t-pred {t'} h) with progress h
... | inj₁ (nval zIsNval) = inj₂ (z , e-PredZ)
... | inj₁ (nval (succNval x)) = {!!}
... | inj₂ (t'' , k) = inj₂ (t'' , e-Pred k)
progress (t-if {t'} h h₁ h₂) with progress h
... | inj₁ ttVal = inj₂ ({!!} ,  e-IfT)
... | inj₁ ffVal = {!!}
... | inj₁ (nval x) = {!!}
... | inj₂ y = {!!}

-- Theorem
-- Preservation
preservation : t ∈ τ → t ↦ t₁ → t₁ ∈ τ
preservation (t-iszero h) e-IsZeroZ = t-tt
preservation (t-iszero h) (e-IsZeroS x) = t-ff
preservation (t-iszero h) (e-IsZ k) = t-iszero (preservation h k) 
preservation (t-succ h) (e-Succ k) = preservation h k
preservation (t-pred h) (e-Pred k) = preservation h k
preservation (t-pred h) e-PredZ = h
preservation (t-pred (t-succ h)) (e-PredS x) = h
preservation (t-if h h₁ h₂) e-IfT = h₁
preservation (t-if h h₁ h₂) e-IfF = h₂
preservation (t-if h h₁ h₂) (e-If k) = t-if (preservation h k) h₁ h₂
