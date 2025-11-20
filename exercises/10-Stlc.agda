-- Chapter 9: Simply Typed Lambda-Calculus
module 10-Stlc where

open import Agda.Builtin.Nat
open import Data.Vec
open import Data.Fin

data Ty : Set where
  Bool : Ty
  _⇀_ : Ty → Ty → Ty -- input: \rightharpoonup (or \r and 0 in Emacs)

-- Context n specifies that the allowed free variables are 0, ..., n - 1.
Context : Set
Context = Nat

-- An element x : Variable n is a natural number m such that m < n.
Variable : Context → Set
Variable = Fin -- have a look at the definition of Fin!

TyContext : Context → Set
TyContext n = Vec Ty n

data Term (n : Context) : Set where
  var : Variable n → Term n
  lam : Ty → Term (suc n) → Term n
  app : Term n → Term n → Term n
  true : Term n
  false : Term n
  if-then-else : Ty → Term n → Term n
  -- Please add true, false, and if-then-else

data Val {n : Context} : Term n → Set where
  lamV : ∀ {t : Term (suc n)} {τ} → Val (lam τ t)
  -- Please complete appropriately

-- Weakening of a variable.
-- Any var x = m < n is also a variable for (suc n), as m < suc n. Try inputting
-- "inject₁" in the hole to check its type.
shiftVar : ∀ {n} → Variable n → Variable (suc n)
shiftVar = inject₁

-- Shifting or (untyped) weakening of a term. Input: \u-
-- Please add true, false, and if-then-else
↑ : ∀ {n} → Term n → Term (suc n)
↑ (var x) = var (shiftVar x)
↑ (lam τ p) = lam τ (↑ p)
↑ (app t s) = app (↑ t) (↑ s)

-- Simultaneous substitutions.
-- A substitution Sub n m is an m-long vector of T n. The term at index i is
-- meant to replace the i-th variable in the context of length n.
Sub : Context → Context → Set
Sub n m = Vec (Term n) m -- have a look at the definition of Vec!

-- Shifting of a substitution
-- Try inputting "map" in the hole to check its type.
S↑ : ∀ {n} {m} → Sub n m → Sub (suc n) m
S↑ = map ↑

-- The 'identity' substitution is the sequence
-- var zero, var 1, var 2, var 3...
idSub : ∀ {n} → Sub n n
idSub {zero} = []
idSub {suc n} = var zero ∷ map ↑ idSub

-- Simultaneous substitution evaluation.
-- Try inputting "lookup" in the hole to check its type.
-- Please add true, false, and if-then-else
_<_> : ∀ {n} {m} → Term n → Sub m n → Term m
var x < sub > = lookup sub x
lam τ t < sub > = lam τ (t < var zero ∷ S↑ sub >)
app t s < sub > = app (t < sub >) (s < sub >)

-- Single-variable substitution
-- Given a term t : Term (n + 1) and a term s : T n, produce a new term t ∣ s ∣
-- by substituting any occurrences of zero in t with s
_∣_∣ : ∀ {n} → Term (suc n) → Term n → Term n
t ∣ s ∣ = t < s ∷ idSub >

-- The typing relation
-- input: \|- and \::
-- Please add true, false, and if-then-else
data _⊢_∷_ {n : Context} (Γ : TyContext n) : Term n → Ty →  Set where
  app : ∀ {t s : Term n} {τ₁} {τ₂}
    → Γ ⊢ t ∷ (τ₁ ⇀ τ₂) → Γ ⊢ s ∷ τ₁ → Γ ⊢ (app t s) ∷ τ₂
  var : ∀ {x : Variable n} → Γ ⊢ var x ∷ lookup Γ x
  lam :  ∀ {t : Term (suc n)} {τ₁} {τ₂}
    → (τ₁ ∷ Γ) ⊢ t ∷ τ₂ → Γ ⊢ lam τ₁ t ∷ (τ₁ ⇀ τ₂)

-- Call-by-value reduction
-- Please complete appropriately
data _↦_ {n : Context} : Term n → Term n → Set where
  app₁ : ∀ {t₁ t₂ s} → t₁ ↦ t₂ → app t₁ s ↦ app t₂ s
  app₂ : ∀ {s t₁ t₂} → Val s → t₁ ↦ t₂ → app s t₁ ↦ app s t₂
  β : ∀ {τ} {t s} → app (lam τ t) s ↦ (t ∣ s ∣)

-- Reflexive-transitive closure
data _⟾_ {n : Context} : Term n → Term n → Set where
  rfl : ∀ {t} → t ⟾ t
  trns : ∀ {t s₁ s₂} → t ⟾ s₁ → s₁ ↦ s₂ → t ⟾ s₂

-- Bonus exercise: let's add natural numbers
-- ℕ : Ty -- input: \bN
