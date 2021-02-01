module Ass1 where

open import Relation.Binary.PropositionalEquality

-- Instructions:

-- This assignment is worth 25 points and is structured in 3 three
-- parts worth 6, 9, and 10 points, respectively.  Each part is
-- structured in small exericses that you have to solve to score
-- points.  Concise solutions are worth more points than longer
-- solutions and you will also score points for incomplete solutions.

-- You are not allowed to change the type signatures of the exercises,
-- but you can define additional types, functions, and lemmas as you see
-- fit.  Previous exercises may help you to solve later exercises and
-- you can reuse them even if you did not manage to solve them.

--------------------------------------------------------------------------------
-- Part 1 (6 pts)
-- Reasoning about natural numbers.
--------------------------------------------------------------------------------
-- Basic definitions.

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

one : ℕ
one = suc zero

two : ℕ
two = suc (suc zero)

-- x ≤ y iff x is less than or equal to y
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s  : ∀ {x y} → x ≤ y → (suc x) ≤ (suc y)

--------------------------------------------------------------------------------
-- Exercises:

-- 1pt) Compute the maximum between two natural numbers.
max : ℕ → ℕ → ℕ
max = {!!}

-- 2pt) Show that max x y is equal to max y x
sym-max : ∀ (x y : ℕ) → max x y ≡ max y x
sym-max = {!!}

-- 2pt) Show that x ≤ max x y for any number y
≤-max₁ : ∀ (x y : ℕ) → x ≤ max x y
≤-max₁ = {!!}

-- 1pt) Show that x ≤ max y x for any number y
≤-max₂ : ∀ x y → x ≤ max y x
≤-max₂ = {!!}

--------------------------------------------------------------------------------
-- Part 2 (9 pts).
-- The goal of this part is to convert ULC expressions with arbitrary
-- DeBrujin indexes to equivalent expressions in the well-scoped syntax.
--------------------------------------------------------------------------------
-- Basic definitions

-- A syntax for ULC with arbitrary DeBrujin indexes.
data Expr : Set where
 var : ℕ → Expr
 λ′ : Expr → Expr
 _∘_ : Expr → Expr → Expr

-- Identity function with De Brujin indexes.
id : Expr
id = λ′ (var zero)

-- A term (x : Fin n) represents a number strictly smaller than n,
-- i.e., a number x ∈ {0, ... , n - 1}.
data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc : ∀ {n} → Fin n → Fin (suc n)

-- A well-scoped syntax for ULC.
-- A term of type WSExpr n can contain only free variables up to n - 1,
-- i.e., FV(e) ⊆ {0, ... , n - 1}.
data WSExpr (n : ℕ) : Set where
  var : Fin n → WSExpr n
  λ′ : WSExpr (suc n) → WSExpr n
  _∘_ : WSExpr n → WSExpr n → WSExpr n

infixr 6 _∘_

-- Identity function with well-scoped syntax.
id' : WSExpr zero
id' = λ′ (var zero)

-- Weakening for well-scoped variables.
-- If x ∈ {0, ..., n - 1}, then x ∈ {0, ..., m - 1}, for any m such that n ≤ m.
wken-fin : ∀ {n m} → Fin n → n ≤ m → Fin m
wken-fin zero (s≤s p) = zero
wken-fin (suc x) (s≤s p) = suc (wken-fin x p)

-- Weakening increases the number of free variables in the
-- type of a well-scoped term.
wken : ∀ {n m} → WSExpr n → n ≤ m → WSExpr m
wken (var x) p = var (wken-fin x p)
wken (λ′ e) p = λ′ (wken e (s≤s p))
wken (e₁ ∘ e₂) p = wken e₁ p ∘ wken e₂ p

-- For example, we can weaken the identitiy function so that it can be
-- combined with WSExpr expressions that have 1 free variable.
id'' : WSExpr one
id'' = wken id' z≤n

--------------------------------------------------------------------------------
-- Exercises:

-- Since Expr and WSExpr have exactly the same constructors, the
-- translation from Expr to WSExpr is trivial. The main challenge is
-- to account for the unrestricted free variables from Expr terms in the
-- well-scoped syntax of WSExpr. In particular, in order to translate
-- an expression (e : Expr), we have to compute the number (x : ℕ) of
-- free variables of e, such that the translation can be typed WSExpr
-- x.

-- 1pt) First, we need to convert DeBrujin variables (e.g., n : ℕ)
-- into the corresponding well-scoped variables (e.g., x : Fin y), for
-- a sufficiently large number y so that n and x can have the same
-- number of "suc" constructors.  Complete the type signature below
-- and convert a DeBrujin variable into the corresponding well-scoped
-- variable of type Fin y.
--
-- Hint: What is the minimum number y such that n < y?
fromℕ : (n : ℕ) → Fin {!!}
fromℕ = {!!}

-- 2pt) The constructor _∘_ in WSExpr takes two expressions that have
-- exactly the same number of free variables.  Here you have to define
-- a smart constructor for function application where the function and
-- the argument may have a different number of free variables.  This
-- requires computing an upper bound over the number of free variables
-- of both expressions, which is sufficiently large to accomodate the
-- free variables of both. Then, we can weaken these expressions to
-- this common bound and apply constructor _∘_.
--
-- Hint:
-- e₁ has free variables {0, ..., x - 1}
-- e₂ has free variables {0, ..., y - 1}
-- What is the minimum number z, such that "e₁ e₂" has free variables
-- {0, ..., z - 1}?
--
-- Complete the type signature below and define the smart constructor
-- "app e₁ e₂", which returns the function application of e₁ to e₂,
-- where e₁ and e₂ have been weakened appropriately to have type
-- "WSExpr z".
app : ∀ {n m} → WSExpr n → WSExpr m → WSExpr {!!}
app = {!!}

-- 3pt) Constructor λ′ in WSExpr takes only expressions that have at
-- least one free variable, as indicated by the parameter "suc n" of the body.
-- Here, you have to define the smart constructor "lam e", which creates
-- a λ-expression regardless of whether "e" contains free variables or
-- not, i.e., for any expression (e : Expr n) and for any n.
-- Like before, you first have to compute how many free variables
-- remain in the result and then apply weakening to the body
-- of the function so that you can use the λ′ constructor.
--
-- Hints:
-- e has free variables {0, ..., n - 1}
-- How many variables remain free in λ′ e?
--
-- Complete the type signature below and define the smart constructor
-- "lam e", which return "λ′ e", where e has been appropriately
-- weakened.
lam : ∀ {n} → WSExpr n → WSExpr {!!}
lam = {!!}


-- 2 pt) In order to convert an expression to the well scoped syntax,
-- we first need to compute how many free variables it
-- contains. Function # e computes the *minimum* number n of free
-- variables, such that e can be converted into a corresponding
-- well-scoped expression of type WSExpr n.
--
-- # e = n iff n is the minimum number such that e contains free variables
-- up to n - 1, i.e., such that ∀ x ∈ FV(e), x ∈ {0, ..., n - 1}.
#_ : Expr → ℕ
#_ = {!!}

-- Examples.  Fill in these holes with "refl" to check that your
-- solution handles these cases correctly.

-- Expression "0" has free variable 0, therefore we need at
-- least "one" free variable to convert it, because 1 is the minimum
-- number such that 0 ∈ {0} = {0, ... , 1 - 1}.
_ : # (var zero) ≡ one
_ = {!!}

-- Expression "id" does not have any free variable, therefore "# id"
-- returns "0".
_ : # id ≡ zero
_ = {!!}

-- Expresion "0 1" has free variables 0 and 1, therefore we need at
-- least "two" free variables to convert it because 2 is the minimum
-- number such that:
-- 0 ∈ {0, 1} = {0, ..., 2 - 1}, and
-- 1 ∈ {0, 1} = {0, ..., 2 - 1}.
_ : # (var zero ∘ (var (suc zero))) ≡ two
_ = {!!}

-- 1 pt) Convert an expression with DeBrujin indexes into an
-- equivalent well-scoped expression with at most "# e" free
-- variables.
--
-- Hint: use the "smart constructors" that you defined before.
toWS : (e : Expr) → WSExpr (# e)
toWS = {!!}

--------------------------------------------------------------------------------
-- Part 3
-- PL & Semantics (10 points)
--------------------------------------------------------------------------------

-- 2 pt) Formalize the following syntax for arithmetic and boolean expressions
-- Bool   b := true | false
-- Nat    n := 0 | 1 | 2 | ...
-- ABExpr e := n | b | e₁ + e₂ | e ≤? e
-- as the Agda data-type ABExpr:
data ABExpr : Set where
  -- Your constructors here

-- 4 pt) Define a big-step semantics for this language.
-- Define helper types, functions, or predicates as needed.
data _⇓_ : ABExpr → ABExpr → Set where
  -- Your constructors here


infixr 3 _⇓_

-- 4 pt)
-- Show that the semantics that you gave is deterministic:
-- an expression can evaluate to at most one expression.
-- Formally, if e ⇓ e₁ and e ⇓ e₂, then e₁ ≡ e₂.
det : ∀ {e e₁ e₂} →
        e ⇓ e₁ →
        e ⇓ e₂ →
        e₁ ≡ e₂
det = {!!}
