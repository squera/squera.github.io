module Asgn5 where

-- Your Name:  ............................................

-- Instructions:
-- This assignment is worth 25 points and is structured in two parts
-- (§1 and §2) worth 11 and 14 points.  Each part is structured in
-- small exericses that you have to solve to score points. Try to keep
-- your solutions short and simple. You can score points also for
-- incomplete or partial solutions. You are not allowed to change the
-- type signatures of the exercises, but you can define additional
-- types, functions, and lemmas as you see fit.

--------------------------------------------------------------------------------
-- Definitions and modules common to both parts.

-- To solve this assignment you can types, functions, and lemmas from these modules.

open import Data.List
open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.String
open import Data.Sum


-- x ∈ xs is the proof that x occurs in the list xs.
data _∈_ {A : Set} : A → List A → Set where

  here : ∀ {τ Γ} → τ ∈ (τ ∷ Γ)

  there : ∀ {τ τ' Γ} →
            τ ∈ Γ →
            τ ∈ (τ' ∷ Γ)

--------------------------------------------------------------------------------

module §1 where  -- (11 pts)

  -- The goal of this part is to define an explicit type system for
  -- untyped, but well-scoped, ULC terms, and a simple type inference
  -- algorithm.

  -- This part is worth 11 points and contains 6 questions:
  -- Type system: 1 + 3 + 1 = 5 points
  -- Type inference: 1 + 1 + 4 = 6 points

  --------------------------------------------------------------------------------
  -- Basic definitions.

  -- Unit and function types.
  data Ty : Set where
    unit : Ty
    _⇒_ : Ty → Ty → Ty

  -- The typing context is just a list of types.
  Ctx : Set
  Ctx = List Ty

  -- Well-scoped ULC syntax.
  -- A term of type UExpr n contains free variables {0, ..., n - 1}.
  data UExpr (n : ℕ) : Set where

    （） : UExpr n

    var : Fin n → UExpr n

    -- The type annotation below indicates the expected type of the
    -- argument of the function, i.e., a function "λ⟨ unit ⟩ e"
    -- accepts only arguments of type "unit".  Your type system and
    -- type inference algorithm must use the type annotation to type
    -- the function.
    λ⟨_⟩ : Ty → UExpr (suc n) → UExpr n

    _∘_ : UExpr n → UExpr n → UExpr n

--------------------------------------------------------------------------------

  -- 1pt) UExpr uses well-scoped DeBrujin indices for variables.
  -- Therefore, to type variables in the type system we have to
  -- explicitly look up their type in the typing context.
  --
  -- Complete the type signature below so that the variable is
  -- guaranteed to be typable in the given context Γ.
  _!!_ : (Γ : Ctx) → Fin {!!} → Ty
  _!!_ = {!!}

  -- 3pt) Define the judgment Γ ⊢ e ∈ τ, which indicates that e has
  -- type τ under typing context Γ.  Make sure to include all the
  -- typing rules needed to type the constructs of UExpr and to honor
  -- the type annotation for lambas.

  data _⊢_∈_ (Γ : Ctx) : UExpr {!!} → Ty → Set where
    -- Your constructors here...

  -- 1 pt) As a sanity check, prove that at most one single type can
  -- be assigned to an expression.
  unique-typing : ∀ {Γ τ₁ τ₂ e} → Γ ⊢ e ∈ τ₁ → Γ ⊢ e ∈ τ₂ → τ₁ ≡ τ₂
  unique-typing x y = {!!}

  --------------------------------------------------------------------------------
  -- The type inference procedure considered in this exercise is
  -- intentionally simple and syntax-driven.  In particular, we
  -- reconstruct the type of terms directly from their syntax, and
  -- rely on type annotations to type lambdas.  If the term is
  -- ill-typed, type inference fails explcitly and returns an
  -- appropriate type error message as a string.

  -- 1 pt) τ₁ ≟ᵀ τ₂ compares the expected type τ₁ and reconstructed
  -- type τ₂ and returns an error message if they do not match.
  _≟ᵀ_ : (τ τ' : Ty) → (τ ≡ τ') ⊎ String
  τ₁ ≟ᵀ τ₂ = {!!}

  -- A ULC term is well-typed under a type environment Γ iff *there exists* a type τ such that Γ ⊢ e : τ.
  -- 1pt) Define the predicate "IsWT Γ e", which indicates that e is well-typed.
  IsWT : (Γ : Ctx) (e : UExpr {!!}) → Set
  IsWT Γ e = {!!}

  -- 4 pt) Determine if e is well-typed or not by infering its type
  -- under Γ.  If e is ill-typed return an appropriate error message.
  ty-infer : ∀ Γ e → IsWT Γ e ⊎ String
  ty-infer Γ x = {!!}

module §2 where

-- This part is worth 14 points and contains 6 exercises.
-- Well-Typed Syntax: 3 + 1 + 3 = 7 points
-- Logical Relations: 1 + 4 + 2 = 7 points

  open import Data.Unit

  -- The goal of this exercise is to extend STLC with sum types
  -- and complete the fundamental property of the logical relations
  -- for the new cases.

  data Ty : Set where
    unit : Ty
    _⇒_ : Ty → Ty → Ty
    _⊕_ : Ty → Ty → Ty  -- New type constructor for sum types

  infixr 7 _⇒_

  Ctx : Set
  Ctx = List Ty

  -- 3pt) Extend the well-typed syntax of expressions with left and right
  -- injections and case.
  -- e ≔ （） | x | λx.e | e e
  --   | inl e | inr e | case e x.e₁ x.e₂
  data Expr (Γ : Ctx) : (τ : Ty) → Set where

    （） : Expr Γ unit

    var : ∀ {τ} → τ ∈ Γ → Expr Γ τ

    λ′ : ∀ {τ τ'} →
        Expr (τ' ∷ Γ) τ →
        Expr Γ (τ' ⇒ τ)

    _∘_ : ∀ {τ τ'} →
          Expr Γ (τ' ⇒ τ) →
          Expr Γ τ' →
          Expr Γ τ

    -- Write your constructors for "inl e", "inr e", and "case e x.e₁ x.e₂" here.


  mutual

    -- 1pt) Extend the syntax of values with values for the left and right injection.
    -- v ≔ （） | ⟨ x.e , θ ⟩ | inl v | inr v
    data Value : Ty → Set where

      （） : Value unit

      ⟨_,_⟩ : ∀ {Γ τ τ'} → Expr (τ ∷ Γ) τ' → Env Γ → Value (τ ⇒ τ')

      -- Write your constructors for inl v and inr v here.

    data Env : Ctx → Set where
      [] : Env []
      _∷_ : ∀ {τ Γ} → Value τ → Env Γ → Env (τ ∷ Γ)

  -- Lookup in environment
  _!!_ : ∀ {τ Γ} → Env Γ → τ ∈ Γ → Value τ
  (v ∷ θ) !! here = v
  (v ∷ θ) !! there x = θ !! x

  -- 3pt) Complete the big-step semantics with the rules for inl, inr, and case.
  data _⇓⟨_⟩_ {Γ} : ∀ {τ} → Expr Γ τ → Env Γ → Value τ → Set where

    Unit : ∀ {θ} → （） ⇓⟨ θ ⟩ （）

    Var : ∀ {θ τ} → (τ∈Γ : τ ∈ Γ) → var τ∈Γ ⇓⟨ θ ⟩ (θ !! τ∈Γ)

    Abs : ∀ {τ' τ θ} {e : Expr (τ' ∷ Γ) τ} →
            λ′ e ⇓⟨ θ ⟩ ⟨ e , θ ⟩

    App : ∀ {θ τ τ' Γ' θ'} {e₁ : Expr Γ (τ ⇒ τ')} {e₂ : Expr Γ τ} →
            {e' : Expr (τ ∷ Γ') τ'} {v : Value τ} {v' : Value τ'} →
            e₁ ⇓⟨ θ ⟩ ⟨ e' , θ' ⟩ →
            e₂ ⇓⟨ θ ⟩ v →
            e' ⇓⟨ v ∷ θ' ⟩ v' →
            (e₁ ∘ e₂) ⇓⟨ θ ⟩ v'

    -- Write the constructors for the rules for inl, inr, and case, here

  --------------------------------------------------------------------------------
  -- Logical Relations

  mutual

    -- 1pt) Complete the logical predicates for values with the missing cases for inl and inr.
    𝑽⟦_⟧ : ∀ {τ} → Value τ → Set
    𝑽⟦ （） ⟧ = ⊤
    𝑽⟦ ⟨ e , θ ⟩ ⟧ = ∀ {v} → 𝑽⟦ v ⟧ → 𝑬⟦ e ⟧ (v ∷ θ)
    -- Missing cases here.

    𝑬⟦_⟧ : ∀ {Γ τ} → Expr Γ τ → Env Γ → Set
    𝑬⟦ e ⟧ θ = ∃ (λ v → e ⇓⟨ θ ⟩ v × 𝑽⟦ v ⟧)

    𝑮⟦_⟧ : ∀ {Γ} → Env Γ → Set
    𝑮⟦ [] ⟧ = ⊤
    𝑮⟦ v ∷ θ ⟧ = 𝑽⟦ v ⟧ × 𝑮⟦ θ ⟧

  -- Judgment for semantic typing.
  _⊨_ : ∀ {τ} (Γ : Ctx) → Expr Γ τ → Set
  Γ ⊨ e  = (θ : Env Γ) → 𝑮⟦ θ ⟧ → 𝑬⟦ e ⟧ θ

  -- Compatibility lemmas (one for each contruct of the calculus)
  -- These lemmas help us structure the proof and avoid ill-founded
  -- induction.

  lookup𝑽⟦_⟧ : ∀ {Γ τ} → (x : τ ∈ Γ) (θ : Env Γ) → 𝑮⟦ θ ⟧ → 𝑽⟦ θ !! x ⟧
  lookup𝑽⟦ here ⟧ (v ∷ θ) (𝑽 , _) = 𝑽
  lookup𝑽⟦ there x ⟧ (_ ∷ θ) (_ , γ) = lookup𝑽⟦ x ⟧ θ γ

  lam-comp : ∀ {τ τ' Γ} (e : Expr (τ' ∷ Γ) τ) → (τ' ∷ Γ) ⊨ e → Γ ⊨ λ′ e
  lam-comp e 𝑬 θ γ = ⟨ e , θ ⟩ , Abs , (λ {v} 𝑽 → 𝑬 (v ∷ θ) (𝑽 , γ))

  var-comp : ∀ {τ Γ} → (x : τ ∈ Γ) → Γ ⊨ var x
  var-comp x θ γ = θ !! x , Var x , lookup𝑽⟦ x ⟧ θ γ

  app-comp : ∀ {τ τ' Γ} {e₁ : Expr Γ (τ' ⇒ τ)} {e₂ : Expr Γ τ'} →
               Γ ⊨ e₁ → Γ ⊨ e₂ → Γ ⊨ (e₁ ∘ e₂)
  app-comp 𝑬₁ 𝑬₂ θ γ with 𝑬₁ θ γ | 𝑬₂ θ γ
  ... | ⟨ e , θ' ⟩ , bs₁ , 𝑽₁ | v₂ , bs₂ , 𝑽₂ with 𝑽₁ 𝑽₂
  ... | v , 𝑽 , bs = v , App bs₁ bs₂ 𝑽 , bs

  -- 4pt) State and prove the compatibility lemmas for constructs inl, inr, and case

  inl-comp :  {!!}
  inl-comp = {!!}

  inr-comp : {!!}
  inr-comp = {!!}

  case-comp : {!!}
  case-comp = {!!}

  -- 2pt) Complete the missing cases of the fundamental property of
  -- the logical relations.

  -- Syntctically well-typed programs are also semantically well-typed
  semantic-soundness : ∀ {Γ τ} (e : Expr Γ τ) → Γ ⊨ e
  semantic-soundness （） θ γ = （） , Unit , tt
  semantic-soundness (var x) θ γ = var-comp x θ γ
  semantic-soundness (e₁ ∘ e₂) θ γ = app-comp (semantic-soundness e₁) (semantic-soundness e₂) θ γ
  semantic-soundness (λ′ e) θ γ = lam-comp e (semantic-soundness e) θ γ
  -- Missing cases here!
