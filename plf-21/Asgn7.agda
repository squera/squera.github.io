module Asgn7 where

-- Your Name:  ............................................

-- Instructions:
-- This assignment is worth 25 points and is structured in 2 parts
-- (§1 and §2) worth 13 and 12 points.

-- The programming exercises in this assignment can be solved in more
-- than one way.  The goal is for you to practice and experiment with
-- various designs and data representations.  Therefore, this
-- assignment also contains questions that you have to answer as a
-- comment, where you explain your design decisions.  Motivate your
-- answers and give enough explanation to understand your approach.

-- To solve this assignment, you can also use functions and types from
-- these modules as well as from any other modules from the Agda
-- standard library.

open import Data.Nat
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])

module §1 where

-- Part 1: Arrays
-- 2 + 3 + 5 + 3 = 13 points

  -- The goal of this exercise is to extend a simple calculus with
  -- *mutable* arrays. This extension should not break type-safety,
  -- therefore it is your goal as language designer to specify a
  -- type- and memory-safe interface to manipulate arrays.

  -- In this language, programs cannot access arrays directly
  -- through pointers like in C. Instead programs use array "handles",
  -- which provide bounds-checked access to the heap.

  -- (2pt) Add types and well-typed constructs to manipulate arrays in
  -- a type-safe way.

  -- Extend the syntax of types with a new type constructor for array
  -- handles. The type of the handle must keep track of the type of
  -- the content of the array.
  data Ty : Set where
    unit : Ty
    nat : Ty

    -- Add the constructor for array handle type here.

  -- Extend the well-typed syntax of expressions with the
  -- following constructs to create and manipulate arrays through
  -- array handles:
  -- e := ... | new(e₁,e₂)    -- Create an array of length e₁ in the heap and return a handle to it.
                              -- The array is initialized with the value of e₂.
  --          | e₁[e₂]        -- Read the the array pointed by the array handle e₁ at index e₂
  --          | e₁[e₂] ≔ e₃   -- Write the value of e₃ in the the array pointed by e₁ at index e₂.
  --          | len(e)        -- Return the length of array pointed to by handle e.
  --
  -- Assign reasonable types to these constructs and their arguments to enforce type safety.
  data Expr : Ty → Set where

    （） : Expr unit

    #_ : ℕ → Expr nat

    -- Add your constructors for new(e₁,e₂), e₁[e₂], e₁[e₂] ≔ e₃, len(e) here.


-- There are different ways to model handles, arrays and the heap to
-- solve this exercise.  You can represent these objects as you want
-- (as long as they meet the requirements given above), but aim for
-- a simple design to make your life easier.
--
-- (3pt) Define values and heaps below and answer the questions
-- belows.  In particular, motivate your design choices and discuss
-- them in relation to the semantics of the language.

   -- How do you represent an array handle? Complete the definition
   -- below and explain your design.
  data Value : Ty → Set where
     #_ : ℕ → Value nat
     （） : Value unit
     -- Add values for array handles here.

  -- How are arrays stored in the heap?  Complete the definition below
  -- and explain your design.
  data Heap : Set where


  -- (5pt) Give a big-step semantics for this language.  Provide rules to
  -- evaluate numeric constants (e.g., # n) and unit, as well as rules
  -- for the new constructs that access arrays through array handles.
  -- Introduce helper function, predicates and types as needed.

  -- Define Your big-step semantics here:



  -- 3pt) Answer the following questions about your semantics.
  -- 1) How do the rules index and access individual array elements?
  -- 2) How do the rules enforce memory safety?
  -- 3) Are there any corner cases (e.g., arrays of size 0) that needs to be handled in a special way in the semantics?
  -- Motivate your answers.



--------------------------------------------------------------------------------

module §2 where

-- Part 2: IFC
-- 4 + 3 + 5 = 12 points

-- The goal of this exercise is to define a static IFC type system for
-- a simple simple language with natural numbers and then prove that
-- the language is secure, i.e., well-typed programs satisfy
-- non-interference.

  data Label : Set where
    L : Label
    H : Label

  data _⊑_ : Label → Label → Set where
    H⊑H : H ⊑ H
    L⊑ : ∀ {ℓ : Label} → L ⊑ ℓ

  -- Since the language has only natural numbers, we do not model
  -- simple types and use labels directly instead. In particular, the
  -- type system assigns to terms only a label, which represents its
  -- sensitivity.  This simplification will make the model a bit less
  -- general, but easier to work with for this basic language with
  -- only one type.

  -- The context keeps track of the sensitivity of the program inputs.
  Ctx : Set
  Ctx = List Label

  -- Labeld input variables, ℓ ∈ Γ, where ℓ indicates the sensitivity
  -- of a particular input.
  data _∈_ : Label → Ctx → Set where
    here : ∀ {ℓ Γ} → ℓ ∈ (ℓ ∷ Γ)
    there : ∀ {ℓ ℓ' Γ} →
              ℓ ∈ Γ →
              ℓ ∈ (ℓ' ∷ Γ)

  -- (4pt) Complete the well-typed syntax for the following language,
  -- which supports variables, natural numbers, addition, and a switch
  -- statement.  Remember that the expression constructs should be
  -- extended with appropriate security checks (i.e., flow-to
  -- constraints ℓ₁ ⊑ ℓ₂ between labels) to prevent data leaks.  Do
  -- not use concrete labels (i.e., L and H) in the
  -- constraints. Instead, let them be general so that the type system
  -- can be reused for more complicated security lattices as well.
  --
  -- Nat        n ∈ ℕ
  -- Variables  x, y, z ...
  -- Expression e  := x | n | e₁ ⊕ e₂ | switch e cs
  -- Cases      cs := { n ⇒ e } , cs
  --                | { _ ⇒ e }          (default case)
  -- Value:     v  := n
  -- Env:       θ ∈ Var → Value
  --
  --
  -- Expr Γ ℓ represents a well-typed expression e that depends on
  -- inputs at most at sensitivity ℓ.

  mutual

    data Expr (Γ : Ctx) (ℓ : Label) : Set where

      -- Add your constructors here and explain how the constraints in
      -- the rules prevent data leaks with concrete examples (i.e.,
      -- programs that would leak without the constraints).


    -- Mutually define a data type for "cases" here.

  record Value (ℓ : Label) : Set where

  data Env : Ctx → Set where
    [] : Env []
    _∷_ : ∀ {ℓ Γ} → Value ℓ → Env Γ → Env (ℓ ∷ Γ)

  -- (3pt) Define a big-step semantics for the language above.  The
  -- semantics for the switch statement is standard, i.e., "switch e
  -- cs" evaluates e to a number "n" and then evaluates the body e of
  -- the first case { n' ⇒ e } such that n = n', or the last default
  -- case { _ ⇒ e } if none matches.
  data _⇓⟨_⟩_ {Γ ℓ} : Expr Γ ℓ → Env Γ → Value ℓ → Set where


  -- Here we define a simple L-equivalence relation for values and
  -- environments of this language. In particular, v₁ ≈ v₂ indicates
  -- that values v₁ and v₂ are indisitinguishable to an attacker at
  -- security level L and similarly for θ₁ ≈ᴱ θ₂.

  data _≈_ : ∀ {ℓ} → Value ℓ → Value ℓ → Set where
    Low : ∀ {v₁ v₂ : Value L} → v₁ ≡ v₂ → v₁ ≈ v₂
    High : ∀ {v₁ v₂ : Value H} → v₁ ≈ v₂

  data _≈ᴱ_ : ∀ {Γ} → Env Γ → Env Γ → Set where
    nil : [] ≈ᴱ []
    cons : ∀ {ℓ Γ} {v₁ v₂ : Value ℓ} {θ₁ θ₂ : Env Γ} →
             v₁ ≈ v₂ →
             θ₁ ≈ᴱ θ₂ →
             (v₁ ∷ θ₁) ≈ᴱ (v₂ ∷ θ₂)

  -- Our notion of security is non-interference: well-typed programs
  -- map L-equivalent inputs to L-equivalent outputs.
  NI : ∀ {Γ ℓ} → Expr Γ ℓ → Set
  NI e = ∀ {θ₁ θ₂ v₁ v₂} → θ₁ ≈ᴱ θ₂ →
                           e ⇓⟨ θ₁ ⟩ v₁ →
                           e ⇓⟨ θ₂ ⟩ v₂ →
                           v₁ ≈ v₂

  -- (5pt) Prove that well-typed programs satisfy non-interference.
  -- State, comment and prove helper lemmas as needed.
  ni : ∀ {Γ ℓ} (e : Expr Γ ℓ) → NI e
  ni e = {!!}
