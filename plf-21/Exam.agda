module Exam where

-- Your Name:  ............................................

-- Instructions:

-- This exam is worth 75 points and is structured in two parts (§1 and
-- §2) worth 40 and 35 points.
--
-- To solve the exercises contained in this exam, you can use types
-- and definitions from these modules or any other module from the
-- Agda standard library.

-- Good luck!

open import Data.Nat
open import Data.Char
open import Data.List
open import Relation.Binary.PropositionalEquality

module §1 where

  -- §1) Typed assembly language for a simple stack machine
  -------------------------------------------------------------
  -- 1. Well-Typed Syntax:            10 +
  -- 2. Type-Preserving Semantics:    10 +
  -- 3. Progress & Termination:       10 +
  -- 4. Typed Registers:              10 =
  -------------------------------------------------------------
  -- *  Total:                        40 pt

  -- The goal of this exercise is to formalize a *typed* assembly
  -- language for a simple stack machine and prove some basic formal
  -- properties of the language.

  -- The stack machine consists of a list of instructions and a stack of
  -- values, and provide two built-in data types: natural numbers and
  -- chars.

  -- Types τ := Char | Nat
  -- Char  c := 'a' | 'b' | 'c' | ...
  -- Nat   n := 0 | 1 | 2 | 3 | ...
  -- Value v := n | c

  -- The machine instructions pop their operands from the stack and
  -- push their results on the stack, so that they can be used as
  -- operands by the following instructions.
  --
  -- Instr i := push v   -- Push value v on the stack
  --          | pop      -- Pop the value from the top of the stack
  --          | add      -- Pop two numbers from the stack and push their sum on the stack
  --          | nop      -- No operation: leave the stack unchanged
  --          | jz is    -- Jump to and execute instructions "is" if the top of the stack is 0.
  --          | cmp      -- Pop two char c₁ and c₂ from the top of the stack, push 0 if c₁ = c₂, or 1 otherwise.
  --
  -- Instructions is := i : is | []

  -- The stack consists of typed values:

  -- Stack S := []       -- The empty stack
  --          | v : S    -- Value v of some type τ is on top of the stack.

  -- The machine state is represented by the program code (a list of
  -- instructions) and the value stack.

  -- Configuration c := ⟨ is , S ⟩

  --------------------------------------------------------------------------------
  -- 1. Well-Typed Syntax (10pt)

  -- Define type-indexed data types to model the syntax of
  -- well-typed instructions, values, stack, and configurations.
  -- Intuitively, your syntax should rule out by construction
  -- configurations where the instructions and the value stack are not
  -- compatible, i.e., the stack contains the wrong number of operands,
  -- or operands of the wrong type.

  -- For example, with your syntax, it should be impossible to construct
  -- the following ill-typed configurations:
  -- ⟨ pop : [] , [] ⟩           -- The stack is empty: no value to pop
  -- ⟨ add : [] , 0 : [] ⟩       -- Only one operand on the stack
  -- ⟨ add : [] , 0 : 'a' : [] ⟩ -- The second operand has the wrong type

  -- Explain how your data-types guarantee that configurations are
  -- well-typed.

  --------------------------------------------------------------------------------
  -- 2. Type-Preserving Semantics (10pt)

  -- Define a *type-preserving* small-step semantics c ⟶ c' for stack
  -- machine configurations. Add one rule for each instruction, which
  -- specifies the behavior described informally above.  Then, define
  -- the classic reflexive transitive closure c ⟶⋆ c' consisting of 0
  -- or multiple small steps. Finally, define a big-step semantics c ⇓
  -- c', which reduces a configuration c into a *final* configuration c'
  -- in 0 or multiple steps. A configuration is final if the list of
  -- instructions is empty.



  --------------------------------------------------------------------------------
  -- 3. Progress & Termination (10pt)

  -- The well-typed stack machine that you just formalized enjoys some
  -- nice properties: (1) it never gets stuck and (2) it always
  -- terminates. The goal of this exercise is to formally establish
  -- these properties.

  -- 1) State and prove "progress" for your typed stack machine
  -- semantics: any stack machine configuration can either make one more
  -- small step or the configuration is final and the program has terminated.


  -- 2) State and prove "termination": all well-typed stack machines eventually
  -- terminate, i.e., they big-step to some final configuration.
  --
  -- Hint: The proof of this property is much simpler than the
  -- corresponding proof for STLC, because the language of this machine
  -- is very restricted (no recursion, loops or functions), therefore
  -- strong reasoning principles (e.g., logical relations) are not
  -- needed.

  --------------------------------------------------------------------------------
  -- 4. Typed Registers (10pt)

  -- Extend the stack machine with n typed registers.
  --
  -- Register Map:   R := {v₁ : τ₁, ... vₙ : τₙ}.
  -- Configuration:  c := ⟨ R , is , S ⟩
  --
  -- Each register stores a value of a given type (e.g., v₁ : τ₁ for
  -- register 1 above). These values can be read and pushed on the stack
  -- or replaced with another value through new instructions:
  --
  -- Instr i := get n    -- Reads the value of register n and pushes it on the stack
  --          | set n    -- Pops a value from the stack and writes it to register n.
  --
  -- Add constructors to model these new instructions of the language.
  -- Adapt the well-typed syntax so that it statically rejects (1)
  -- programs that read or write from registers not present in the
  -- register map, and (2) programs that write values of the wrong
  -- type in a typed register.  Notice that your language must be
  -- parametric in the concrete number and the type of registers,
  -- which do not change during the execution.

  -- Similarly, add a register map to stack machine configuration, adapt
  -- the small-step semantics given in the previous exercise, and add
  -- new rules for instructions "get n" and "set n". As you add new
  -- rules to the semantics your proofs will become incomplete and may
  -- break (do not worry, Agda will tell you!). Add the missing cases
  -- and repair those broken proofs.

  -- End of Part §1.
  --------------------------------------------------------------------------------

module §2 where

  -- §2) IFC type system for a language with algebraic data types and arrays.
  ---------------------------------------------------------------------------
  -- 1. Well-Typed Syntax & Semantics:            10 +
  -- 2. L-Equivalence & Non-Interference:         10 +
  -- 3. Arrays Extension:                         15 =
  ---------------------------------------------------------------------------
  -- *  Total:                                    35 pt

  -- The goal of this exercise is to formalize a static IFC type system
  -- for a simple language with algebraic data types, which we will
  -- later extend with heap-allocated arrays.  To represent algebraic
  -- data types, the language must include the following constructs:
  --
  -- Numbers    n ∈ ℕ
  -- Variables  x, y, z
  -- Expr.      e := x | n                                  -- variables for input values and numbers
  --               | ⟨ e₁ , e₂ ⟩ | fst(e) | snd(e)          -- pairs and projections
  --               | inj₁(e) | inj₂(e) | case(e, x.e, x.e)  -- sum types and case split

  -- The security policy considered in this exercise is defined by the
  -- classic 2-point lattice, where security label L indicates public
  -- (Low) data, security label H indicates secret (High) data, and
  -- secret-to-public flows of information are disallowed, i.e., H ⋤ L.

  data Label : Set where
    L : Label
    H : Label

  data _⊑_ : Label → Label → Set where
    H⊑H : H ⊑ H
    L⊑ : ∀ {ℓ : Label} → L ⊑ ℓ


  --------------------------------------------------------------------------------
  -- 1. Well-Typed Syntax & Semantics (10pt)

  -- Define appropriate labeled types for this language and then give
  -- a well-typed syntax for its constructs, i.e., expressions,
  -- values, and input environments. Lastly, give a big-step
  -- type-preserving semantics for the language.

  -- In the syntax for expressions, do not forget to include security
  -- checks to prevent data leaks!  These checks (constraints ℓ ⊑ ℓ'
  -- between security labels) should not involve concrete labels
  -- (e.g., L and H from the 2-point lattice above). Instead, let them
  -- be always relative to the label of other sub-expressions, so that
  -- you can reuse the type system for other security lattices as
  -- well.  Explain how the constraints in the rules prevent data
  -- leaks with concrete examples (i.e., programs that, without those
  -- constraints, would leak).

  --------------------------------------------------------------------------------
  -- 2. L-Equivalence & Non-Interference (10pt)

  -- Define an appropriate type-indexed L-equivalence relation for
  -- labeled values and environments. Make sure that only values and
  -- environments that are *indistinguishable* to an attacker at
  -- security level L can be related by these relations.

  -- State non-interference for this language and then prove that all
  -- well-typed programs satisfy non-interference.

  --------------------------------------------------------------------------------
  -- 3. Arrays Extension (15pt)

  -- (5pt) Extend the syntax of types, values, and expressions given
  -- in exercise 1, so that programs can dynamically create, read, and
  -- write arrays in a type- and memory-safe way, and securely,
  -- without leaking data.  In particular, add the following
  -- constructs to the category of expressions:

  -- Expr. e := ... | new(e₁, e₂)   -- Allocate an array of length e₁ in the heap and initialize it with the value of e₂
  --                | e₁[e₂]        -- Read array e₁ at index e₂
  --                | e₁[e₂] ≔ e₃   -- Update the content of array e₁ at index e₂ with the value of e₃.
  --                | len(e)        -- Return the length of array e

  -- Explain how the constraints for the operations that read and
  -- write the heap prevent data leaks through explicit and implicit
  -- flows.

  -- Similarly, add heaps and configurations to the language and adapt
  -- the semantics given in exercise 1 accordingly.

  -- (10pt) Extend the definition of L-equivalence for the new values
  -- and add similar relations for the new syntactic constructs
  -- (configurations and heaps). Adapt the definition of
  -- non-interference for the new extensions and then complete the
  -- previous proof with the missing cases and fix the cases that are
  -- now incomplete.

  -- End of Part §2.
  --------------------------------------------------------------------------------
