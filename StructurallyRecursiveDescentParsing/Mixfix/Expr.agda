------------------------------------------------------------------------
-- Concrete syntax used by the mixfix operator parser
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Mixfix.Expr where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec  using (Vec)
open import Data.List using (List; []; _∷_)
open import Data.List.Any as Any using (here; there)
open Any.Membership-≡ using (_∈_)
open import Data.Product using (∃; ∃₂; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import StructurallyRecursiveDescentParsing.Mixfix.Fixity

------------------------------------------------------------------------
-- Operators

-- Name parts.

NamePart : Set
NamePart = String

-- Operators. arity is the internal arity of the operator, i.e. the
-- number of arguments taken between the first and last name parts.

record Operator (fix : Fixity) (arity : ℕ) : Set where
  field nameParts : Vec NamePart (1 + arity)

open Operator public

-- Predicate filtering out operators of the given fixity and
-- associativity.

hasFixity : ∀ fix → ∃₂ Operator → Maybe (∃ (Operator fix))
hasFixity fix (fix' , op) with fix ≟ fix'
hasFixity fix (.fix , op) | yes refl = just op
hasFixity fix (fix' , op) | _        = nothing

------------------------------------------------------------------------
-- Precedence graphs

-- Precedence graphs are represented by their unfoldings as forests
-- (one tree for every node in the graph). This does not take into
-- account the sharing of the precedence graphs, but this code is
-- not aimed at efficiency.

-- Precedence trees.

data Precedence : Set where
  precedence : (o : (fix : Fixity) → List (∃ (Operator fix)))
               (s : List Precedence) →
               Precedence

-- Precedence forests.

PrecedenceGraph : Set
PrecedenceGraph = List Precedence

-- The operators of the given precedence.

ops : Precedence → (fix : Fixity) → List (∃ (Operator fix))
ops (precedence o s) = o

-- The immediate successors of the precedence level.

↑ : Precedence → List Precedence
↑ (precedence o s) = s

------------------------------------------------------------------------
-- Precedence-correct operator applications

-- Parameterised on a precedence graph.

module PrecedenceCorrect (g : PrecedenceGraph) where

  mutual

    infixl 4 _⟨_⟩ˡ_
    infixr 4 _⟨_⟩ʳ_
    infix  4 _⟨_⟩_ _⟨_⟫ ⟪_⟩_ _∙_

    -- Expr ps contains expressions where the outermost operator has
    -- one of the precedences in ps.

    data Expr (ps : List Precedence) : Set where
      _∙_ : ∀ {p assoc} (p∈ps : p ∈ ps) (e : ExprIn p assoc) → Expr ps

    -- ExprIn p assoc contains expressions where the outermost
    -- operator has precedence p (is /in/ precedence level p) and the
    -- associativity assoc.

    data ExprIn (p : Precedence) : Associativity → Set where
      ⟪_⟫    :                    (op : Inner (ops p closed      ))                     → ExprIn p non
      _⟨_⟫   : (l : Outer p left) (op : Inner (ops p postfx      ))                     → ExprIn p left
      ⟪_⟩_   :                    (op : Inner (ops p prefx       )) (r : Outer p right) → ExprIn p right
      _⟨_⟩_  : (l : Expr (↑ p)  ) (op : Inner (ops p (infx non  ))) (r : Expr (↑ p)   ) → ExprIn p non
      _⟨_⟩ˡ_ : (l : Outer p left) (op : Inner (ops p (infx left ))) (r : Expr (↑ p)   ) → ExprIn p left
      _⟨_⟩ʳ_ : (l : Expr (↑ p)  ) (op : Inner (ops p (infx right))) (r : Outer p right) → ExprIn p right

    -- Outer p fix contains expressions where the head operator either
    --   ⑴ has precedence p and associativity assoc or
    --   ⑵ binds strictly tighter than p.

    data Outer (p : Precedence) (assoc : Associativity) : Set where
      similar : (e : ExprIn p assoc) → Outer p assoc
      tighter : (e : Expr (↑ p))     → Outer p assoc

    -- Inner ops contains the internal parts (operator plus
    -- internal arguments) of operator applications. The operators
    -- have to be members of ops.

    data Inner {fix} (ops : List (∃ (Operator fix))) : Set where
      _∙_ : ∀ {arity op}
            (op∈ops : (arity , op) ∈ ops) (args : Vec (Expr g) arity) →
            Inner ops

  -- "Weakening".

  weakenE : ∀ {p ps} → Expr ps → Expr (p ∷ ps)
  weakenE (p∈ps ∙ e) = there p∈ps ∙ e

  weakenI : ∀ {fix ops} {op : ∃ (Operator fix)} →
            Inner ops → Inner (op ∷ ops)
  weakenI (op∈ops ∙ args) = there op∈ops ∙ args
