------------------------------------------------------------------------
-- Concrete syntax used by the mixfix operator parser
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix.Expr where

open import Data.Nat hiding (_≟_)
open import Data.Vec
open import Data.List using (List)
open import Data.Product
open import Data.Maybe
open import Data.Unit
open import Data.Fin using (Fin)
open import Data.String using (String)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import RecursiveDescent.Inductive.Mixfix.FA

-- Name parts.

NamePart : Set
NamePart = String

-- Operators. arity is the internal arity of the operator, i.e. the
-- number of arguments taken between the first and last name parts.

data Operator (fix : Fixity) (arity : ℕ) : Set where
  operator : (nameParts : Vec NamePart (1 + arity)) ->
             Operator fix arity

-- Precedence graphs are represented by their unfoldings as forests
-- (one tree for every node in the graph). This does not take into
-- account the sharing of the precedence graphs, but this program is
-- not aimed at efficiency.

mutual

  PrecedenceGraph : Set
  PrecedenceGraph = List PrecedenceTree

  data PrecedenceTree : Set where
    node : (label : List (∃₂ Operator))
           (successors : PrecedenceGraph) -> PrecedenceTree

-- Predicate filtering out operators of the given fixity and
-- associativity.

hasFixity : forall fix -> ∃₂ Operator -> Maybe (∃ (Operator fix))
hasFixity fix (fix' , op) with fix ≟ fix'
hasFixity fix (.fix , op) | yes ≡-refl = just op
hasFixity fix (fix' , op) | _          = nothing

-- Concrete syntax. TODO: Ensure that expressions are precedence
-- correct by parameterising the expression type on a precedence graph
-- and indexing on precedences.

mutual

  infixl 4 _⟨_⟩_ _∙_
  infix  4 _⟨_⟫ ⟪_⟩_

  data Expr : Set where
    _⟨_⟩_ : forall {assoc}
            (l : Expr) (op : Internal (infx assoc)) (r : Expr) -> Expr
    _⟨_⟫  : (l : Expr) (op : Internal postfx)                  -> Expr
    ⟪_⟩_  :            (op : Internal prefx)        (r : Expr) -> Expr
    ⟪_⟫   :            (op : Internal closed)                  -> Expr

  -- Application of an operator to all its internal arguments.

  data Internal (fix : Fixity) : Set where
    _∙_ : forall {arity}
          (op : Operator fix arity) (args : Vec Expr arity) ->
          Internal fix
