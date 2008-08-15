------------------------------------------------------------------------
-- Concrete syntax used by the mixfix operator parser
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix.Expr where

open import Data.Nat hiding (_≟_)
open import Data.Vec
open import Data.List using ([_])
open import Data.Product
open import Data.Maybe
open import Data.Graph.Acyclic
open import Data.Unit
open import Data.Fin using (Fin)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import RecursiveDescent.Inductive.Mixfix.FA
open import RecursiveDescent.Inductive.Mixfix.Token

-- Operators.

data Operator (fa : FA) noParts-1 : Set where
  oper : (nameParts : Vec NamePart (1 + noParts-1)) ->
         Operator fa noParts-1

-- Precedence graphs.

PrecedenceGraph : ℕ -> Set
PrecedenceGraph = Graph [ ∃₂ Operator ] ⊤

-- Precedences (graph nodes).

Precedence : ℕ -> Set
Precedence = Fin

-- Predicate filtering out operators of the given fixity and
-- associativity.

hasFA : forall fa -> ∃₂ Operator -> Maybe (∃ (Operator fa))
hasFA fa (fa' , op) with fa ≟ fa'
hasFA fa (.fa , op) | yes ≡-refl = just op
hasFA fa (fa' , op) | _          = nothing

-- arity fix n is the arity of operators with fixity fix and 1 + n
-- name parts.

arity : Fixity -> ℕ -> ℕ
arity prefx  n = 1 + n
arity infx   n = 2 + n
arity postfx n = 1 + n

-- Concrete syntax. TODO: Ensure that expressions are precedence
-- correct by parameterising the expression type on a precedence graph
-- and indexing on precedences.

infixl 4 _∙_

data Expr : Set where
  -- Atom.
  atom : Expr

  -- Parenthesised expression.
  ⟨_⟩  : (e : Expr) -> Expr

  -- Operator application.
  _∙_  : forall {fa noParts-1}
         (op : Operator fa noParts-1)
         (args : Vec Expr (arity (fixity fa) noParts-1)) ->
         Expr

-- Application of an operator to all its internal arguments.

data OpApp fa noParts-1 : Set where
  _∙_ : (op : Operator fa noParts-1) (args : Vec Expr noParts-1) ->
        OpApp fa noParts-1

-- Applies an OpApp to all remaining (outer) arguments.

AppType : Fixity -> Set
AppType infx = Expr -> Expr -> Expr
AppType _    = Expr -> Expr

app : forall {fa} -> ∃ (OpApp fa) -> AppType (fixity fa)
app {prefx}  (_ , (op ∙ args)) = \e     -> op ∙ args ∷ʳ e
app {infx _} (_ , (op ∙ args)) = \e₁ e₂ -> op ∙ e₁ ∷ args ∷ʳ e₂
app {postfx} (_ , (op ∙ args)) = \e     -> op ∙ e ∷ args
