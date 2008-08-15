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
open import Data.String using (String)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import RecursiveDescent.Inductive.Mixfix.FA

-- Name parts.

NamePart : Set
NamePart = String

-- Operators. arity is the internal arity of the operator, i.e. the
-- number of arguments taken between the first and last name parts.

data Operator (fa : FA) arity : Set where
  oper : (nameParts : Vec NamePart (1 + arity)) ->
         Operator fa arity

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

-- HasLeft/Right fix A evaluates to A if operators of fixity fix have
-- an external left/right argument.

HasLeft : Fixity -> Set -> Set
HasLeft prefx  _ = ⊤
HasLeft infx   A = A
HasLeft postfx A = A
HasLeft closed _ = ⊤

HasRight : Fixity -> Set -> Set
HasRight infx   A = A
HasRight prefx  A = A
HasRight postfx _ = ⊤
HasRight closed _ = ⊤

-- Concrete syntax. TODO: Ensure that expressions are precedence
-- correct by parameterising the expression type on a precedence graph
-- and indexing on precedences.

mutual

  infixl 4 _⟨_⟩_
  infix  4 _⟨_⟩

  data Expr : Set where
    -- Operator application.
    _⟨_⟩_  : forall {fa arity}
             (l  : HasLeft (fixity fa) Expr)
             (op : OpApp fa arity)
             (r  : HasRight (fixity fa) Expr) ->
             Expr

  -- Application of an operator to all its internal arguments.

  data OpApp fa arity : Set where
    _⟨_⟩ : (op : Operator fa arity) (args : Vec Expr arity) ->
           OpApp fa arity

-- Applies an OpApp to all remaining (outer) arguments.

AppType : Fixity -> Set
AppType postfx = Expr -> Expr
AppType infx   = Expr -> Expr -> Expr
AppType prefx  = Expr -> Expr
AppType closed = Expr

app : forall {fa} -> ∃ (OpApp fa) -> AppType (fixity fa)
app {prefx}  (_ , op) = \e     -> _  ⟨ op ⟩ e
app {infx _} (_ , op) = \e₁ e₂ -> e₁ ⟨ op ⟩ e₂
app {postfx} (_ , op) = \e     -> e  ⟨ op ⟩ _
app {closed} (_ , op) =           _  ⟨ op ⟩ _
