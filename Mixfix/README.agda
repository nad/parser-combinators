------------------------------------------------------------------------
-- Mixfix operator grammars, and parsing of mixfix operators
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module Mixfix.README where

-- There are two separate developments here. One is very close to the
-- paper "Parsing Mixfix Operators" (by me and Ulf Norell), and uses
-- directed acyclic precedence graphs and grammars which are neither
-- left nor right recursive. The other uses precedence graphs which
-- may be cyclic and grammars which can be both left and right
-- recursive (following an alternative definition of grammars given in
-- the paper). The two grammar schemes are equivalent when restricted
-- to acyclic precedence graphs.

-- The grammars which use DAGs have the advantage that they can be
-- implemented using a larger variety of parser combinator libraries.
-- This could lead to a more efficient implementation. On the other
-- hand the definition of the other grammars does not attempt to avoid
-- left and right recursion, which means that it is arguably a bit
-- easier to understand and work with (compare the proofs in
-- Mixfix.Acyclic.Show and Mixfix.Cyclic.Show, for instance).

------------------------------------------------------------------------
-- Shared code

-- Fixity and associativity.

import Mixfix.Fixity

-- Operators.

import Mixfix.Operator

-- Precedence-correct expressions, parametrised on abstract precedence
-- graphs.

import Mixfix.Expr

------------------------------------------------------------------------
-- Acyclic graphs

-- A custom-made parser combinator library (with a formal semantics).

import Mixfix.Acyclic.Lib

-- Acyclic precedence graphs.

import Mixfix.Acyclic.PrecedenceGraph

-- Mixfix operator grammars. The resulting expressions are
-- precedence-correct by construction.

import Mixfix.Acyclic.Grammar

-- A minor lemma.

import Mixfix.Acyclic.Lemma

-- Linearisation of operators, and a proof showing that all the
-- generated strings are syntactically correct (although perhaps
-- ambiguous). If the result is combined with the one in
-- Mixfix.Cyclic.Uniqueness we get that every expression has a unique
-- representation. (Two different expressions may have the same
-- representation, though.)

import Mixfix.Acyclic.Show

-- An example.

import Mixfix.Acyclic.Example

------------------------------------------------------------------------
-- Cyclic graphs

-- A custom-made parser combinator library (with a formal semantics).

import Mixfix.Cyclic.Lib

-- Cyclic precedence graphs. (These graphs are not used below, because
-- Mixfix.Cyclic.Grammar can handle arbitrary precedence graphs.)

import Mixfix.Cyclic.PrecedenceGraph

-- Mixfix operator grammars. The resulting expressions are
-- precedence-correct by construction.

import Mixfix.Cyclic.Grammar

-- A constructive proof (i.e. a "show" function) showing that every
-- expression has at least one representation.

import Mixfix.Cyclic.Show

-- A proof showing that every expression has at most one
-- representation.

import Mixfix.Cyclic.Uniqueness

-- An example.

import Mixfix.Cyclic.Example

------------------------------------------------------------------------
-- Equivalence

-- For acyclic precedence graphs the two grammar definitions above are
-- equivalent.

import Mixfix.Equivalence
