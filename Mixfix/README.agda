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
-- the paper).

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

------------------------------------------------------------------------
-- Acyclic graphs

-- Precedence graphs and precedence-correct expressions.

import Mixfix.Acyclic.Expr

-- A custom-made parser combinator library (with a formal semantics).

import Mixfix.Acyclic.Lib

-- Mixfix operator grammars. The resulting expressions are
-- precedence-correct by construction.

import Mixfix.Acyclic.Grammar

-- Linearisation of operators, and a proof showing that all the
-- generated strings are syntactically correct (although perhaps
-- ambiguous).

import Mixfix.Acyclic.Show

-- An example.

import Mixfix.Acyclic.Example

------------------------------------------------------------------------
-- Cyclic graphs

-- Precedence graphs and precedence-correct expressions.

import Mixfix.Cyclic.Expr

-- A custom-made parser combinator library (with a formal semantics).

import Mixfix.Cyclic.Lib

-- Mixfix operator grammars. The resulting expressions are
-- precedence-correct by construction.

import Mixfix.Cyclic.Grammar

-- Linearisation of operators, and a proof showing that all the
-- generated strings are syntactically correct (although perhaps
-- ambiguous).

import Mixfix.Cyclic.Show
