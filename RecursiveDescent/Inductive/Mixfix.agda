------------------------------------------------------------------------
-- Parsing of mixfix operators
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix where

import Data.Vec as Vec
import Data.List as List
open List using (List; []; _∷_; foldr; foldl)
import Data.Vec1 as Vec1
open Vec1 using (Vec₁)
open import Data.Product renaming (_,_ to pair)
open import Data.Product.Record using (_,_)
open import Data.Bool
open import Data.Unit
open import Data.Nat
open import Data.Function hiding (_⟨_⟩_)
import Data.String as String

open import RecursiveDescent.Inductive.Mixfix.FA
open import RecursiveDescent.Inductive.Mixfix.Expr
open import RecursiveDescent.Index
open import RecursiveDescent.Inductive
open import RecursiveDescent.Inductive.SimpleLib
import RecursiveDescent.Inductive.Lib as Lib
import RecursiveDescent.Inductive.Token as Tok
open Tok String.decSetoid

-- Note that, even though grammar below is not recursive, these
-- functions are (mutually). Fortunately the recursion is structural,
-- though. Note also that the reason for not using the implementation
--
--   grammar (precs g ts) = choiceMap (\t -> ! prec g t) ts
--
-- is that this would lead to a definition of prec-corners which
-- was not structurally recursive.

precs-corners : PrecedenceGraph -> PrecedenceGraph -> Corners
precs-corners g []       = _
precs-corners g (p ∷ ps) = _

prec-corners : PrecedenceGraph -> PrecedenceTree -> Corners
prec-corners g (node ops ps) = _

-- Nonterminals.

data NT : ParserType where
  lib : forall {i r} (p : Lib.Nonterminal NamePart NT i r) -> NT _ r

  -- Expressions.
  expr : (g : PrecedenceGraph) -> NT _ Expr

  -- Operator applications where the outermost operator has one of the
  -- precedences ps (and the overall precedence graph is g).
  precs : (g ps : PrecedenceGraph) ->
          NT (false , precs-corners g ps) Expr

  -- Operator applications where the outermost operator has
  -- precedence p (and the overall precedence graph is g).
  prec : (g : PrecedenceGraph) (p : PrecedenceTree) ->
         NT (false , prec-corners g p) Expr

open Lib.Combinators NamePart lib

-- The parser type used in this module.

P : Index -> Set -> Set1
P = Parser NamePart NT

-- A vector containing parsers recognising the name parts of the
-- operator.

nameParts : forall {fix arity} -> Operator fix arity ->
            Vec₁ (P _ NamePart) (1 + arity)
nameParts (operator ns) = Vec1.map₀₁ sym ns

-- Internal parts (all name parts plus internal expressions) of
-- operators of the given precedence and fixity.

internal : forall (g : PrecedenceGraph) {fix}
           (ops : List (∃ (Operator fix))) -> P _ (Internal fix)
internal g =
  choiceMap (\op' -> let op = proj₂ op' in
                     _∙_ op <$> (! expr g between nameParts op))

-- The grammar.

grammar : Grammar NamePart NT
grammar (lib p)                 = library p
grammar (expr g)                = ! precs g g
grammar (precs g [])            = fail
grammar (precs g (p ∷ ps))      = ! prec g p ∣ ! precs g ps
grammar (prec  g (node ops ps)) =
    ⟪_⟫                <$>  ⟦ closed ⟧
  ∣ _⟨_⟩_              <$>  ↑ ⊛ ⟦ infx non ⟧ ⊛ ↑
  ∣ flip (foldr ⟪_⟩_)  <$>  ⟦ prefx ⟧ + ⊛ ↑
  ∣ flip (foldr _$_)   <$>  (_⟨_⟩_ <$> ↑ ⊛ ⟦ infx right ⟧) + ⊛ ↑
  ∣ foldl _⟨_⟫         <$>  ↑ ⊛ ⟦ postfx ⟧ +
  ∣ foldl (flip _$_)   <$>  ↑ ⊛ (⟨_⟩_,_ <$> ⟦ infx left ⟧ ⊛ ↑) +
  where
  ⟨_⟩_,_ = \op e₂ e₁ -> e₁ ⟨ op ⟩ e₂

  -- ⟦ fix ⟧ parses the internal parts of operators with the
  -- current precedence level and fixity fix.
  ⟦_⟧ = \fix -> internal g (ops fix)

  -- Operator applications where the outermost operator binds
  -- tighter than the current precedence level.
  ↑ = ! precs g ps
