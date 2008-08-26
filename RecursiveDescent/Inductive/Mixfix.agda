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

-- Nonterminals.

data NT : ParserType where
  lib : forall {i r} (p : Lib.Nonterminal NamePart NT i r) -> NT _ r

  -- Expressions.
  expr : (g : PrecedenceGraph) -> NT _ Expr

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
-- operators of the given precedence, fixity and associativity.

internal : forall (g : PrecedenceGraph) {fix}
           (ops : List (∃ (Operator fix))) -> P _ (Internal fix)
internal g =
  choiceMap (\op' -> let op = proj₂ op' in
                     _∙_ op <$> (! expr g between nameParts op))

precs-corners : PrecedenceGraph -> PrecedenceGraph -> Corners
precs-corners g []       = _
precs-corners g (t ∷ ts) = _

prec-corners : PrecedenceGraph -> PrecedenceTree -> Corners
prec-corners g (node ops ts) = _

mutual

  -- Operator applications where the outermost operator has one of
  -- the given precedences. (Reason for not using choiceMap: to
  -- please the termination checker.)

  precs : (g ts : PrecedenceGraph) ->
          P (false , precs-corners g ts) Expr
  precs g []       = fail
  precs g (t ∷ ts) = prec g t ∣ precs g ts

  -- Operator applications where the outermost operator has the given
  -- precedence.

  prec : (g : PrecedenceGraph) (t : PrecedenceTree) ->
         P (false , prec-corners g t) Expr
  prec g (node ops ts) =
      ⟪_⟫                <$>  ⟦ closed ⟧
    ∣ flip (foldr ⟪_⟩_)  <$>  ⟦ prefx ⟧ + ⊛ ↑
    ∣ foldl _⟨_⟫         <$>  ↑ ⊛ ⟦ postfx ⟧ +
    ∣ _⟨_⟩_              <$>  ↑ ⊛ ⟦ infx non ⟧ ⊛ ↑
    ∣ flip (foldr _$_)   <$>  (_⟨_⟩_ <$> ↑ ⊛ ⟦ infx right ⟧) + ⊛ ↑
    ∣ foldl (flip _$_)   <$>  ↑ ⊛ (⟨_⟩_,_ <$> ⟦ infx left ⟧ ⊛ ↑) +
    where
    ⟨_⟩_,_ = \op e₂ e₁ -> e₁ ⟨ op ⟩ e₂

    -- ⟦ fix ⟧ parses the internal parts of operators with the
    -- current precedence level and fixity fix.
    ⟦_⟧ = \fix -> internal g (ops fix)

    -- Operator applications where the outermost operator binds
    -- tighter than the current precedence level.
    ↑ = precs g ts

-- The grammar.

grammar : Grammar NamePart NT
grammar (lib p)  = library p
grammar (expr g) = precs g g
