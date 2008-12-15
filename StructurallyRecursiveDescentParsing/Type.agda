------------------------------------------------------------------------
-- The parser data type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Type where

open import Data.Bool

open import StructurallyRecursiveDescentParsing.Index

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implemented backends are
-- structurally recursive.

-- The parsers are indexed on a type of nonterminals.

codata Parser (Tok : Set) (NT : ParserType) : ParserType₁ where
  return : forall {R} -> R -> Parser Tok NT (true ◇ leaf) R
  _?>>=_ : forall {c₁ e₂ c₂ R₁ R₂} ->
           Parser Tok NT (true ◇ c₁) R₁ ->
           (R₁ -> Parser Tok NT (e₂ ◇ c₂) R₂) ->
           Parser Tok NT (e₂ ◇ node c₁ c₂) R₂
  _!>>=_ : forall {c₁ R₁ R₂} {i₂ : R₁ -> Index} ->
           Parser Tok NT (false ◇ c₁) R₁ ->
           ((x : R₁) -> Parser Tok NT (i₂ x) R₂) ->
           Parser Tok NT (false ◇ step c₁) R₂
  fail   : forall {R} -> Parser Tok NT (false ◇ leaf) R
  alt    : forall e₁ e₂ {c₁ c₂ R} ->
           Parser Tok NT (e₁      ◇ c₁)         R ->
           Parser Tok NT (e₂      ◇ c₂)         R ->
           Parser Tok NT (e₁ ∨ e₂ ◇ node c₁ c₂) R
  token  : Parser Tok NT (false ◇ leaf) Tok
  !_     : forall {e c R} ->
           NT (e ◇ c) R -> Parser Tok NT (e ◇ step c) R

-- Grammars.

Grammar : Set -> ParserType -> Set1
Grammar Tok NT = forall {i R} -> NT i R -> Parser Tok NT i R
