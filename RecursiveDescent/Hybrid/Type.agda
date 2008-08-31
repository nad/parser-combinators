------------------------------------------------------------------------
-- The parser data type
------------------------------------------------------------------------

-- This hybrid variant is coinductive /and/ includes !_.

module RecursiveDescent.Hybrid.Type where

open import Data.Bool
open import Data.Product.Record

open import RecursiveDescent.Index

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implemented backends are
-- structurally recursive.

-- The parsers are indexed on a type of nonterminals.

codata Parser (tok : Set) (nt : ParserType) : ParserType₁ where
  !_     :  forall {e c r}
         -> nt (e , c) r -> Parser tok nt (e , step c) r
  symbol :  Parser tok nt (false , leaf) tok
  return :  forall {r} -> r -> Parser tok nt (true , leaf) r
  fail   :  forall {r} -> Parser tok nt (false , leaf) r
  _?>>=_ :  forall {c₁ e₂ c₂ r₁ r₂}
         -> Parser tok nt (true , c₁) r₁
         -> (r₁ -> Parser tok nt (e₂ , c₂) r₂)
         -> Parser tok nt (e₂ , node c₁ c₂) r₂
  _!>>=_ :  forall {c₁ r₁ r₂} {i₂ : r₁ -> Index}
         -> Parser tok nt (false , c₁) r₁
         -> ((x : r₁) -> Parser tok nt (i₂ x) r₂)
         -> Parser tok nt (false , step c₁) r₂
  alt    :  forall e₁ e₂ {c₁ c₂ r}
         -> Parser tok nt (e₁      , c₁)         r
         -> Parser tok nt (e₂      , c₂)         r
         -> Parser tok nt (e₁ ∨ e₂ , node c₁ c₂) r

-- Grammars.

Grammar : Set -> ParserType -> Set1
Grammar tok nt = forall {i r} -> nt i r -> Parser tok nt i r
