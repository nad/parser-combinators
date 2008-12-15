------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Examples where

open import Data.List
open import Data.Nat
import Data.Char as C
import Data.String as S
open C using (Char)
open S using (String)
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Index
open import StructurallyRecursiveDescentParsing.Interface
open import StructurallyRecursiveDescentParsing.Lib
open Token C.decSetoid
open import StructurallyRecursiveDescentParsing.Simple

-- A function used to simplify the examples a little.

_∈?_/_ : forall {NT i R} ->
         String -> Parser Char NT i R -> Grammar Char NT -> List R
s ∈? p / g = parse-complete p g (S.toList s)

module Ex₁ where

  -- e ∷= 0 + e | 0

  data Nonterminal : ParserType where
    e : Nonterminal _ Char

  grammar : Grammar Char Nonterminal
  grammar e = sym '0' ⊛> sym '+' ⊛> ! e
            ∣ sym '0'

  ex₁ : "0+0" ∈? (! e) / grammar ≡ '0' ∷ []
  ex₁ = ≡-refl

module Ex₂ where

  -- e ∷= f + e | f
  -- f ∷= 0 | 0 * f | ( e )

  data Nonterminal : ParserType where
    expr   : Nonterminal _ Char
    factor : Nonterminal _ Char

  grammar : Grammar Char Nonterminal
  grammar expr   = ! factor ⊛> sym '+' ⊛> ! expr
                 ∣ ! factor
  grammar factor = sym '0'
                 ∣ sym '0' ⊛> sym '*' ⊛> ! factor
                 ∣ sym '(' ⊛> ! expr <⊛ sym ')'

  ex₁ : "(0*)" ∈? (! expr) / grammar ≡ []
  ex₁ = ≡-refl

  ex₂ : "0*(0+0)" ∈? (! expr) / grammar ≡ '0' ∷ []
  ex₂ = ≡-refl

{-
module Ex₃ where

  -- This is not allowed:

  -- e ∷= f + e | f
  -- f ∷= 0 | f * 0 | ( e )

  data Nonterminal : ParserType where
    expr   : Nonterminal _ Char
    factor : Nonterminal _ Char

  grammar : Grammar Char Nonterminal
  grammar expr   = ! factor ⊛> sym '+' ⊛> ! expr
                 ∣ ! factor
  grammar factor = sym '0'
                 ∣ ! factor ⊛> sym '*' ⊛> sym '0'
                 ∣ sym '(' ⊛> ! expr <⊛ sym ')'
-}

module Ex₄ where

  -- The language aⁿbⁿcⁿ, which is not context free.

  -- The non-terminal top returns the number of 'a' characters parsed.

  data NT : ParserType where
    top :              NT _ ℕ  -- top     ∷= aⁿbⁿcⁿ
    as  :         ℕ -> NT _ ℕ  -- as n    ∷= aˡ⁺¹bⁿ⁺ˡ⁺¹cⁿ⁺ˡ⁺¹
    bcs : Char -> ℕ -> NT _ ℕ  -- bcs x n ∷= xⁿ⁺¹

  grammar : Grammar Char NT
  grammar top             = return 0 ∣ ! as zero
  grammar (as n)          = suc <$ sym 'a' ⊛
                            ( ! as (suc n)
                            ∣ _+_ <$> ! bcs 'b' n ⊛ ! bcs 'c' n
                            )
  grammar (bcs c zero)    = sym c ⊛> return 0
  grammar (bcs c (suc n)) = sym c ⊛> ! bcs c n

  ex₁ : "aaabbbccc" ∈? (! top) / grammar ≡ 3 ∷ []
  ex₁ = ≡-refl

  ex₂ : "aaabbccc" ∈? (! top) / grammar ≡ []
  ex₂ = ≡-refl

module Ex₅ where

  -- A grammar making use of a parameterised parser from the library.

  data NT : ParserType where
    a  : NT _ Char
    as : NT _ ℕ

  grammar : Grammar Char NT
  grammar a  = sym 'a'
  grammar as = length <$> ! a ⋆

  ex₁ : "aaaaa" ∈? (! as) / grammar ≡ 5 ∷ []
  ex₁ = ≡-refl

module Ex₆ where

  -- A grammar which uses the chain≥ combinator.

  data NT : ParserType where
    op   : NT _ (ℕ -> ℕ -> ℕ)
    expr : Assoc -> NT _ ℕ

  grammar : Grammar Char NT
  grammar op       = _+_ <$ sym '+'
                   ∣ _*_ <$ sym '*'
                   ∣ _∸_ <$ sym '∸'
  grammar (expr a) = chain≥ 0 a number (! op)

  ex₁ : "12345" ∈? number / grammar ≡ 12345 ∷ []
  ex₁ = ≡-refl

  ex₂ : "1+5*2∸3" ∈? (! expr left) / grammar ≡ 9 ∷ []
  ex₂ = ≡-refl

  ex₃ : "1+5*2∸3" ∈? (! expr right) / grammar ≡ 1 ∷ []
  ex₃ = ≡-refl

module Ex₇ where

  -- A proper expression example.

  data NT : ParserType where
    expr   : NT _ ℕ
    term   : NT _ ℕ
    factor : NT _ ℕ
    addOp  : NT _ (ℕ -> ℕ -> ℕ)
    mulOp  : NT _ (ℕ -> ℕ -> ℕ)

  grammar : Grammar Char NT
  grammar expr   = chain≥ 0 left (! term)   (! addOp)
  grammar term   = chain≥ 0 left (! factor) (! mulOp)
  grammar factor = sym '(' ⊛> ! expr <⊛ sym ')'
                 ∣ number
  grammar addOp  = _+_ <$ sym '+'
                 ∣ _∸_ <$ sym '∸'
  grammar mulOp  = _*_ <$ sym '*'

  ex₁ : "1+5*2∸3" ∈? (! expr) / grammar ≡ 8 ∷ []
  ex₁ = ≡-refl

  ex₂ : "1+5*(2∸3)" ∈? (! expr) / grammar ≡ 1 ∷ []
  ex₂ = ≡-refl
