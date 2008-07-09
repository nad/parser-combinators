------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

module Parallel.Examples where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Product.Record
import Data.Char as C
import Data.String as S
open C using (Char)
open S using (String)
open import Relation.Binary.PropositionalEquality

open import Parallel
open import Utilities
open import Parallel.Lib
open Sym C.decSetoid

-- A function used to simplify the examples a little.

_∈?_ : forall {i r} -> String -> Parser Char i r -> [ r ]
s ∈? p = parse-complete p (S.toList s)

module Ex₀ where

  -- This example illustrates a problem with this library. This
  -- definition is not productive, but is otherwise well-typed. That
  -- is fine, but if this definition is rejected by a productivity
  -- checker, how can we expect the other definitions below to be
  -- accepted? In fact, are they productive? Maybe not...

  p : Parser Char (false , 12) String
  p ~ return 5 ⊛> p

  -- ex₁ : "apa" ∈? p ≡ {! !}
  -- ex₁ = ≡-refl

module Ex₁ where

  -- e ∷= 0 + e | 0

  e ~ sym '0' ⊛> sym '+' ⊛> e
    ∣ sym '0'

  ex₁ : "0+0" ∈? e ≡ '0' ∷ []
  ex₁ = ≡-refl

module Ex₂ where

  -- e ∷= f + e | f
  -- f ∷= 0 | 0 * f | ( e )

  mutual

    expr   ~ factor ⊛> sym '+' ⊛> expr
           ∣ factor

    factor ~ sym '0'
           ∣ sym '0' ⊛> sym '*' ⊛> factor
           ∣ sym '(' ⊛> expr <⊛ sym ')'

  ex₁ : "(0*)" ∈? expr ≡ []
  ex₁ = ≡-refl

  ex₂ : "0*(0+0)" ∈? expr ≡ '0' ∷ []
  ex₂ = ≡-refl

{-
module Ex₃ where

  -- This is not allowed:

  -- e ∷= f + e | f
  -- f ∷= 0 | f * 0 | ( e )

  mutual

    expr   ~ factor ⊛> sym '+' ⊛> expr
           ∣ factor

    factor ~ sym '0'
           ∣ factor ⊛> sym '*' ⊛> sym '0'
           ∣ sym '(' ⊛> expr <⊛ sym ')'
-}

module Ex₄ where

  -- The language aⁿbⁿcⁿ, which is not context free.

  -- The non-terminal top returns the number of 'a' characters parsed.

  -- top     ∷= aⁿbⁿcⁿ
  -- as n    ∷= aˡ⁺¹bⁿ⁺ˡ⁺¹cⁿ⁺ˡ⁺¹
  -- bcs x n ∷= xⁿ⁺¹

  bcs : Char -> ℕ -> Parser Char _ ℕ
  bcs c zero    = sym c ⊛> return 0
  bcs c (suc n) = sym c ⊛> bcs c n

  as : ℕ -> Parser Char _ ℕ
  as n ~ suc <$ sym 'a' ⊛
         ( as (suc n)
         ∣ _+_ <$> bcs 'b' n ⊛ bcs 'c' n
         )

  top = return 0 ∣ as zero

  ex₁ : "aaabbbccc" ∈? top ≡ 3 ∷ []
  ex₁ = ≡-refl

  ex₂ : "aaabbccc" ∈? top ≡ []
  ex₂ = ≡-refl

module Ex₅ where

  -- A grammar making use of a parameterised parser from the library.

  a  = sym 'a'
  as = length <$> a ⋆

  ex₁ : "aaaaa" ∈? as ≡ 5 ∷ []
  ex₁ = ≡-refl

module Ex₆ where

  -- A grammar which uses the chain₁ combinator.

  op = _+_ <$ sym '+'
     ∣ _*_ <$ sym '*'
     ∣ _∸_ <$ sym '∸'

  expr : Assoc -> Parser Char _ ℕ
  expr a = chain₁ a number op

  ex₁ : "123" ∈? number ≡ 123 ∷ []
  ex₁ = ≡-refl

  -- Note: The type checking of the following definitions does not
  -- appear to terminate (with the version of Agda which is current at
  -- the time of writing).

  -- ex₂ : "1+5*2∸3" ∈? expr left ≡ 9 ∷ []
  -- ex₂ = ≡-refl

  -- ex₃ : "1+5*2∸3" ∈? expr right ≡ 1 ∷ []
  -- ex₃ = ≡-refl

module Ex₇ where

  -- A proper expression example.

  addOp = _+_ <$ sym '+'
        ∣ _∸_ <$ sym '∸'
  mulOp = _*_ <$ sym '*'

  mutual

    expr   ~ chain₁ left term   addOp
    term   ~ chain₁ left factor mulOp
    factor ~ sym '(' ⊛> expr <⊛ sym ')'
           ∣ number

  -- Note: The type checking of the following definitions does not
  -- appear to terminate (with the version of Agda which is current at
  -- the time of writing).

  -- ex₁ : "1+5*2∸3" ∈? expr ≡ 8 ∷ []
  -- ex₁ = ≡-refl

  -- ex₂ : "1+5*(2∸3)" ∈? expr ≡ 1 ∷ []
  -- ex₂ = ≡-refl
