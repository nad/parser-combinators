------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

module Examples where

open import Data.List
open import Data.Nat
open import Logic
import Data.Char as C
import Data.String as S
open C using (Char)
open import Parser
import Parser.Lib as Lib
private
  open module T = Token C.decSetoid

module Ex₁ where

  -- e ∷= 0 + e | 0

  data Name : ParserType where
    e : Name _ _

  grammar : Grammar Char Name
  grammar e = token '0' · token '+' · ! e
            ∣ token '0'

  ex₁ : ⟦ ! e ⟧ grammar (S.toList "0+0") ≡ [] ∷ S.toList "+0" ∷ []
  ex₁ = ≡-refl

module Ex₂ where

  -- e ∷= f + e | f
  -- f ∷= 0 | 0 * f | ( e )

  data Name : ParserType where
    expr   : Name _ _
    factor : Name _ _

  grammar : Grammar Char Name
  grammar expr   = ! factor · token '+' · ! expr
                 ∣ ! factor
  grammar factor = token '0'
                 ∣ token '0' · token '*' · ! factor
                 ∣ token '(' · ! expr · token ')'

  ex₁ : ⟦ ! expr ⟧ grammar (S.toList "(0*)") ≡ []
  ex₁ = ≡-refl

  ex₂ : ⟦ ! expr ⟧ grammar (S.toList "0*(0+0)") ≡
        S.toList "*(0+0)" ∷ [] ∷ []
  ex₂ = ≡-refl

{-

module Ex₃ where

  -- This is not allowed:

  -- e ∷= f + e | f
  -- f ∷= 0 | f * 0 | ( e )

  data Name : ParserType where
    expr   : Name _ _
    factor : Name _ _

  grammar : Grammar Char Name
  grammar expr   = ! factor · token '+' · ! expr
                 ∣ ! factor
  grammar factor = token '0'
                 ∣ ! factor · token '*' · token '0'
                 ∣ token '(' · ! expr · token ')'

-}

module Ex₄ where

  -- The language aⁿbⁿcⁿ, which is not context free.

  data Name : ParserType where
    top :              Name _ _
    as  :         ℕ -> Name _ _
    bcs : Char -> ℕ -> Name _ _

  grammar : Grammar Char Name
  grammar top             = ε ∣ ! as zero
  grammar (as n)          = token 'a' ·
                            (! as (suc n) ∣ ! bcs 'b' n · ! bcs 'c' n)
  grammar (bcs c zero)    = token c · ε
  grammar (bcs c (suc n)) = token c · ! bcs c n

  ex₁ : ⟦ ! top ⟧ grammar (S.toList "aaabbbccc") ≡
        S.toList "aaabbbccc" ∷ [] ∷ []
  ex₁ = ≡-refl

  ex₂ : ⟦ ! top ⟧ grammar (S.toList "aaabbccc") ≡
        S.toList "aaabbccc" ∷ []
  ex₂ = ≡-refl

module Ex₅ where

  -- A grammar making use of a parameterised parser from the library.

  data Name : ParserType where
    lib : forall {e d} -> Lib.Name Char Name e d -> Name _ _
    a   : Name _ _
    as  : Name _ _

  private
    open module L = Lib.Combinators Char lib

  grammar : Grammar Char Name
  grammar (lib p) = library p
  grammar a       = token 'a'
  grammar as      = ! a ⋆

  ex₁ : ⟦ ! as ⟧ grammar (S.toList "aab") ≡
        S.toList "aab" ∷ S.toList "ab" ∷ S.toList "b" ∷ []
  ex₁ = ≡-refl
