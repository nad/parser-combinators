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
open S using (String)
open import Parser
open import Parser.Lib.Types
import Parser.Lib  as Lib
import Parser.Char as CharLib
private
  open module T = Token C.decSetoid

-- A function used to simplify the examples a little.

⟦_⟧′ :  forall {name i r}
     -> Parser Char name i r -> Grammar Char name
     -> String -> [ r ]
⟦ p ⟧′ g s = ⟦ p ⟧! g (S.toList s)

module Ex₁ where

  -- e ∷= 0 + e | 0

  data Name : ParserType where
    e : Name _ Char

  grammar : Grammar Char Name
  grammar e = token '0' ·> token '+' ·> ! e
            ∣ token '0'

  ex₁ : ⟦ ! e ⟧′ grammar "0+0" ≡ '0' ∷ []
  ex₁ = ≡-refl

module Ex₂ where

  -- e ∷= f + e | f
  -- f ∷= 0 | 0 * f | ( e )

  data Name : ParserType where
    expr   : Name _ Char
    factor : Name _ Char

  grammar : Grammar Char Name
  grammar expr   = ! factor ·> token '+' ·> ! expr
                 ∣ ! factor
  grammar factor = token '0'
                 ∣ token '0' ·> token '*' ·> ! factor
                 ∣ token '(' ·> ! expr <· token ')'

  ex₁ : ⟦ ! expr ⟧′ grammar "(0*)" ≡ []
  ex₁ = ≡-refl

  ex₂ : ⟦ ! expr ⟧′ grammar "0*(0+0)" ≡ '0' ∷ []
  ex₂ = ≡-refl

{-
module Ex₃ where

  -- This is not allowed:

  -- e ∷= f + e | f
  -- f ∷= 0 | f * 0 | ( e )

  data Name : ParserType where
    expr   : Name _ Char
    factor : Name _ Char

  grammar : Grammar Char Name
  grammar expr   = ! factor ·> token '+' ·> ! expr
                 ∣ ! factor
  grammar factor = token '0'
                 ∣ ! factor ·> token '*' ·> token '0'
                 ∣ token '(' ·> ! expr <· token ')'
-}

module Ex₄ where

  -- The language aⁿbⁿcⁿ, which is not context free.

  -- The non-terminal top returns the number of 'a' characters parsed.

  data Name : ParserType where
    top :              Name _ ℕ
    as  :         ℕ -> Name _ ℕ
    bcs : Char -> ℕ -> Name _ ℕ

  grammar : Grammar Char Name
  grammar top             = ε 0 ∣ ! as zero
  grammar (as n)          = suc <$ token 'a' ·
                            ( ! as (suc n)
                            ∣ _+_ $ ! bcs 'b' n · ! bcs 'c' n
                            )
  grammar (bcs c zero)    = token c ·> ε 0
  grammar (bcs c (suc n)) = token c ·> ! bcs c n

  ex₁ : ⟦ ! top ⟧′ grammar "aaabbbccc" ≡ 3 ∷ []
  ex₁ = ≡-refl

  ex₂ : ⟦ ! top ⟧′ grammar "aaabbccc" ≡ []
  ex₂ = ≡-refl

module Ex₅ where

  -- A grammar making use of a parameterised parser from the library.

  data Name : ParserType where
    lib : forall {i r} -> Lib.Name Char Name i r -> Name _ r
    a   : Name _ Char
    as  : Name _ ℕ

  private
    open module L = Lib.Combinators Char lib

  grammar : Grammar Char Name
  grammar (lib p) = library p
  grammar a       = token 'a'
  grammar as      = length $ ! a ⋆

  ex₁ : ⟦ ! as ⟧′ grammar "aaaaa" ≡ 5 ∷ []
  ex₁ = ≡-refl

module Ex₆ where

  -- A grammar which uses the chain₁ combinator.

  private
    module L = Lib Char

  data Name : ParserType where
    lib  : forall {i r} -> L.Name       Name i r -> Name _ r
    cLib : forall {i r} -> CharLib.Name Name i r -> Name _ r
    op   : Name _ (ℕ -> ℕ -> ℕ)
    expr : Assoc -> Name _ ℕ

  private
    open module LC = Lib.Combinators Char lib
    open module LC = CharLib.Combinators cLib

  grammar : Grammar Char Name
  grammar (lib p)  = library p
  grammar (cLib p) = charLib p
  grammar op       = _+_ <$ token '+'
                   ∣ _*_ <$ token '*'
                   ∣ _∸_ <$ token '∸'
  grammar (expr a) = chain₁ a number (! op)

  ex₁ : ⟦ number ⟧′ grammar "12345" ≡ 12345 ∷ []
  ex₁ = ≡-refl

  ex₂ : ⟦ ! expr left ⟧′ grammar "1+5*2∸3" ≡ 9 ∷ []
  ex₂ = ≡-refl

  ex₃ : ⟦ ! expr right ⟧′ grammar "1+5*2∸3" ≡ 1 ∷ []
  ex₃ = ≡-refl

module Ex₇ where

  -- A proper expression example.

  private
    module L = Lib Char

  data Name : ParserType where
    lib    : forall {i r} -> L.Name       Name i r -> Name _ r
    cLib   : forall {i r} -> CharLib.Name Name i r -> Name _ r
    expr   : Name _ ℕ
    term   : Name _ ℕ
    factor : Name _ ℕ
    addOp  : Name _ (ℕ -> ℕ -> ℕ)
    mulOp  : Name _ (ℕ -> ℕ -> ℕ)

  private
    open module LC = Lib.Combinators Char lib
    open module LC = CharLib.Combinators cLib

  grammar : Grammar Char Name
  grammar (lib p)  = library p
  grammar (cLib p) = charLib p
  grammar expr     = chain₁ left (! term)   (! addOp)
  grammar term     = chain₁ left (! factor) (! mulOp)
  grammar factor   = token '(' ·> ! expr <· token ')'
                   ∣ number
  grammar addOp    = _+_ <$ token '+'
                   ∣ _∸_ <$ token '∸'
  grammar mulOp    = _*_ <$ token '*'

  ex₁ : ⟦ ! expr ⟧′ grammar "1+5*2∸3" ≡ 8 ∷ []
  ex₁ = ≡-refl

  ex₂ : ⟦ ! expr ⟧′ grammar "1+5*(2∸3)" ≡ 1 ∷ []
  ex₂ = ≡-refl
