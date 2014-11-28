------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Examples where

open import Data.List
open import Data.Vec using ([]; _∷_)
open import Data.Nat
open import Data.Bool
import Data.Char as C
import Data.String as S
open C using (Char)
open S using (String)
open import Coinduction
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import StructurallyRecursiveDescentParsing.Index
open import StructurallyRecursiveDescentParsing.Grammar
open import StructurallyRecursiveDescentParsing.DepthFirst
open import StructurallyRecursiveDescentParsing.Lib
open Token C.decSetoid

-- Some functions used to simplify the examples a little.

_∈?_/_ : ∀ {NT i R} →
         String → Parser NT Char i R → Grammar NT Char → List R
s ∈? p / g = parseComplete (⟦ p ⟧ g) (S.toList s)

_∈?_ : ∀ {i R} → String → Parser EmptyNT Char i R → List R
s ∈? p = s ∈? p / emptyGrammar

module Ex₁ where

  mutual

    -- e ∷= 0 + e | 0

    data Nonterminal : NonTerminalType where
      e : Nonterminal _ Char

    grammar : Grammar Nonterminal Char
    grammar e = tok '0' ⊛> tok '+' ⊛> ! e
              ∣ tok '0'

  ex₁ : "0+0" ∈? ! e / grammar ≡ [ '0' ]
  ex₁ = P.refl

module Ex₂ where

  mutual

    -- e ∷= f + e | f
    -- f ∷= 0 | 0 * f | ( e )

    data Nonterminal : NonTerminalType where
      expr   : Nonterminal _ Char
      factor : Nonterminal _ Char

    grammar : Grammar Nonterminal Char
    grammar expr   = ! factor ⊛> tok '+' ⊛> ! expr
                   ∣ ! factor
    grammar factor = tok '0'
                   ∣ tok '0' ⊛> tok '*' ⊛> ! factor
                   ∣ tok '(' ⊛> ! expr <⊛ tok ')'

  ex₁ : "(0*)" ∈? ! expr / grammar ≡ []
  ex₁ = P.refl

  ex₂ : "0*(0+0)" ∈? ! expr / grammar ≡ [ '0' ]
  ex₂ = P.refl

{-
module Ex₃ where

  mutual

    -- This is not allowed:

    -- e ∷= f + e | f
    -- f ∷= 0 | f * 0 | ( e )

    data Nonterminal : NonTerminalType where
      expr   : Nonterminal _ Char
      factor : Nonterminal _ Char

  grammar : Grammar Nonterminal Char
  grammar expr   = ! factor ⊛> tok '+' ⊛> ! expr
                 ∣ ! factor
  grammar factor = tok '0'
                 ∣ ! factor ⊛> tok '*' ⊛> tok '0'
                 ∣ tok '(' ⊛> ! expr <⊛ tok ')'
-}

module Ex₄ where

  mutual

    -- The language aⁿbⁿcⁿ, which is not context free.

    -- The non-terminal top returns the number of 'a' characters
    -- parsed.

    -- Note: It is important that the ℕ argument to bcs is not named,
    -- because if it is Agda cannot infer the index.

    data NT : NonTerminalType where
      top :            NT _ ℕ  -- top     ∷= aⁿbⁿcⁿ
      as  :        ℕ → NT _ ℕ  -- as n    ∷= aˡ⁺¹bⁿ⁺ˡ⁺¹cⁿ⁺ˡ⁺¹
      bcs : Char → ℕ → NT _ ℕ  -- bcs x n ∷= xⁿ⁺¹

    grammar : Grammar NT Char
    grammar top             = return 0 ∣ ! (as zero)
    grammar (as n)          = suc <$ tok 'a' ⊛
                              ( ! (as (suc n))
                              ∣ _+_ <$> ! (bcs 'b' n) ⊛ ! (bcs 'c' n)
                              )
    grammar (bcs c zero)    = tok c ⊛> return 0
    grammar (bcs c (suc n)) = tok c ⊛> ! (bcs c n)

  ex₁ : "aaabbbccc" ∈? ! top / grammar ≡ [ 3 ]
  ex₁ = P.refl

  ex₂ : "aaabbccc" ∈? ! top / grammar ≡ []
  ex₂ = P.refl

module Ex₄′ where

  mutual

    -- A monadic variant of Ex₄.

    aⁿbⁿcⁿ = return 0
           ∣ tok 'a' +            !>>= λ as → ♯
             (let n = length as in
              exactly n (tok 'b') ⊛>
              exactly n (tok 'c') ⊛>
              return n)

    ex₁ : "aaabbbccc" ∈? aⁿbⁿcⁿ ≡ [ 3 ]
    ex₁ = P.refl

  ex₂ : "aaabbccc" ∈? aⁿbⁿcⁿ ≡ []
  ex₂ = P.refl

module Ex₅ where

  mutual

    -- A grammar making use of a parameterised parser from the
    -- library.

    data NT : NonTerminalType where
      a  : NT _ Char
      as : NT _ ℕ

    grammar : Grammar NT Char
    grammar a  = tok 'a'
    grammar as = length <$> ! a ⋆

  ex₁ : "aaaaa" ∈? ! as / grammar ≡ [ 5 ]
  ex₁ = P.refl

module Ex₆ where

  mutual

    -- A grammar which uses the chain≥ combinator.

    data NT : NonTerminalType where
      op   : NT _ (ℕ → ℕ → ℕ)
      expr : (a : Assoc) → NT _ ℕ

    grammar : Grammar NT Char
    grammar op       = _+_ <$ tok '+'
                     ∣ _*_ <$ tok '*'
                     ∣ _∸_ <$ tok '∸'
    grammar (expr a) = chain≥ 0 a number (! op)

  ex₁ : "12345" ∈? number / grammar ≡ [ 12345 ]
  ex₁ = P.refl

  ex₂ : "1+5*2∸3" ∈? ! (expr left) / grammar ≡ [ 9 ]
  ex₂ = P.refl

  ex₃ : "1+5*2∸3" ∈? ! (expr right) / grammar ≡ [ 1 ]
  ex₃ = P.refl

module Ex₇ where

  mutual

    -- A proper expression example.

    data NT : NonTerminalType where
      expr   : NT _ ℕ
      term   : NT _ ℕ
      factor : NT _ ℕ
      addOp  : NT _ (ℕ → ℕ → ℕ)
      mulOp  : NT _ (ℕ → ℕ → ℕ)

    grammar : Grammar NT Char
    grammar expr   = chain≥ 0 left (! term)   (! addOp)
    grammar term   = chain≥ 0 left (! factor) (! mulOp)
    grammar factor = tok '(' ⊛> ! expr <⊛ tok ')'
                   ∣ number
    grammar addOp  = _+_ <$ tok '+'
                   ∣ _∸_ <$ tok '∸'
    grammar mulOp  = _*_ <$ tok '*'

  ex₁ : "1+5*2∸3" ∈? ! expr / grammar ≡ [ 8 ]
  ex₁ = P.refl

  ex₂ : "1+5*(2∸3)" ∈? ! expr / grammar ≡ [ 1 ]
  ex₂ = P.refl

module Ex₈ where

  mutual

    -- An example illustrating the use of one grammar within another.

    data NT : NonTerminalType where
      lib   : ∀ {i R} (nt : Ex₇.NT i R) → NT i R
      exprs : NT _ (List ℕ)

    expr = lib Ex₇.expr

    grammar : Grammar NT Char
    grammar (lib nt) = mapNT lib (Ex₇.grammar nt)
    grammar exprs    = ! expr sepBy tok ','

  ex₁ : "1,2∸1" ∈? ! exprs / grammar ≡ [ 1 ∷ 1 ∷ [] ]
  ex₁ = P.refl

module Ex₉ where

  mutual

    -- An example illustrating the use of one grammar within another
    -- when the inner grammar contains non-terminals parameterised on
    -- parsers, and the outer grammar instantiates one of these
    -- parsers with an outer non-terminal.

    infix 55 _★ _∔

    data LibraryNT (NT : NonTerminalType) (Tok : Set) :
                   NonTerminalType where
      _★ : ∀ {c R} → Parser NT Tok (false ◇ c) R →
           LibraryNT NT Tok _ (List R)
      _∔ : ∀ {c R} → Parser NT Tok (false ◇ c) R →
           LibraryNT NT Tok _ (List R)

    library : ∀ {NT Tok} → (∀ {i R} → LibraryNT NT Tok i R → NT i R) →
              ∀ {i R} → LibraryNT NT Tok i R → Parser NT Tok i R
    library lift (p ★) = return [] ∣ ! (lift (p ∔))
    library lift (p ∔) = p              >>= λ x  →
                         ! (lift (p ★)) >>= λ xs →
                         return (x ∷ xs)

  mutual

    data NT : NonTerminalType where
      lib : ∀ {i R} → LibraryNT NT Char i R → NT i R
      a   : NT _ Char
      as  : NT _ (List Char)

    grammar : Grammar NT Char
    grammar (lib nt) = library lib nt
    grammar a        = tok 'a'
    grammar as       = ! (lib (! a ★))

  ex₁ : "aa" ∈? ! as / grammar ≡ [ 'a' ∷ 'a' ∷ [] ]
  ex₁ = P.refl
