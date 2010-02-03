------------------------------------------------------------------------
-- A simplified parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Simplified where

open import Category.Monad
open import Coinduction
open import Data.Bool

import Data.List.NonEmpty as List⁺
open List⁺ using (List⁺; _∷_; [_]; _⁺++_; head; tail)
open RawMonad List⁺.monad using () renaming (_>>=_ to _>>=⁺_)
open import Data.List.NonEmpty.Properties

import Data.List as List
open List using (List; _∷_; []; _++_)
open RawMonad List.monad using () renaming (_>>=_ to _>>=′_)
import Data.List.Properties as ListProp

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser as Parser hiding (Parser)
open import StructurallyRecursiveDescentParsing.Simplified.Lemmas

------------------------------------------------------------------------
-- Parsers

infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_

-- A type for parsers which are not left recursive.
--
-- The boolean index is true iff the parser is nullable (accepts the
-- empty string).

data Parser (Tok : Set) : Bool → Set → Set1 where
  return : ∀ {R} (x : R) → Parser Tok true R
  fail   : ∀ {R} → Parser Tok false R
  token  : Parser Tok false Tok
  _∣_    : ∀ {e₁ e₂ R}
           (p₁ : Parser Tok  e₁       R)
           (p₂ : Parser Tok       e₂  R) →
                 Parser Tok (e₁ ∨ e₂) R
  _?>>=_ : ∀ {e₂ R₁ R₂}
           (p₁ :      Parser Tok true R₁)
           (p₂ : R₁ → Parser Tok e₂   R₂) →
                      Parser Tok e₂   R₂
  _!>>=_ : ∀ {R₁ R₂} {e₂ : R₁ → Bool}
           (p₁ :               Parser Tok false  R₁)
           (p₂ : (x : R₁) → ∞ (Parser Tok (e₂ x) R₂)) →
                               Parser Tok false  R₂

-- Note that Parser has only one coinductive recursive component.
-- Making any other recursive component coinductive would allow left
-- recursive grammars to be formed, but it is safe to use coinduction
-- in _>>=_ when we know that a token has been consumed, because for
-- every successive use of coinduction we are at least one step closer
-- to the end of the input.

------------------------------------------------------------------------
-- "Initial sets"

-- The initial set of a parser is calculated in such a way that it is
-- obvious, given the nullability of the parser, whether or not the
-- set is empty.

mutual

  initial⁺ : ∀ {Tok e R} → Parser Tok e R → e ≡ true → List⁺ R
  initial⁺ (return x)                  refl = [ x ]
  initial⁺ fail                        ()
  initial⁺ token                       ()
  initial⁺ (_∣_ {true}          p₁ p₂) refl = initial⁺ p₁ refl ⁺++ initial p₂
  initial⁺ (_∣_ {false} {true}  p₁ p₂) refl = initial⁺ p₂ refl
  initial⁺ (_∣_ {false} {false} p₁ p₂) ()
  initial⁺ (p₁ ?>>= p₂)                refl = initial⁺ p₁     refl >>=⁺ λ x →
                                              initial⁺ (p₂ x) refl
  initial⁺ (p₁ !>>= p₂)                ()

  initial : ∀ {e Tok R} → Parser Tok e R → List R
  initial {false} p = []
  initial {true}  p = head is ∷ tail is
    where is = initial⁺ p refl

-- Some boring lemmas.

private

  ∣-lemma : ∀ {e₁ e₂ Tok R}
            (p₁ : Parser Tok e₁ R) (p₂ : Parser Tok e₂ R) →
            initial p₁ ++ initial p₂ ≡ initial (p₁ ∣ p₂)
  ∣-lemma {false} {false} p₁ p₂ = refl
  ∣-lemma {false} {true}  p₁ p₂ = refl
  ∣-lemma {true}          p₁ p₂ = begin
    (head xs ∷ tail xs) ++ ys ≡⟨ cong (λ xs → xs ++ ys) (η xs) ⟩
    List⁺.toList xs ++ ys     ≡⟨ toList-⁺++ xs ys ⟩
    List⁺.toList (xs ⁺++ ys)  ≡⟨ sym (η xsys) ⟩
    head xsys ∷ tail xsys     ∎
    where
    xs   = initial⁺ p₁ refl
    ys   = initial p₂
    xsys = xs ⁺++ ys

  ?>>=-lemma : ∀ {e₂ Tok R₁ R₂}
               (p₁ : Parser Tok true R₁) (p₂ : R₁ → Parser Tok e₂ R₂) →
               initial (p₂ (head (initial⁺ p₁ refl))) ++
                 (tail (initial⁺ p₁ refl) >>=′ λ x → initial (p₂ x)) ≡
               initial (p₁ ?>>= p₂)
  ?>>=-lemma {false} p₁ p₂ = ListProp.Monad.right-zero
                               (tail (initial⁺ p₁ refl))
  ?>>=-lemma {true}  p₁ p₂ = cong₂ _∷_ (head->>= f xs) (tail->>= f xs)
    where f  = λ x → initial⁺ (p₂ x) refl
          xs = initial⁺ p₁ refl

------------------------------------------------------------------------
-- Semantics

-- The semantics of simplified parsers is defined by translation.

⟦_⟧ : ∀ {Tok e R}
      (p : Parser Tok e R) → Parser.Parser Tok R (initial p)
⟦ return x   ⟧ = return x
⟦ fail       ⟧ = fail
⟦ token      ⟧ = token
⟦ p₁ ∣ p₂    ⟧ = cast lem (⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧)
                 where lem = ∣-lemma p₁ p₂
⟦ p₁ !>>= p₂ ⟧ =           ⟦ p₁ ⟧ >>= λ x → ⟪ ♯ ⟦ ♭ (p₂ x) ⟧ ⟫
⟦ p₁ ?>>= p₂ ⟧ = cast lem (⟦ p₁ ⟧ >>= λ x → ⟨   ⟦    p₂ x  ⟧ ⟩)
                 where lem = ?>>=-lemma p₁ p₂
