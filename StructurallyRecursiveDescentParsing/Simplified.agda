------------------------------------------------------------------------
-- A simplified parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Simplified where

open import Codata.Musical.Notation
open import Data.Bool
open import Data.List using (List; _∷_; []; _++_)
import Data.List.Effectful as ListMonad
import Data.List.Properties as ListProp
open import Data.List.Relation.Binary.BagAndSetEquality
open import Data.List.NonEmpty
  using (List⁺; _∷_; [_]; _⁺++_; head; tail)
import Data.List.NonEmpty.Effectful as List⁺
open import Data.List.NonEmpty.Properties
open import Effect.Monad
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open RawMonad {f = zero} ListMonad.monad
  using () renaming (_>>=_ to _>>=′_)
open RawMonad {f = zero} List⁺.monad
  using () renaming (_>>=_ to _>>=⁺_)
private
  open module BagS {A : Set} = Setoid ([ bag ]-Equality A)
    using () renaming (_≈_ to _Bag-≈_)

open import TotalParserCombinators.Parser as P
  hiding (Parser; module Parser)

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
-- "Initial bags"

-- The initial bag of a parser is calculated in such a way that it is
-- obvious, given the nullability of the parser, whether or not the
-- bag is empty.

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
  ∣-lemma {true}          p₁ p₂ = refl

  ?>>=-lemma : ∀ {e₂ Tok R₁ R₂}
               (p₁ : Parser Tok true R₁) (p₂ : R₁ → Parser Tok e₂ R₂) →
               initial (p₂ (head (initial⁺ p₁ refl))) ++
                 (tail (initial⁺ p₁ refl) >>=′ λ x → initial (p₂ x)) ≡
               initial (p₁ ?>>= p₂)
  ?>>=-lemma {false} p₁ p₂ = ListMonad.MonadProperties.right-zero
                               (tail (initial⁺ p₁ refl))
  ?>>=-lemma {true}  p₁ p₂ = toList->>= f xs
    where f  = λ x → initial⁺ (p₂ x) refl
          xs = initial⁺ p₁ refl

------------------------------------------------------------------------
-- Semantics

-- The semantics of simplified parsers is defined by translation.

⟦_⟧ : ∀ {Tok e R} (p : Parser Tok e R) → P.Parser Tok R (initial p)
⟦ return x   ⟧ = return x
⟦ fail       ⟧ = fail
⟦ token      ⟧ = token
⟦ p₁ ∣ p₂    ⟧ = cast lem (⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧)
                 where
                 lem : _ Bag-≈ _
                 lem = BagS.reflexive (∣-lemma p₁ p₂)
⟦ p₁ !>>= p₂ ⟧ =           ⟦ p₁ ⟧ >>= λ x → ♯ ⟦ ♭ (p₂ x) ⟧
⟦ p₁ ?>>= p₂ ⟧ = cast lem (⟦ p₁ ⟧ >>= λ x →   ⟦    p₂ x  ⟧)
                 where
                 lem : _ Bag-≈ _
                 lem = BagS.reflexive (?>>=-lemma p₁ p₂)
