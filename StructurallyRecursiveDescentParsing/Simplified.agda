------------------------------------------------------------------------
-- A simplified parser type
------------------------------------------------------------------------

-- Less general, but sometimes easier to use.

module StructurallyRecursiveDescentParsing.Simplified where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.Bool
open import Data.Function
open import Data.Product

import Data.List.NonEmpty as List⁺
open List⁺ using (List⁺; _∷_; [_]; _⁺++⁺_; _⁺++_; _++⁺_; head; tail)
open RawMonad List⁺.monad using () renaming (_>>=_ to _>>=⁺_)
open import Data.List.NonEmpty.Properties

import Data.List as List
open List using (List; _∷_; []; _++_)
private module LM {A} = Monoid (List.monoid A)
open RawMonad List.monad using () renaming (_>>=_ to _>>=′_)
import Data.List.Properties as ListProp

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import StructurallyRecursiveDescentParsing.Coinduction
import StructurallyRecursiveDescentParsing.Parser as Parser
open Parser hiding (Parser)

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
           (p₁ :                Parser Tok false  R₁)
           (p₂ : (x : R₁) → ∞₁ (Parser Tok (e₂ x) R₂)) →
                                Parser Tok false  R₂

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

-- Boring lemmas.

private

  >>=-∅ : ∀ {A B} (xs : List A) →
          (xs >>=′ const {List B} []) ≡ []
  >>=-∅ []       = refl
  >>=-∅ (x ∷ xs) = >>=-∅ xs

  tail-++ : ∀ {A} (xs ys : List⁺ A) →
            tail xs ++ List⁺.toList ys ≡ tail (xs ⁺++⁺ ys)
  tail-++ [ x ]    ys = refl
  tail-++ (x ∷ xs) ys = toList-⁺++⁺ xs ys

  head->>= : ∀ {A B} (f : A → List⁺ B) (xs : List⁺ A) →
             head (f (head xs)) ≡ head (xs >>=⁺ f)
  head->>= f [ x ]    = refl
  head->>= f (x ∷ xs) with f x
  head->>= f (x ∷ xs) | [ y ]    = refl
  head->>= f (x ∷ xs) | (y ∷ ys) = refl

  tail->>= : ∀ {A B} (f : A → List⁺ B) (xs : List⁺ A) →
             tail (f (head xs)) ++ (tail xs >>=′ λ x → head (f x) ∷ tail (f x)) ≡
             tail (xs >>=⁺ f)
  tail->>= f [ x ]    = proj₂ LM.identity _
  tail->>= f (x ∷ xs) = begin
    tail (f x) ++ (List⁺.toList xs >>=′ λ x → head (f x) ∷ tail (f x)) ≡⟨ cong (λ ys → tail (f x) ++ List.concat ys)
                                                                               (ListProp.map-cong (η ∘ f) (List⁺.toList xs)) ⟩
    tail (f x) ++ (List⁺.toList xs >>=′ List⁺.toList ∘ f)              ≡⟨ cong (_++_ (tail (f x))) (toList->>= f xs) ⟩
    tail (f x) ++ (List⁺.toList (xs >>=⁺ f))                           ≡⟨ tail-++ (f x) (xs >>=⁺ f) ⟩
    tail (f x ⁺++⁺ (xs >>=⁺ f))                                        ≡⟨ refl ⟩
    tail (x ∷ xs >>=⁺ f)                                               ∎

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
  ?>>=-lemma {false} p₁ p₂ = >>=-∅ (tail (initial⁺ p₁ refl))
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
⟦ p₁ !>>= p₂ ⟧ =           ⟦ p₁ ⟧ >>= λ x → ♯₁ ⟦ ♭₁ (p₂ x) ⟧
⟦ p₁ ?>>= p₂ ⟧ = cast lem (⟦ p₁ ⟧ >>= λ x →    ⟦     p₂ x  ⟧)
                 where lem = ?>>=-lemma p₁ p₂
