------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Type where

open import Coinduction
open import Data.Bool
open import Data.List
open import Data.Product1 as Prod renaming (∃₀₁ to ∃; map₀₁ to map)
open import Data.Function
open import Data.Empty
open import Relation.Binary.PropositionalEquality

infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_

------------------------------------------------------------------------
-- Parsers

-- A type for parsers which can be implemented using recursive
-- descent. The types used ensure that the implemented backends are
-- structurally recursive.
--
-- The boolean index is true iff the parser accepts the empty string.

data Parser (Tok : Set) : Bool → Set → Set1 where
  return : ∀ {R} (x : R) → Parser Tok true R

  fail   : ∀ {R} → Parser Tok false R

  token  : Parser Tok false Tok

  _∣_    : ∀ {e₁ e₂ R}
           (p₁ : Parser Tok  e₁       R)
           (p₂ : Parser Tok       e₂  R) →
                 Parser Tok (e₁ ∨ e₂) R

  -- The second parser's index cannot depend on the result of the
  -- first parser, because (in general) the result depends on the
  -- input string, and the index of p₁ ?>>= p₂, for which the result
  -- is not in scope, is the same as that of p₂.
  _?>>=_ : ∀ {e₂ R₁ R₂}
           (p₁ :      Parser Tok true R₁)
           (p₂ : R₁ → Parser Tok e₂   R₂) →
                      Parser Tok e₂   R₂

  -- If the first parser is guaranteed to consume something, then the
  -- second parser's index can depend on the result of the first
  -- parser, because the resulting index is already known to be false.
  _!>>=_ : ∀ {R₁ R₂} {e₂ : R₁ → Bool}
           (p₁ :                Parser Tok false  R₁)
           (p₂ : (x : R₁) → ∞₁ (Parser Tok (e₂ x) R₂)) →
                                Parser Tok false  R₂

-- Note that there is only one coinductive recursive component
-- (annotated with ∞₁). Making any other recursive component
-- coinductive would allow left recursive grammars to be formed, but
-- it is safe to use coinduction in _!>>=_ because we know that a
-- token has been consumed, so for every successive use of coinduction
-- we are at least one step closer to the end of the input.

------------------------------------------------------------------------
-- Semantics

-- The semantics of the parsers. x ∈ p · s means that x can be the
-- result of applying the parser p to the string s. Note that the
-- semantics is defined inductively.

infix 4 _∈_·_

data _∈_·_ {Tok} : ∀ {R e} → R → Parser Tok e R → List Tok → Set1 where
  return : ∀ {R} {x : R} → x ∈ return x · []
  token  : ∀ {x} → x ∈ token · [ x ]
  ∣ˡ     : ∀ {R x e₁ e₂ s} {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₁·s : x ∈ p₁ · s) → x ∈ p₁ ∣ p₂ · s
  ∣ʳ     : ∀ {R x e₂ s} e₁ {p₁ : Parser Tok e₁ R} {p₂ : Parser Tok e₂ R}
           (x∈p₂·s : x ∈ p₂ · s) → x ∈ p₁ ∣ p₂ · s
  _?>>=_ : ∀ {R₁ R₂ x y e₂ s₁ s₂}
             {p₁ : Parser Tok true R₁} {p₂ : R₁ → Parser Tok e₂ R₂}
           (x∈p₁·s₁ : x ∈ p₁ · s₁) (y∈p₂x·s₂ : y ∈ p₂ x · s₂) →
           y ∈ p₁ ?>>= p₂ · s₁ ++ s₂
  _!>>=_ : ∀ {R₁ R₂ x y} {e₂ : R₁ → Bool} {s₁ s₂}
             {p₁ : Parser Tok false R₁}
             {p₂ : (x : R₁) → ∞₁ (Parser Tok (e₂ x) R₂)}
           (x∈p₁·s₁ : x ∈ p₁ · s₁) (y∈p₂x·s₂ : y ∈ ♭₁ (p₂ x) · s₂) →
           y ∈ p₁ !>>= p₂ · s₁ ++ s₂

------------------------------------------------------------------------
-- Some lemmas

-- A simple cast lemma.

cast : ∀ {Tok e R} {p : Parser Tok e R} {x s s′} →
       s ≡ s′ → x ∈ p · s → x ∈ p · s′
cast refl x∈ = x∈

-- Sanity check: The Bool index is true iff the empty string is
-- accepted.

does : ∀ {Tok R} (p : Parser Tok true R) → ∃ λ x → x ∈ p · []
does p = does′ p refl
  where
  does′ : ∀ {Tok e R}
          (p : Parser Tok e R) → e ≡ true → ∃ λ x → x ∈ p · []
  does′ (return x)          refl = (x , return)
  does′ (_∣_ {true}  p₁ p₂) refl = Prod.map id ∣ˡ         (does p₁)
  does′ (_∣_ {false} p₁ p₂) refl = Prod.map id (∣ʳ false) (does p₂)
  does′ (p₁ ?>>= p₂)        refl with does p₁
  does′ (p₁ ?>>= p₂)        refl | (x , x∈p₁·[]) =
    Prod.map id (_?>>=_ x∈p₁·[]) (does (p₂ x))
  does′ fail         ()
  does′ token        ()
  does′ (p₁ !>>= p₂) ()

doesNot : ∀ {Tok R} (p : Parser Tok false R) → ∃ (λ x → x ∈ p · []) → ⊥
doesNot p x∈p·[] = doesNot′ p refl x∈p·[] refl
  where
  doesNot′ : ∀ {Tok R e s} (p : Parser Tok e R) → e ≡ false →
             ∃ (λ x → x ∈ p · s) → s ≢ []
  doesNot′ (return x) () _ _
  doesNot′ fail  refl (_ , ()) _
  doesNot′ token refl (_ , ()) refl
  doesNot′ (_∣_ {true}          p₁ p₂) () _ _
  doesNot′ (_∣_ {false} {true}  p₁ p₂) () _ _
  doesNot′ (_∣_ {false} {false} p₁ p₂) refl (x , ∣ˡ        x∈p₁·s) refl = doesNot p₁ (x , x∈p₁·s)
  doesNot′ (_∣_ {false} {false} p₁ p₂) refl (x , ∣ʳ .false x∈p₂·s) refl = doesNot p₂ (x , x∈p₂·s)
  doesNot′ (p₁ ?>>= p₂) refl (y , _?>>=_ {x = x} {s₁ = []} x∈p₁·[] y∈p₂x·[]) refl = doesNot (p₂ x) (y , y∈p₂x·[])
  doesNot′ (p₁ ?>>= p₂) refl (y , _?>>=_         {s₁ = _ ∷ _} _ _) ()
  doesNot′ (p₁ !>>= p₂) refl (y , _!>>=_ {x = x} {s₁ = []} x∈p₁·[] y∈p₂x·[]) refl = doesNot p₁ (x , x∈p₁·[])
  doesNot′ (p₁ !>>= p₂) refl (y , _!>>=_         {s₁ = _ ∷ _} _ _) ()
