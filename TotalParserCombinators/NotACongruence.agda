------------------------------------------------------------------------
-- One can construct combinators which do not preserve equality
------------------------------------------------------------------------

module TotalParserCombinators.NotACongruence where

open import Coinduction
open import Data.Bool
open import Data.List
open import Function
open import Function.Equality
open import Function.Inverse as Inv
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary

open import TotalParserCombinators.Congruence using (_≅P_; _∷_)
open import TotalParserCombinators.Derivative
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics as S using (_∈_·_; _≅_)

-- It is easy to construct a combinator which does not preserve
-- equality. All it takes is to inspect the input combinator's
-- structure (or that of its index), and make some suitable decision
-- based on this information. Examples:

module Example₁ where

  -- A combinator which removes ambiguity.

  unambiguous : ∀ {Tok R xs} →
                Parser Tok R xs → Parser Tok R (take 1 xs)
  unambiguous {xs = xs} p =
      token >>= (λ t → ♯ unambiguous (D t p))
    ∣ return⋆ (take 1 xs)

  -- The following two parsers are (parser) equal.

  p₁ : Parser Bool Bool (true ∷ (false ∷ []))
  p₁ = return true ∣ return false

  p₂ : Parser Bool Bool (false ∷ (true ∷ []))
  p₂ = return false ∣ return true

  equal : p₁ ≅P p₂
  equal = AdditiveMonoid.commutative (return true) (return false)

  -- However, unambiguous does not respect this equality.

  unambiguous-is-not-a-congruence :
    ¬ (unambiguous p₁ ≅ unambiguous p₂)
  unambiguous-is-not-a-congruence eq =
    case Inverse.to eq ⟨$⟩ S.∣-right [] (S.∣-left S.return) of λ
      { (S.∣-right .[] (S.∣-left               ()))
      ; (S.∣-right .[] (S.∣-right .([ false ]) ()))
      ; (S.∣-left []∈) → helper refl []∈
      }
    where
    helper : ∀ {s} {f : Bool → List Bool}
               {p : ∀ b → ∞ (Parser Bool Bool (f b))} →
               s ≡ [] →
             ¬ (true ∈ token >>= p · s)
    helper () (S._>>=_ S.token _)

module Example₂ where

  -- A combinator which returns true (without consuming input) if its
  -- argument is "fail", and false otherwise.

  is-fail-bag : ∀ {Tok R xs} → Parser Tok R xs → List Bool
  is-fail-bag fail = [ true  ]
  is-fail-bag _    = [ false ]

  is-fail : ∀ {Tok R xs}
            (p : Parser Tok R xs) → Parser Tok Bool (is-fail-bag p)
  is-fail fail             = return true
  is-fail (return x)       = return false
  is-fail token            = return false
  is-fail (p₁ ∣ p₂)        = return false
  is-fail (f <$> p)        = return false
  is-fail (p₁ ⊛ p₂)        = return false
  is-fail (p₁ >>= p₂)      = return false
  is-fail (nonempty p)     = return false
  is-fail (cast xs₁≈xs₂ p) = return false

  -- The following parsers are equal, but is-fail treats them
  -- differently.

  p₁ : Parser Bool Bool []
  p₁ = fail

  p₂ : Parser Bool Bool []
  p₂ = fail ∣ fail

  equal : p₁ ≅P p₂
  equal = Inv.id ∷ λ _ → ♯ equal

  is-fail-is-not-a-congruence : ¬ (is-fail p₁ ≅ is-fail p₂)
  is-fail-is-not-a-congruence eq with Inverse.to eq ⟨$⟩ S.return
  ... | ()
