------------------------------------------------------------------------
-- This module proves that the context-sensitive language aⁿbⁿcⁿ can
-- be recognised
------------------------------------------------------------------------

-- This is obvious given the proof in
-- TotalRecognisers.LeftRecursion.ExpressiveStrength but the code
-- below provides a non-trivial example of the use of the parser
-- combinators.

module TotalRecognisers.LeftRecursion.NotOnlyContextFree where

open import Algebra
open import Coinduction
open import Data.Bool using (Bool; true; false; _∨_)
open import Function
open import Data.List as List using (List; []; _∷_; _++_; [_])
private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as NatProp
open NatProp.SemiringSolver
private
  module NatCS = CommutativeSemiring NatProp.commutativeSemiring
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open ≡-Reasoning

import TotalRecognisers.LeftRecursion
import TotalRecognisers.LeftRecursion.Lib as Lib

------------------------------------------------------------------------
-- The alphabet

data Tok : Set where
  a b c : Tok

_≟_ : Decidable (_≡_ {A = Tok})
a ≟ a = yes refl
a ≟ b = no λ()
a ≟ c = no λ()
b ≟ a = no λ()
b ≟ b = yes refl
b ≟ c = no λ()
c ≟ a = no λ()
c ≟ b = no λ()
c ≟ c = yes refl

open TotalRecognisers.LeftRecursion Tok
open Lib Tok
private
  open module TokTok = Lib.Tok Tok _≟_ using (tok)

------------------------------------------------------------------------
-- An auxiliary definition and a boring lemma

infixr 8 _^^_

_^^_ : Tok → ℕ → List Tok
_^^_ = flip List.replicate

private

  shallow-comm : ∀ i n → i + suc n ≡ suc (i + n)
  shallow-comm i n =
    solve 2 (λ i n → i :+ (con 1 :+ n) := con 1 :+ i :+ n) refl i n

------------------------------------------------------------------------
-- Some lemmas relating _^^_, _^_ and tok

tok-^-complete : ∀ t i → t ^^ i ∈ tok t ^ i
tok-^-complete t zero    = ε
tok-^-complete t (suc i) =
  add-♭♯ (false ^ⁿ i) TokTok.complete · tok-^-complete t i

tok-^-sound : ∀ t i {s} → s ∈ tok t ^ i → s ≡ t ^^ i
tok-^-sound t zero    ε         = refl
tok-^-sound t (suc i) (t∈ · s∈)
  with TokTok.sound (drop-♭♯ (false ^ⁿ i) t∈)
... | refl = cong (_∷_ t) (tok-^-sound t i s∈)

------------------------------------------------------------------------
-- aⁿbⁿcⁿ

-- The context-sensitive language { aⁿbⁿcⁿ | n ∈ ℕ } can be recognised
-- using the parser combinators defined in this development.

private

  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-index : ℕ → Bool
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-index _ = _

  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ : (i : ℕ) → P (aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-index i)
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ i = cast lem (♯? (tok a) · ⟪ ♯ aⁿbⁱ⁺ⁿcⁱ⁺ⁿ (suc i) ⟫)
               ∣ ♯? (tok b ^ i) · ♯? (tok c ^ i)
    where lem = left-zero (aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-index (suc i))

aⁿbⁿcⁿ : P true
aⁿbⁿcⁿ = aⁿbⁱ⁺ⁿcⁱ⁺ⁿ 0

-- Let us prove that aⁿbⁿcⁿ is correctly defined.

aⁿbⁿcⁿ-string : ℕ → List Tok
aⁿbⁿcⁿ-string n = a ^^ n ++ b ^^ n ++ c ^^ n

private

  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-string : ℕ → ℕ → List Tok
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-string n i = a ^^ n ++ b ^^ (i + n) ++ c ^^ (i + n)

aⁿbⁿcⁿ-complete : ∀ n → aⁿbⁿcⁿ-string n ∈ aⁿbⁿcⁿ
aⁿbⁿcⁿ-complete n = aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-complete n 0
  where
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-complete : ∀ n i → aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-string n i ∈ aⁿbⁱ⁺ⁿcⁱ⁺ⁿ i
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-complete zero i with i + 0 | proj₂ NatCS.+-identity i
  ... | .i | refl = ∣ʳ {n₁ = false} (helper b · helper c)
    where
    helper = λ (t : Tok) →
      add-♭♯ (false ^ⁿ i) (tok-^-complete t i)
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-complete (suc n) i with i + suc n | shallow-comm i n
  ... | .(suc i + n) | refl =
    ∣ˡ $ cast {eq = lem} (
      add-♭♯ (aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-index (suc i)) TokTok.complete ·
      aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-complete n (suc i))
    where lem = left-zero (aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-index (suc i))

aⁿbⁿcⁿ-sound : ∀ {s} → s ∈ aⁿbⁿcⁿ → ∃ λ n → s ≡ aⁿbⁿcⁿ-string n
aⁿbⁿcⁿ-sound = aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-sound 0
  where
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-sound : ∀ {s} i → s ∈ aⁿbⁱ⁺ⁿcⁱ⁺ⁿ i →
                     ∃ λ n → s ≡ aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-string n i
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-sound i (∣ˡ (cast (t∈ · s∈)))
    with TokTok.sound (drop-♭♯ (aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-index (suc i)) t∈)
  ... | refl with aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-sound (suc i) s∈
  ... | (n , refl) = suc n , (begin
    a ^^ suc n ++ b ^^ (suc i + n) ++ c ^^ (suc i + n)
      ≡⟨ cong (λ i → a ^^ suc n ++ b ^^ i ++ c ^^ i)
              (sym (shallow-comm i n)) ⟩
    a ^^ suc n ++ b ^^ (i + suc n) ++ c ^^ (i + suc n)
      ∎)
  aⁿbⁱ⁺ⁿcⁱ⁺ⁿ-sound i (∣ʳ (_·_ {s₁} {s₂} s₁∈ s₂∈)) = 0 , (begin
    s₁ ++ s₂
      ≡⟨ cong₂ _++_ (tok-^-sound b i
                      (drop-♭♯ (false ^ⁿ i) s₁∈))
                    (tok-^-sound c i
                      (drop-♭♯ (false ^ⁿ i) s₂∈)) ⟩
    b ^^ i ++ c ^^ i
      ≡⟨ cong (λ i → b ^^ i ++ c ^^ i)
              (sym (proj₂ NatCS.+-identity i)) ⟩
    b ^^ (i + 0) ++ c ^^ (i + 0)
      ∎)
