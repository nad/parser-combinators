------------------------------------------------------------------------
-- And
------------------------------------------------------------------------

-- TODO: Unify with AsymmetricChoice and Not.

module TotalParserCombinators.And where

open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any as Any
open import Data.List.Any.BagAndSetEquality
open import Data.List.Any.Membership
open import Data.Product
open import Function.Inverse as Inv using (_⇿_)
open import Relation.Binary.Product.Pointwise

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)
open RawMonadPlus List.monadPlus using (_⊗_)

open import TotalParserCombinators.BreadthFirst hiding (correct)
open import TotalParserCombinators.Congruence as C using (_≈[_]P_; _≅P_)
import TotalParserCombinators.Congruence.Sound as CS
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics using (_∈_·_)

------------------------------------------------------------------------
-- And

-- p₁ & p₂ returns a result if both p₁ and p₂ do.

-- Note that this definition is closely related to Theorem 4.4 in
-- Brzozowski's paper "Derivatives of Regular Expressions". This paper
-- also contains an and operator.

infixr 6 _&_

_&_ : ∀ {Tok R₁ R₂ xs₁ xs₂} →
      Parser Tok R₁ xs₁ → Parser Tok R₂ xs₂ →
      Parser Tok (R₁ × R₂) (xs₁ ⊗ xs₂)
p₁ & p₂ = (token >>= λ t → ♯ (D t p₁ & D t p₂))
        ∣ return⋆ (initial-bag p₁ ⊗ initial-bag p₂)

------------------------------------------------------------------------
-- Properties of asymmetric choice

-- D distributes over _&_.

D-& : ∀ {Tok R₁ R₂ xs₁ xs₂ t}
      (p₁ : Parser Tok R₁ xs₁) (p₂ : Parser Tok R₂ xs₂) →
      D t (p₁ & p₂) ≅P D t p₁ & D t p₂
D-& {xs₁ = xs₁} {xs₂} {t} p₁ p₂ =
  D t (p₁ & p₂)                           ≅⟨ D t (p₁ & p₂) ∎ ⟩

  (return t >>= λ t → D t p₁ & D t p₂) ∣
    D t (return⋆ (xs₁ ⊗ xs₂))             ≅⟨ Monad.left-identity t (λ t → D t p₁ & D t p₂) ∣
                                             D.D-return⋆ (xs₁ ⊗ xs₂) ⟩
  (D t p₁ & D t p₂) ∣ fail                ≅⟨ AdditiveMonoid.right-identity (D t p₁ & D t p₂) ⟩

  D t p₁ & D t p₂                         ∎
  where open C using (_≅⟨_⟩_; _∎; _∣_)

-- _&_ preserves equality.

_&-cong_ : ∀ {k Tok R xs₁ xs₁′ xs₂ xs₂′}
             {p₁  : Parser Tok R xs₁} {p₁′ : Parser Tok R xs₁′}
             {p₂  : Parser Tok R xs₂} {p₂′ : Parser Tok R xs₂′} →
           p₁ ≈[ k ]P p₁′ → p₂ ≈[ k ]P p₂′ → p₁ & p₂ ≈[ k ]P p₁′ & p₂′
_&-cong_ {k} {xs₁ = xs₁} {xs₁′} {xs₂} {xs₂′} {p₁} {p₁′} {p₂} {p₂′}
         p₁≈p₁′ p₂≈p₂′ = lemma ∷ λ t → ♯ (
  D t (p₁ & p₂)      ≅⟨ D-& p₁ p₂ ⟩
  D t p₁  & D t p₂   ≈⟨ D-congP p₁≈p₁′ &-cong D-congP p₂≈p₂′ ⟩
  D t p₁′ & D t p₂′  ≅⟨ sym (D-& p₁′ p₂′) ⟩
  D t (p₁′ & p₂′)    ∎)
  where
  open C using (_≅⟨_⟩_; _≈⟨_⟩_; _∎; sym; _∷_)

  lemma : (xs₁ ⊗ xs₂) List-≈[ k ] (xs₁′ ⊗ xs₂′)
  lemma = ⊗-cong (I.same-bag/set (CS.sound p₁≈p₁′))
                 (I.same-bag/set (CS.sound p₂≈p₂′))

-- _&_ is correct.

correct : ∀ {Tok R₁ R₂ xs₁ xs₂ x₁ x₂} s
          (p₁ : Parser Tok R₁ xs₁) (p₂ : Parser Tok R₂ xs₂) →
          (x₁ , x₂) ∈ p₁ & p₂ · s ⇿ (x₁ ∈ p₁ · s × x₂ ∈ p₂ · s)
correct {xs₁ = xs₁} {xs₂} {x₁} {x₂} [] p₁ p₂ =
  (x₁ , x₂) ∈ p₁ & p₂ · []       ⇿⟨ I.correct ⟩
  ((x₁ , x₂) ∈ (xs₁ ⊗ xs₂))      ⇿⟨ sym ⊗-∈⇿ ⟩
  (x₁ ∈ xs₁ × x₂ ∈ xs₂)          ⇿⟨ sym (I.correct ×-⇿ I.correct) ⟩
  (x₁ ∈ p₁ · [] × x₂ ∈ p₂ · [])  ∎
  where open Inv.EquationalReasoning
correct {x₁ = x₁} {x₂} (t ∷ s) p₁ p₂ =
  (x₁ , x₂) ∈ p₁ & p₂ · t ∷ s          ⇿⟨ sym D-correct ⟩
  (x₁ , x₂) ∈ D t (p₁ & p₂) · s        ⇿⟨ CS.sound (D-& p₁ p₂) ⟩
  (x₁ , x₂) ∈ D t p₁ & D t p₂ · s      ⇿⟨ correct s (D t p₁) (D t p₂) ⟩
  (x₁ ∈ D t p₁ · s × x₂ ∈ D t p₂ · s)  ⇿⟨ D-correct ×-⇿ D-correct ⟩
  (x₁ ∈ p₁ · t ∷ s × x₂ ∈ p₂ · t ∷ s)  ∎
  where open Inv.EquationalReasoning
