------------------------------------------------------------------------
-- Asymmetric choice
------------------------------------------------------------------------

-- TODO: Unify with And and Not.

module TotalParserCombinators.AsymmetricChoice where

open import Coinduction
open import Data.List
open import Data.List.Any as Any using (here)
open import Data.Product as Prod
open import Function
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as Eq
open import Function.Inverse as Inv using (_⇿_)
import Relation.Binary.PropositionalEquality as P

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)

open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Congruence as C using (_≈[_]P_; _≅P_)
import TotalParserCombinators.Congruence.Sound as CS
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics using (_∈_·_)

------------------------------------------------------------------------
-- Asymmetric choice

-- Helper function: Returns the left-most non-empty list, if any.

first-nonempty : {R : Set} → List R → List R → List R
first-nonempty [] ys = ys
first-nonempty xs ys = xs

-- p₁ ◃ p₂ returns a result if either p₁ or p₂ does. For a given
-- string results are returned either from p₁ or from p₂, not both.

-- Note that this function pattern matches on one of the input
-- indices, so it is not obvious that it preserves equality. Instead
-- this fact is established explicitly below.

-- Note also that this definition is closely related to Theorem 4.4 in
-- Brzozowski's paper "Derivatives of Regular Expressions".

infixl 5 _◃_

_◃_ : ∀ {Tok R xs₁ xs₂} →
      Parser Tok R xs₁ → Parser Tok R xs₂ →
      Parser Tok R (first-nonempty xs₁ xs₂)
p₁ ◃ p₂ =
    (token >>= λ t → ♯ (D t p₁ ◃ D t p₂))
  ∣ return⋆ (first-nonempty (initial-bag p₁) (initial-bag p₂))

------------------------------------------------------------------------
-- Properties of asymmetric choice

-- D distributes over _◃_.

D-◃ : ∀ {Tok R xs₁ xs₂ t}
      (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
      D t (p₁ ◃ p₂) ≅P D t p₁ ◃ D t p₂
D-◃ {xs₁ = xs₁} {xs₂} {t} p₁ p₂ =
  D t (p₁ ◃ p₂)                             ≅⟨ D t (p₁ ◃ p₂) ∎ ⟩

  (return t >>= λ t → D t p₁ ◃ D t p₂) ∣
    D t (return⋆ (first-nonempty xs₁ xs₂))  ≅⟨ Monad.left-identity t (λ t → D t p₁ ◃ D t p₂) ∣
                                               D.D-return⋆ (first-nonempty xs₁ xs₂) ⟩
  (D t p₁ ◃ D t p₂) ∣ fail                  ≅⟨ AdditiveMonoid.right-identity (D t p₁ ◃ D t p₂) ⟩

  D t p₁ ◃ D t p₂                           ∎
  where open C using (_≅⟨_⟩_; _∎; _∣_)

-- first-nonempty preserves equality.

first-nonempty-cong :
  ∀ {k} {R : Set} {xs₁ xs₁′ xs₂ xs₂′ : List R} →
  xs₁ List-≈[ k ] xs₁′ → xs₂ List-≈[ k ] xs₂′ →
  first-nonempty xs₁ xs₂ List-≈[ k ] first-nonempty xs₁′ xs₂′
first-nonempty-cong {xs₁ = []}    {[]}    eq₁ eq₂ = eq₂
first-nonempty-cong {xs₁ = _ ∷ _} {_ ∷ _} eq₁ eq₂ = eq₁
first-nonempty-cong {xs₁ = []} {_ ∷ _} eq₁ eq₂
  with Eq.Equivalent.from (Inv.⇒⇔ eq₁) ⟨$⟩ here P.refl
... | ()
first-nonempty-cong {xs₁ = _ ∷ _} {[]} eq₁ eq₂
  with Eq.Equivalent.to (Inv.⇒⇔ eq₁) ⟨$⟩ here P.refl
... | ()

-- _◃_ preserves equality.

_◃-cong_ : ∀ {k Tok R xs₁ xs₁′ xs₂ xs₂′}
             {p₁  : Parser Tok R xs₁} {p₁′ : Parser Tok R xs₁′}
             {p₂  : Parser Tok R xs₂} {p₂′ : Parser Tok R xs₂′} →
           p₁ ≈[ k ]P p₁′ → p₂ ≈[ k ]P p₂′ → p₁ ◃ p₂ ≈[ k ]P p₁′ ◃ p₂′
_◃-cong_ {k} {xs₁ = xs₁} {xs₁′} {xs₂} {xs₂′} {p₁} {p₁′} {p₂} {p₂′}
         p₁≈p₁′ p₂≈p₂′ = lemma ∷ λ t → ♯ (
  D t (p₁ ◃ p₂)      ≅⟨ D-◃ p₁ p₂ ⟩
  D t p₁  ◃ D t p₂   ≈⟨ D-congP p₁≈p₁′ ◃-cong D-congP p₂≈p₂′ ⟩
  D t p₁′ ◃ D t p₂′  ≅⟨ sym (D-◃ p₁′ p₂′) ⟩
  D t (p₁′ ◃ p₂′)    ∎)
  where
  open C using (_≅⟨_⟩_; _≈⟨_⟩_; _∎; sym; _∷_)

  lemma : first-nonempty xs₁ xs₂ List-≈[ k ] first-nonempty xs₁′ xs₂′
  lemma = first-nonempty-cong (I.same-bag/set (CS.sound p₁≈p₁′))
                              (I.same-bag/set (CS.sound p₂≈p₂′))

-- If p₁ accepts s, then p₁ ◃ p₂ behaves as p₁ when applied to s.

left : ∀ {Tok R xs₁ xs₂ y} s
       (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
       (∃ λ y → y ∈ p₁ · s) → y ∈ p₁ ◃ p₂ · s ⇿ y ∈ p₁ · s
left {xs₁ = []} [] p₁ p₂ []∈p₁
  with I.complete (proj₂ []∈p₁)
... | ()
left {xs₁ = x ∷ xs₁} {y = y} [] p₁ p₂ []∈p₁ =
  y ∈ p₁ ◃ p₂ · []  ⇿⟨ I.correct ⟩
  (y ∈ x ∷ xs₁)     ⇿⟨ sym I.correct ⟩
  y ∈ p₁ · []       ∎
  where open Inv.EquationalReasoning
left {y = y} (t ∷ s) p₁ p₂ t∷s∈p₁ =
  y ∈ p₁ ◃ p₂         · t ∷ s  ⇿⟨ sym D-correct ⟩
  y ∈ D t (p₁ ◃ p₂)   ·     s  ⇿⟨ CS.sound (D-◃ p₁ p₂) ⟩
  y ∈ D t p₁ ◃ D t p₂ ·     s  ⇿⟨ left s (D t p₁) (D t p₂) (Prod.map id D-complete t∷s∈p₁) ⟩
  y ∈ D t p₁          ·     s  ⇿⟨ D-correct ⟩
  y ∈ p₁              · t ∷ s  ∎
  where open Inv.EquationalReasoning

-- If p₁ does not accept s, then p₁ ◃ p₂ behaves as p₂ when applied to
-- s.

right : ∀ {Tok R xs₁ xs₂ y} s
        (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
        (∄ λ y → y ∈ p₁ · s) → y ∈ p₁ ◃ p₂ · s ⇿ y ∈ p₂ · s
right {xs₁ = _ ∷ _} [] p₁ p₂ []∉p₁
  with []∉p₁ (, I.sound p₁ (here P.refl))
... | ()
right {xs₁ = []} {xs₂} {y = y} [] p₁ p₂ []∉p₁ =
  y ∈ p₁ ◃ p₂ · []  ⇿⟨ I.correct ⟩
  (y ∈ xs₂)         ⇿⟨ sym I.correct ⟩
  y ∈ p₂ · []       ∎
  where open Inv.EquationalReasoning
right {y = y} (t ∷ s) p₁ p₂ t∷s∉p₁ =
  y ∈ p₁ ◃ p₂         · t ∷ s  ⇿⟨ sym D-correct ⟩
  y ∈ D t (p₁ ◃ p₂)   ·     s  ⇿⟨ CS.sound (D-◃ p₁ p₂) ⟩
  y ∈ D t p₁ ◃ D t p₂ ·     s  ⇿⟨ right s (D t p₁) (D t p₂) (t∷s∉p₁ ∘ Prod.map id (D-sound p₁)) ⟩
  y ∈ D t p₂          ·     s  ⇿⟨ D-correct ⟩
  y ∈ p₂              · t ∷ s  ∎
  where open Inv.EquationalReasoning
