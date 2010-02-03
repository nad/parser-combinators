------------------------------------------------------------------------
-- Various parser combinator laws
------------------------------------------------------------------------

-- Note that terms like "monad" and "Kleene algebra" are interpreted
-- liberally below.

module TotalParserCombinators.Laws where

open import Algebra
open import Category.Monad
open import Coinduction
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq hiding (id; _∘_)
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.Membership as ∈
import Data.List.Any.Properties as AnyProp
import Data.List.Any.SetEquality as SetEq
open import Data.Product
open import Data.Unit using (⊤; tt)
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
  open module ListMonad = RawMonad List.monad
         using () renaming (_>>=_ to _>>=′_)
  open module SetS {A : Set} =
    Setoid (Any.Membership-≡.Set-equality {A})
      using () renaming (_≈_ to _≛_)
  module SetMonoid {A : Set} =
    CommutativeMonoid (SetEq.commutativeMonoid A)

open import TotalParserCombinators.Applicative
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.CoinductiveEquality
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- _∣_ and fail form an idempotent commutative monoid

module AdditiveMonoid where

  commutative : ∀ {Tok R xs₁ xs₂}
                (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
                p₁ ∣ p₂ ≈ p₂ ∣ p₁
  commutative p₁ p₂ = LanguageEquivalence.sound (commutative′ p₁ p₂)
    where
    commutative′ : ∀ {Tok R xs₁ xs₂}
                   (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
                   p₁ ∣ p₂ ≈′ p₂ ∣ p₁
    commutative′ {xs₁ = xs₁} {xs₂} p₁ p₂ =
      (λ {_} → SetMonoid.comm xs₁ xs₂) ∷ λ t → ♯
      commutative′ (∂ p₁ t) (∂ p₂ t)

  left-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → fail ∣ p ≈ p
  left-identity = LanguageEquivalence.sound ∘ left-identity′
    where
    left-identity′ : ∀ {Tok R xs} (p : Parser Tok R xs) → fail ∣ p ≈′ p
    left-identity′ p =
      (λ {_} → SetS.refl) ∷ λ t → ♯ left-identity′ (∂ p t)

  right-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → p ∣ fail ≈ p
  right-identity = LanguageEquivalence.sound ∘ right-identity′
    where
    right-identity′ : ∀ {Tok R xs} (p : Parser Tok R xs) →
                      p ∣ fail ≈′ p
    right-identity′ {xs = xs} p =
      (λ {_} → lemma) ∷ λ t → ♯ right-identity′ (∂ p t)
      where
      lemma : _ ≛ _
      lemma = SetS.reflexive (proj₂ ListMonoid.identity xs)

  associative : ∀ {Tok R xs₁ xs₂ xs₃}
                (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂)
                (p₃ : Parser Tok R xs₃) →
                p₁ ∣ (p₂ ∣ p₃) ≈ (p₁ ∣ p₂) ∣ p₃
  associative p₁ p₂ p₃ =
    LanguageEquivalence.sound $ associative′ p₁ p₂ p₃
    where
    associative′ : ∀ {Tok R xs₁ xs₂ xs₃}
                   (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂)
                   (p₃ : Parser Tok R xs₃) →
                   p₁ ∣ (p₂ ∣ p₃) ≈′ (p₁ ∣ p₂) ∣ p₃
    associative′ {xs₁ = xs₁} {xs₂} {xs₃} p₁ p₂ p₃ =
      (λ {_} → lemma) ∷ λ t → ♯ associative′ (∂ p₁ t) (∂ p₂ t) (∂ p₃ t)
      where
      lemma : _ ≛ _
      lemma = SetS.reflexive (P.sym $ ListMonoid.assoc xs₁ xs₂ xs₃)

  idempotent : ∀ {Tok R xs} (p : Parser Tok R xs) → p ∣ p ≈ p
  idempotent = LanguageEquivalence.sound ∘ idempotent′
    where
    idempotent′ : ∀ {Tok R xs} (p : Parser Tok R xs) → p ∣ p ≈′ p
    idempotent′ {xs = xs} p =
      (λ {_} → lemma) ∷ λ t → ♯ idempotent′ (∂ p t)
      where
      lemma : _ ≛ _
      lemma = equivalent (AnyProp.++-idempotent)
                         (AnyProp.++⁺ˡ {xs = xs})

------------------------------------------------------------------------
-- A variant of _⊑_

infix 4 _≤_

-- The AdditiveMonoid module shows that _∣_ can be viewed as the join
-- operation of a join-semilattice. This means that the following
-- definition of order is natural.

_≤_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≤ p₂ = p₁ ∣ p₂ ≈ p₂

-- This order coincides with _⊑_.

⊑⇔≤ : ∀ {Tok R xs₁ xs₂}
      (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
      p₁ ⊑ p₂ ⇔ p₁ ≤ p₂
⊑⇔≤ {xs₁ = xs₁} p₁ p₂ =
  equivalent
    (λ (p₁⊑p₂ : p₁ ⊑ p₂) {_} → equivalent (helper p₁⊑p₂) (∣ʳ xs₁))
    (λ (p₁≤p₂ : p₁ ≤ p₂) s∈p₁ → Equivalent.to p₁≤p₂ ⟨$⟩ ∣ˡ s∈p₁)
  where
  helper : p₁ ⊑ p₂ → p₁ ∣ p₂ ⊑ p₂
  helper p₁⊑p₂ (∣ˡ      s∈p₁) = p₁⊑p₂ s∈p₁
  helper p₁⊑p₂ (∣ʳ .xs₁ s∈p₂) = s∈p₂

------------------------------------------------------------------------
-- _⊙_ and return form an applicative functor

module ApplicativeFunctor where

  open ⊙ using (_⊙′_)

  identity-⊛ : ∀ {Tok R xs} (p : ∞? (Parser Tok R xs) [ id ]) →
               ♯? (return id) ⊛ p ≈ ♭? p
  identity-⊛ {Tok} {R} {xs} p =
    equivalent helper (λ x∈p → ♭♯.add xs return ⊛ x∈p)
    where
    helper : ♯? (return id) ⊛ p ⊑ ♭? p
    helper (∈ret ⊛ ∈p) with ♭♯.drop xs ∈ret
    ... | return = ∈p

  identity : ∀ {Tok R xs} (p : Parser Tok R xs) → return id ⊙ p ≈ p
  identity p = identity-⊛ (♯? p)

  composition :
    ∀ {Tok R₁ R₂ R₃ fs gs xs}
    (p₁ : Parser Tok (R₂ → R₃) fs)
    (p₂ : Parser Tok (R₁ → R₂) gs)
    (p₃ : Parser Tok R₁        xs) →
    return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃ ≈ p₁ ⊙ (p₂ ⊙ p₃)
  composition {fs = fs} {gs} {xs} p₁ p₂ p₃ = equivalent helper₁ helper₂
    where
    helper₁ : return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃ ⊑ p₁ ⊙ (p₂ ⊙ p₃)
    helper₁ ∈⊙⊙⊙ with ⊙.sound xs ∈⊙⊙⊙
    ... | ∈⊙⊙ ⊙′ ∈p₃ with ⊙.sound gs ∈⊙⊙
    ... | ∈⊙  ⊙′ ∈p₂ with ⊙.sound {fs = [ _∘′_ ]} fs ∈⊙
    ... | _⊙′_ {s₂ = s₁} return ∈p₁ =
      cast∈ P.refl P.refl (P.sym $ ListMonoid.assoc s₁ _ _) $
        ⊙.complete ∈p₁ (⊙.complete ∈p₂ ∈p₃)

    helper₂ : p₁ ⊙ (p₂ ⊙ p₃) ⊑ return _∘′_ ⊙ p₁ ⊙ p₂ ⊙ p₃
    helper₂ ∈⊙⊙ with ⊙.sound (gs ⊛′ xs) ∈⊙⊙
    ... | _⊙′_ {s₁ = s₁} ∈p₁ ∈⊙ with ⊙.sound xs ∈⊙
    ... | ∈p₂ ⊙′ ∈p₃ =
      cast∈ P.refl P.refl (ListMonoid.assoc s₁ _ _) $
        ⊙.complete (⊙.complete (⊙.complete return ∈p₁) ∈p₂) ∈p₃

  homomorphism : ∀ {Tok R₁ R₂} (f : R₁ → R₂) (x : R₁) →
                 return f ⊙ return x ≈ return {Tok = Tok} (f x)
  homomorphism {Tok} f x = equivalent helper₁ helper₂
    where
    helper₁ : return f ⊙ return x ⊑ return {Tok = Tok} (f x)
    helper₁ (return ⊛ return) = return

    helper₂ : return {Tok = Tok} (f x) ⊑ return f ⊙ return x
    helper₂ return = return {x = f} ⊛ return

  interchange : ∀ {Tok R₁ R₂ fs}
                (p : Parser Tok (R₁ → R₂) fs) (x : R₁) →
                p ⊙ return x ≈ return (λ f → f x) ⊙ p
  interchange {fs = fs} p x = equivalent helper₁ helper₂
    where
    helper₁ : p ⊙ return x ⊑ return (λ f → f x) ⊙ p
    helper₁ ∈⊙ret with ⊙.sound {fs = fs} [ x ] ∈⊙ret
    ... | ∈p ⊙′ return =
      cast∈ P.refl P.refl (P.sym $ proj₂ ListMonoid.identity _) $
        ⊙.complete return ∈p

    helper₂ : return (λ f → f x) ⊙ p ⊑ p ⊙ return x
    helper₂ ∈ret⊙ with ⊙.sound {fs = [ (λ f → f x) ]} fs ∈ret⊙
    ... | return ⊙′ ∈p =
      cast∈ P.refl P.refl (proj₂ ListMonoid.identity _) $
        ⊙.complete ∈p return

------------------------------------------------------------------------
-- _⟫=_ and return form a monad

module Monad where

  open ⟫= using (_⟫=′_)

  left-identity->>= : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                      (x : R₁)
                      (p : (y : R₁) → ∞? (Parser Tok R₂ (f y)) [ x ]) →
                      return x >>= p ≈ ♭? (p x)
  left-identity->>= x p = equivalent helper (_>>=_ {p₂ = p} return)
    where
    helper : return x >>= p ⊑ ♭? (p x)
    helper (return >>= ∈px) = ∈px

  left-identity : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                  (x : R₁) (p : (x : R₁) → Parser Tok R₂ (f x)) →
                  return x ⟫= p ≈ p x
  left-identity x p = left-identity->>= x (λ x → ♯? (p x))

  right-identity : ∀ {Tok R xs} (p : Parser Tok R xs) → p ⟫= return ≈ p
  right-identity {xs = xs} p =
    equivalent
      helper
      (λ ∈p → cast∈ P.refl P.refl (proj₂ ListMonoid.identity _) $
                ⟫=.complete ∈p return)
    where
    helper : p ⟫= return ⊑ p
    helper ∈⟫=ret with ⟫=.sound xs ∈⟫=ret
    ... | ∈p ⟫=′ return =
      cast∈ P.refl P.refl (P.sym $ proj₂ ListMonoid.identity _) ∈p

  associative : ∀ {Tok R₁ R₂ R₃ xs}
                  {f : R₁ → List R₂} {g : R₂ → List R₃}
                (p₁ : Parser Tok R₁ xs)
                (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                (p₃ : (x : R₂) → Parser Tok R₃ (g x)) →
                (p₁ ⟫= λ x → p₂ x ⟫= p₃) ≈ p₁ ⟫= p₂ ⟫= p₃
  associative {xs = xs} {f} p₁ p₂ p₃ = equivalent helper₁ helper₂
    where
    helper₁ : (p₁ ⟫= λ x → p₂ x ⟫= p₃) ⊑ p₁ ⟫= p₂ ⟫= p₃
    helper₁ ∈⟫=⟫= with ⟫=.sound xs ∈⟫=⟫=
    ... | _⟫=′_ {x = x} {s₁ = s₁} ∈p₁ ∈⟫= with ⟫=.sound (f x) ∈⟫=
    ... | ∈p₂x ⟫=′ ∈p₃ =
      cast∈ P.refl P.refl (ListMonoid.assoc s₁ _ _) $
        ⟫=.complete (⟫=.complete ∈p₁ ∈p₂x) ∈p₃

    helper₂ : p₁ ⟫= p₂ ⟫= p₃ ⊑ (p₁ ⟫= λ x → p₂ x ⟫= p₃)
    helper₂ ∈⟫=⟫= with ⟫=.sound (xs >>=′ f) ∈⟫=⟫=
    ... | ∈⟫= ⟫=′ ∈p₃ with ⟫=.sound xs ∈⟫=
    ... | _⟫=′_ {s₁ = s₁} ∈p₁ ∈p₂ =
      cast∈ P.refl P.refl (P.sym $ ListMonoid.assoc s₁ _ _) $
        ⟫=.complete ∈p₁ (⟫=.complete ∈p₂ ∈p₃)

------------------------------------------------------------------------
-- fail is a zero for _⊙_ and _⟫=_, and both _⊙_ and _⟫=_ distribute
-- over _∣_

-- Together with the laws above this means that we have something
-- which resembles an idempotent semiring (both for _⊙_ and for _⟫=_).

module ⊙-IdempotentSemiring where

  open AdditiveMonoid     public
  open ApplicativeFunctor public
  open ⊙ using (_⊙′_)

  left-zero-⊛ : ∀ {Tok R₁ R₂ xs} (p : ∞? (Parser Tok R₁ xs) []) →
                ♯? fail ⊛ p ≈ fail {R = R₂}
  left-zero-⊛ {Tok} {R₁} {R₂} {xs} p = equivalent helper (λ ())
    where
    helper : ♯? fail ⊛ p ⊑ fail {R = R₂}
    helper (∈fail ⊛ _)
      rewrite ♭?♯? xs {fail {Tok = Tok} {R = R₁ → R₂}}
        with ∈fail
    ... | ()

  left-zero : ∀ {Tok R₁ R₂ xs} (p : Parser Tok R₁ xs) →
              fail ⊙ p ≈ fail {R = R₂}
  left-zero p = left-zero-⊛ (♯? p)

  right-zero-⊛ : ∀ {Tok R₁ R₂ fs} (p : ∞? (Parser Tok (R₁ → R₂) fs) []) →
                 p ⊛ ♯? fail ≈ fail
  right-zero-⊛ {Tok} {R₁} {fs = fs} p = equivalent helper (λ ())
    where
    helper : p ⊛ ♯? fail ⊑ fail
    helper (_ ⊛ ∈fail)
      rewrite ♭?♯? fs {fail {Tok = Tok} {R = R₁}}
        with ∈fail
    ... | ()

  right-zero : ∀ {Tok R₁ R₂ fs} (p : Parser Tok (R₁ → R₂) fs) →
               p ⊙ fail ≈ fail
  right-zero p = right-zero-⊛ (♯? p)

  left-distributive : ∀ {Tok R₁ R₂ fs xs₁ xs₂}
                      (p₁ : Parser Tok (R₁ → R₂) fs)
                      (p₂ : Parser Tok R₁ xs₁)
                      (p₃ : Parser Tok R₁ xs₂) →
                      p₁ ⊙ (p₂ ∣ p₃) ≈ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
  left-distributive {fs = fs} {xs₁} {xs₂} p₁ p₂ p₃ =
    equivalent helper₁ helper₂
    where
    helper₁ : p₁ ⊙ (p₂ ∣ p₃) ⊑ p₁ ⊙ p₂ ∣ p₁ ⊙ p₃
    helper₁ ∈⊙∣ with ⊙.sound (xs₁ ++ xs₂) ∈⊙∣
    ... | ∈p₁ ⊙′ ∣ˡ      ∈p₂ = ∣ˡ             (⊙.complete ∈p₁ ∈p₂)
    ... | ∈p₁ ⊙′ ∣ʳ .xs₁ ∈p₃ = ∣ʳ (fs ⊛′ xs₁) (⊙.complete ∈p₁ ∈p₃)

    helper₂ : p₁ ⊙ p₂ ∣ p₁ ⊙ p₃ ⊑ p₁ ⊙ (p₂ ∣ p₃)
    helper₂ (∣ˡ ∈⊙) with ⊙.sound xs₁ ∈⊙
    ... | ∈p₁ ⊙′ ∈p₂ = ⊙.complete ∈p₁ (∣ˡ ∈p₂)
    helper₂ (∣ʳ .(fs ⊛′ xs₁) ∈⊙) with ⊙.sound xs₂ ∈⊙
    ... | ∈p₁ ⊙′ ∈p₃ = ⊙.complete ∈p₁ (∣ʳ xs₁ ∈p₃)

  right-distributive : ∀ {Tok R₁ R₂ fs₁ fs₂ xs}
                       (p₁ : Parser Tok (R₁ → R₂) fs₁)
                       (p₂ : Parser Tok (R₁ → R₂) fs₂)
                       (p₃ : Parser Tok R₁ xs) →
                       (p₁ ∣ p₂) ⊙ p₃ ≈ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
  right-distributive {fs₁ = fs₁} {fs₂} {xs} p₁ p₂ p₃ =
    equivalent helper₁ helper₂
    where
    helper₁ : (p₁ ∣ p₂) ⊙ p₃ ⊑ p₁ ⊙ p₃ ∣ p₂ ⊙ p₃
    helper₁ ∈∣⊙ with ⊙.sound xs ∈∣⊙
    ... | ∣ˡ      ∈p₁ ⊙′ ∈p₃ = ∣ˡ             (⊙.complete ∈p₁ ∈p₃)
    ... | ∣ʳ .fs₁ ∈p₂ ⊙′ ∈p₃ = ∣ʳ (fs₁ ⊛′ xs) (⊙.complete ∈p₂ ∈p₃)

    helper₂ : p₁ ⊙ p₃ ∣ p₂ ⊙ p₃ ⊑ (p₁ ∣ p₂) ⊙ p₃
    helper₂ (∣ˡ ∈⊙) with ⊙.sound xs ∈⊙
    ... | ∈p₁ ⊙′ ∈p₃ = ⊙.complete (∣ˡ ∈p₁) ∈p₃
    helper₂ (∣ʳ .(fs₁ ⊛′ xs) ∈⊙) with ⊙.sound xs ∈⊙
    ... | ∈p₂ ⊙′ ∈p₃ = ⊙.complete (∣ʳ fs₁ ∈p₂) ∈p₃

module ⟫=-IdempotentSemiring where

  open AdditiveMonoid public
    renaming ( associative    to ∣-associative
             ; left-identity  to ∣-left-identity
             ; right-identity to ∣-right-identity
             )
  open Monad public
    renaming ( associative    to ⟫=-associative
             ; left-identity  to ⟫=-left-identity
             ; right-identity to ⟫=-right-identity
             )
  open ⟫= using (_⟫=′_)

  left-zero->>= : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
                  (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) []) →
                  fail >>= p ≈ fail
  left-zero->>= {f = f} p = equivalent helper (λ ())
    where
    helper : fail >>= p ⊑ fail
    helper (() >>= _)

  left-zero : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
              (p : (x : R₁) → Parser Tok R₂ (f x)) → fail ⟫= p ≈ fail
  left-zero p = left-zero->>= (λ x → ♯? (p x))

  right-zero : ∀ {Tok R₁ R₂ xs}
               (p : Parser Tok R₁ xs) → p ⟫= const fail ≈ fail {R = R₂}
  right-zero {R₂ = R₂} {xs} p = equivalent helper (λ ())
    where
    helper : p ⟫= const fail ⊑ fail {R = R₂}
    helper ∈⟫= with ⟫=.sound xs ∈⟫=
    ... | _ ⟫=′ ()

  left-distributive : ∀ {Tok R₁ R₂ xs} {f g : R₁ → List R₂}
                      (p₁ : Parser Tok R₁ xs)
                      (p₂ : (x : R₁) → Parser Tok R₂ (f x))
                      (p₃ : (x : R₁) → Parser Tok R₂ (g x)) →
                      p₁ ⟫= (λ x → p₂ x ∣ p₃ x) ≈ p₁ ⟫= p₂ ∣ p₁ ⟫= p₃
  left-distributive {xs = xs} {f} {g} p₁ p₂ p₃ =
    equivalent helper₁ helper₂
    where
    helper₁ : p₁ ⟫= (λ x → p₂ x ∣ p₃ x) ⊑ p₁ ⟫= p₂ ∣ p₁ ⟫= p₃
    helper₁ ∈⟫=∣ with ⟫=.sound xs ∈⟫=∣
    ... | ∈p₁ ⟫=′ ∣ˡ    ∈p₂ = ∣ˡ             (⟫=.complete ∈p₁ ∈p₂)
    ... | ∈p₁ ⟫=′ ∣ʳ ._ ∈p₃ = ∣ʳ (xs >>=′ f) (⟫=.complete ∈p₁ ∈p₃)

    helper₂ : p₁ ⟫= p₂ ∣ p₁ ⟫= p₃ ⊑ p₁ ⟫= (λ x → p₂ x ∣ p₃ x)
    helper₂ (∣ˡ ∈⟫=) with ⟫=.sound xs ∈⟫=
    ... | ∈p₁ ⟫=′ ∈p₂ = ⟫=.complete ∈p₁ (∣ˡ ∈p₂)
    helper₂ (∣ʳ .(xs >>=′ f) ∈⟫=) with ⟫=.sound xs ∈⟫=
    ... | ∈p₁ ⟫=′ ∈p₃ = ⟫=.complete ∈p₁ (∣ʳ (f _) ∈p₃)

  right-distributive : ∀ {Tok R₁ R₂ xs₁ xs₂} {f : R₁ → List R₂}
                       (p₁ : Parser Tok R₁ xs₁)
                       (p₂ : Parser Tok R₁ xs₂)
                       (p₃ : (x : R₁) → Parser Tok R₂ (f x)) →
                       (p₁ ∣ p₂) ⟫= p₃ ≈ p₁ ⟫= p₃ ∣ p₂ ⟫= p₃
  right-distributive {xs₁ = xs₁} {xs₂} {f} p₁ p₂ p₃ =
    equivalent helper₁ helper₂
    where
    helper₁ : (p₁ ∣ p₂) ⟫= p₃ ⊑ p₁ ⟫= p₃ ∣ p₂ ⟫= p₃
    helper₁ ∈∣⟫= with ⟫=.sound (xs₁ ++ xs₂) ∈∣⟫=
    ... | ∣ˡ      ∈p₁ ⟫=′ ∈p₃ = ∣ˡ              (⟫=.complete ∈p₁ ∈p₃)
    ... | ∣ʳ .xs₁ ∈p₂ ⟫=′ ∈p₃ = ∣ʳ (xs₁ >>=′ f) (⟫=.complete ∈p₂ ∈p₃)

    helper₂ : p₁ ⟫= p₃ ∣ p₂ ⟫= p₃ ⊑ (p₁ ∣ p₂) ⟫= p₃
    helper₂ (∣ˡ ∈⟫=) with ⟫=.sound xs₁ ∈⟫=
    ... | ∈p₁ ⟫=′ ∈p₃ = ⟫=.complete (∣ˡ ∈p₁) ∈p₃
    helper₂ (∣ʳ .(xs₁ >>=′ f) ∈⟫=) with ⟫=.sound xs₂ ∈⟫=
    ... | ∈p₂ ⟫=′ ∈p₃ = ⟫=.complete (∣ʳ xs₁ ∈p₂) ∈p₃

------------------------------------------------------------------------
-- A limited notion of *-continuity

module *-Continuity where

  open ⊙ using (_⊙′_)

  -- For argument parsers which are not nullable we can prove that the
  -- Kleene star operator is *-continuous.

  upper-bound : ∀ {Tok R₁ R₂ R₃ fs xs}
                (p₁ : Parser Tok (List R₁ → R₂ → R₃) fs)
                (p₂ : Parser Tok R₁ [])
                (p₃ : Parser Tok R₂ xs) →
    ∀ n → p₁ ⊙ p₂ ↑ n ⊙ p₃ ⊑ p₁ ⊙ p₂ ⋆ ⊙ p₃
  upper-bound {R₁ = R₁} {fs = fs} {xs} _ _ _ n ∈⊙ⁿ⊙
    with ⊙.sound xs ∈⊙ⁿ⊙
  ... | ∈⊙ⁿ ⊙′ ∈p₃ with ⊙.sound (↑-initial [] n) ∈⊙ⁿ
  ... | ∈p₁ ⊙′ ∈p₂ⁿ =
    ⊙.complete (⊙.complete ∈p₁ (Exactly.↑⊑⋆ n ∈p₂ⁿ)) ∈p₃

  least-upper-bound : ∀ {Tok R₁ R₂ R₃ fs xs₃ xs}
                      (p₁ : Parser Tok (List R₁ → R₂ → R₃) fs)
                      (p₂ : Parser Tok R₁ [])
                      (p₃ : Parser Tok R₂ xs₃)
                      (p  : Parser Tok R₃ xs) →
    (∀ i → p₁ ⊙ p₂ ↑ i ⊙ p₃ ⊑ p) → p₁ ⊙ p₂ ⋆ ⊙ p₃ ⊑ p
  least-upper-bound {R₁ = R₁} {fs = fs} {xs₃} {xs} _ _ _ _ ub ∈⊙⋆⊙
    with ⊙.sound xs₃ ∈⊙⋆⊙
  ... | ∈⊙⋆ ⊙′ ∈p₃ with ⊙.sound {fs = fs} [ [] ] ∈⊙⋆
  ... | ∈p₁ ⊙′ ∈p₂⋆ with Exactly.⋆⊑∃↑ ∈p₂⋆
  ... | (n , ∈p₂ⁿ) = ub n (⊙.complete (⊙.complete ∈p₁ ∈p₂ⁿ) ∈p₃)

  -- However, if we allow arbitrary argument parsers, then we cannot
  -- even prove the following (variant of a) Kleene algebra axiom.

  not-Kleene-algebra :
    (f : ∀ {Tok R xs} → Parser Tok R xs → List (List R)) →
    (_⋆′ : ∀ {Tok R xs} (p : Parser Tok R xs) →
           Parser Tok (List R) (f p)) →
    ¬ (∀ {Tok R xs} {p : Parser Tok R xs} →
       return [] ∣ _∷_ <$> p ⊙ (p ⋆′) ⊑ (p ⋆′))
  not-Kleene-algebra f _⋆′ fold =
    KleeneStar.unrestricted-incomplete tt f _⋆′ ⋆′-complete
    where
    ⋆′-complete : ∀ {xs ys s} {p : Parser ⊤ ⊤ ys} →
                  xs ∈[ p ]⋆· s → xs ∈ p ⋆′ · s
    ⋆′-complete                   []         = fold (∣ˡ return)
    ⋆′-complete {ys = ys} {p = p} (∈p ∷ ∈p⋆) =
      fold (∣ʳ [ [] ] (⊙.complete (<$> ∈p) (⋆′-complete ∈p⋆)))

  -- This shows that the parser combinators do not form a Kleene
  -- algebra (interpreted liberally) using _⊙_ for composition, return
  -- for unit, etc. However, it should be straightforward to build a
  -- recogniser library, based on the parser combinators, which does
  -- satisfy the Kleene algebra axioms (see
  -- TotalRecognisers.LeftRecursion.KleeneAlgebra).
