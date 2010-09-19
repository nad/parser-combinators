------------------------------------------------------------------------
-- Laws related to _⊛_ and return
------------------------------------------------------------------------

module TotalParserCombinators.Laws.ApplicativeFunctor where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any.BagAndSetEquality as BSEq
open import Function

open RawMonad List.monad
  using () renaming (_⊛_ to _⊛′_; _>>=_ to _>>=′_)
private
  module BagMonoid {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid _ A)

open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.Congruence
  hiding (return; fail) renaming (_∣_ to _∣′_)
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative as Derivative
import TotalParserCombinators.Laws.Monad as Monad
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

------------------------------------------------------------------------
-- _⊛_, return, _∣_ and fail form an applicative functor "with a zero
-- and a plus"

-- Together with the additive monoid laws we get something which
-- resembles an idempotent semiring (if we restrict ourselves to
-- language equivalence).

-- First note that _⊛_ can be defined using _>>=_.

private

  -- A variant of "flip map".

  pam : ∀ {Tok R₁ R₂ xs} →
        Parser Tok R₁ xs → (f : R₁ → R₂) →
        Parser Tok R₂ (xs >>=′ [_] ∘ f)
  pam p f = p >>= (return ∘ f)

  infixl 10 _⊛″_

  -- Note that this definition forces the argument parsers.

  _⊛″_ : ∀ {Tok R₁ R₂ fs xs} →
         ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs)               →
         ∞⟨ fs ⟩Parser Tok  R₁                     (flatten xs) →
                Parser Tok       R₂  (flatten fs ⊛′ flatten xs)
  p₁ ⊛″ p₂ = ♭? p₁ >>= pam (♭? p₂)

⊛-in-terms-of->>= :
  ∀ {Tok R₁ R₂ fs xs}
  (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs)            )
  (p₂ : ∞⟨ fs ⟩Parser Tok  R₁                   (flatten xs)) →
  p₁ ⊛ p₂ ≅P p₁ ⊛″ p₂
⊛-in-terms-of->>= {R₁ = R₁} {R₂} {fs} {xs} p₁ p₂ =
  BagMonoid.reflexive (Claims.⊛flatten-⊛-flatten (flatten fs) xs) ∷ λ t → ♯ (
    D t (p₁ ⊛ p₂)                                         ≅⟨ D-⊛ p₁ p₂ ⟩

    D t (♭? p₁) ⊛ ♭? p₂ ∣
    return⋆ (flatten fs) ⊛ D t (♭? p₂)                    ≅⟨ ⊛-in-terms-of->>= (D t (♭? p₁)) (♭? p₂) ∣′
                                                             ⊛-in-terms-of->>= (return⋆ (flatten fs)) (D t (♭? p₂)) ⟩
    D t (♭? p₁) ⊛″ ♭? p₂ ∣
    return⋆ (flatten fs) ⊛″ D t (♭? p₂)                   ≅⟨ (D t (♭? p₁) ⊛″ ♭? p₂ ∎) ∣′
                                                             ([ ○ - ○ - ○ - ○ ] return⋆ (flatten fs) ∎ >>= λ f →
                                                                                sym $ lemma t f) ⟩
    D t (♭? p₁) >>= pam (♭? p₂) ∣
    return⋆ (flatten fs) >>= (λ f → D t (pam (♭? p₂) f))  ≅⟨ sym $ D->>= (♭? p₁) (pam (♭? p₂)) ⟩

    D t (♭? p₁ >>= pam (♭? p₂))                           ∎)
  where
  lemma : ∀ t (f : R₁ → R₂) →
          D t (♭? p₂ >>= λ x → return (f x)) ≅P
          D t (♭? p₂) >>= λ x → return (f x)
  lemma t f =
    D t (pam (♭? p₂) f)                    ≅⟨ D->>= (♭? p₂) (return ∘ f) ⟩

    pam (D t (♭? p₂)) f ∣
    (return⋆ (flatten xs) >>= λ _ → fail)  ≅⟨ (pam (D t (♭? p₂)) f ∎) ∣′
                                              Monad.right-zero (return⋆ (flatten xs)) ⟩
    pam (D t (♭? p₂)) f ∣ fail             ≅⟨ AdditiveMonoid.right-identity (pam (D t (♭? p₂)) f) ⟩
    pam (D t (♭? p₂)) f                    ∎

-- We can then reduce all the laws to corresponding laws for _>>=_.

-- The zero laws have already been proved.

open Derivative public
  using () renaming (left-zero-⊛  to left-zero;
                     right-zero-⊛ to right-zero)

-- _⊛_ distributes from the left over _∣_.

left-distributive : ∀ {Tok R₁ R₂ fs xs₁ xs₂}
                    (p₁ : Parser Tok (R₁ → R₂) fs)
                    (p₂ : Parser Tok R₁ xs₁)
                    (p₃ : Parser Tok R₁ xs₂) →
                    p₁ ⊛ (p₂ ∣ p₃) ≅P p₁ ⊛ p₂ ∣ p₁ ⊛ p₃
left-distributive p₁ p₂ p₃ =
  p₁ ⊛  (p₂ ∣ p₃)                     ≅⟨ ⊛-in-terms-of->>= p₁ (p₂ ∣ p₃) ⟩
  p₁ ⊛″ (p₂ ∣ p₃)                     ≅⟨ ([ ○ - ○ - ○ - ○ ] p₁ ∎ >>= λ f →
                                            Monad.right-distributive p₂ p₃ (return ∘ f)) ⟩
  (p₁ >>= λ f → pam p₂ f ∣ pam p₃ f)  ≅⟨ Monad.left-distributive p₁ (pam p₂) (pam p₃) ⟩
  p₁ ⊛″ p₂ ∣ p₁ ⊛″ p₃                 ≅⟨ sym $ ⊛-in-terms-of->>= p₁ p₂ ∣′
                                               ⊛-in-terms-of->>= p₁ p₃ ⟩
  p₁ ⊛  p₂ ∣ p₁ ⊛  p₃                 ∎

-- _⊛_ distributes from the right over _∣_.

right-distributive : ∀ {Tok R₁ R₂ fs₁ fs₂ xs}
                     (p₁ : Parser Tok (R₁ → R₂) fs₁)
                     (p₂ : Parser Tok (R₁ → R₂) fs₂)
                     (p₃ : Parser Tok R₁ xs) →
                     (p₁ ∣ p₂) ⊛ p₃ ≅P p₁ ⊛ p₃ ∣ p₂ ⊛ p₃
right-distributive p₁ p₂ p₃ =
  (p₁ ∣ p₂) ⊛  p₃      ≅⟨ ⊛-in-terms-of->>= (p₁ ∣ p₂) p₃ ⟩
  (p₁ ∣ p₂) ⊛″ p₃      ≅⟨ Monad.right-distributive p₁ p₂ (pam p₃) ⟩
  p₁ ⊛″ p₃ ∣ p₂ ⊛″ p₃  ≅⟨ sym $ ⊛-in-terms-of->>= p₁ p₃ ∣′
                                ⊛-in-terms-of->>= p₂ p₃ ⟩
  p₁ ⊛  p₃ ∣ p₂ ⊛  p₃  ∎

-- Applicative functor laws.

identity : ∀ {Tok R xs} (p : Parser Tok R xs) → return id ⊛ p ≅P p
identity p =
  return id ⊛  p  ≅⟨ ⊛-in-terms-of->>= (return id) p ⟩
  return id ⊛″ p  ≅⟨ Monad.left-identity id (pam p) ⟩
  p >>= return    ≅⟨ Monad.right-identity p ⟩
  p               ∎

homomorphism : ∀ {Tok R₁ R₂} (f : R₁ → R₂) (x : R₁) →
               return f ⊛ return x ≅P return {Tok = Tok} (f x)
homomorphism f x =
  return f ⊛  return x  ≅⟨ ⊛-in-terms-of->>= (return f) (return x) ⟩
  return f ⊛″ return x  ≅⟨ Monad.left-identity f (pam (return x)) ⟩
  pam (return x) f      ≅⟨ Monad.left-identity x (return ∘ f) ⟩
  return (f x)          ∎

private

  infixl 10 _⊛-cong_

  _⊛-cong_ :
    ∀ {k Tok R₁ R₂ xs₁ xs₂ fs₁ fs₂}
      {p₁ : Parser Tok (R₁ → R₂) fs₁} {p₂ : Parser Tok R₁ xs₁}
      {p₃ : Parser Tok (R₁ → R₂) fs₂} {p₄ : Parser Tok R₁ xs₂} →
    p₁ ≈[ k ]P p₃ → p₂ ≈[ k ]P p₄ → p₁ ⊛″ p₂ ≈[ k ]P p₃ ⊛″ p₄
  _⊛-cong_ {p₁ = p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄ =
    p₁ ⊛″ p₂  ≅⟨ sym $ ⊛-in-terms-of->>= p₁ p₂ ⟩
    p₁ ⊛  p₂  ≈⟨ [ ○ - ○ - ○ - ○ ] p₁≈p₃ ⊛ p₂≈p₄ ⟩
    p₃ ⊛  p₄  ≅⟨ ⊛-in-terms-of->>= p₃ p₄ ⟩
    p₃ ⊛″ p₄  ∎

  pam-lemma : ∀ {Tok R₁ R₂ R₃ xs} {g : R₂ → List R₃}
              (p₁ : Parser Tok R₁ xs) (f : R₁ → R₂)
              (p₂ : (x : R₂) → Parser Tok R₃ (g x)) →
              pam p₁ f >>= p₂ ≅P p₁ >>= λ x → p₂ (f x)
  pam-lemma p₁ f p₂ =
    pam p₁ f >>= p₂                     ≅⟨ sym $ Monad.associative p₁ (return ∘ f) p₂ ⟩
    (p₁ >>= λ x → return (f x) >>= p₂)  ≅⟨ ([ ○ - ○ - ○ - ○ ] p₁ ∎ >>= λ x →
                                              Monad.left-identity (f x) p₂) ⟩
    (p₁ >>= λ x → p₂ (f x))             ∎

composition :
  ∀ {Tok R₁ R₂ R₃ fs gs xs}
  (p₁ : Parser Tok (R₂ → R₃) fs)
  (p₂ : Parser Tok (R₁ → R₂) gs)
  (p₃ : Parser Tok R₁        xs) →
  return _∘′_ ⊛ p₁ ⊛ p₂ ⊛ p₃ ≅P p₁ ⊛ (p₂ ⊛ p₃)
composition p₁ p₂ p₃ =
  return _∘′_ ⊛  p₁ ⊛  p₂ ⊛  p₃                   ≅⟨ ⊛-in-terms-of->>= (return _∘′_ ⊛ p₁ ⊛ p₂) p₃ ⟩
  return _∘′_ ⊛  p₁ ⊛  p₂ ⊛″ p₃                   ≅⟨ ⊛-in-terms-of->>= (return _∘′_ ⊛ p₁) p₂ ⊛-cong (p₃ ∎) ⟩
  return _∘′_ ⊛  p₁ ⊛″ p₂ ⊛″ p₃                   ≅⟨ ⊛-in-terms-of->>= (return _∘′_) p₁ ⊛-cong (p₂ ∎) ⊛-cong (p₃ ∎) ⟩
  return _∘′_ ⊛″ p₁ ⊛″ p₂ ⊛″ p₃                   ≅⟨ Monad.left-identity _∘′_ (pam p₁) ⊛-cong (p₂ ∎) ⊛-cong (p₃ ∎) ⟩
  pam p₁ _∘′_ ⊛″ p₂ ⊛″ p₃                         ≅⟨ pam-lemma p₁ _∘′_ (pam p₂) ⊛-cong (p₃ ∎) ⟩
  ((p₁ >>= λ f → pam p₂ (_∘′_ f)) ⊛″ p₃)          ≅⟨ sym $ Monad.associative p₁ (λ f → pam p₂ (_∘′_ f)) (pam p₃) ⟩
  (p₁ >>= λ f → pam p₂ (_∘′_ f) >>= pam p₃)       ≅⟨ ([ ○ - ○ - ○ - ○ ] p₁ ∎ >>= λ f →
                                                      pam-lemma p₂ (_∘′_ f) (pam p₃)) ⟩
  (p₁ >>= λ f → p₂ >>= λ g → pam p₃ (f ∘′ g))     ≅⟨ ([ ○ - ○ - ○ - ○ ] p₁ ∎ >>= λ f →
                                                      [ ○ - ○ - ○ - ○ ] p₂ ∎ >>= λ g →
                                                      sym $ pam-lemma p₃ g (return ∘ f)) ⟩
  (p₁ >>= λ f → p₂ >>= λ g → pam (pam p₃ g) f)    ≅⟨ ([ ○ - ○ - ○ - ○ ] p₁ ∎ >>= λ f →
                                                      Monad.associative p₂ (pam p₃) (return ∘ f)) ⟩
  p₁ ⊛″ (p₂ ⊛″ p₃)                                ≅⟨ sym $ (p₁ ∎) ⊛-cong ⊛-in-terms-of->>= p₂ p₃ ⟩
  p₁ ⊛″ (p₂ ⊛  p₃)                                ≅⟨ sym $ ⊛-in-terms-of->>= p₁ (p₂ ⊛ p₃) ⟩
  p₁ ⊛  (p₂ ⊛  p₃)                                ∎

interchange : ∀ {Tok R₁ R₂ fs}
              (p : Parser Tok (R₁ → R₂) fs) (x : R₁) →
              p ⊛ return x ≅P return (λ f → f x) ⊛ p
interchange p x =
  p ⊛  return x               ≅⟨ ⊛-in-terms-of->>= p (return x) ⟩
  p ⊛″ return x               ≅⟨ ([ ○ - ○ - ○ - ○ ] p ∎ >>= λ f →
                                    Monad.left-identity x (return ∘ f)) ⟩
  (p >>= λ f → return (f x))  ≅⟨ pam p (λ f → f x) ∎ ⟩
  pam p (λ f → f x)           ≅⟨ sym $ Monad.left-identity (λ f → f x) (pam p) ⟩
  return (λ f → f x) ⊛″ p     ≅⟨ sym $ ⊛-in-terms-of->>= (return (λ f → f x)) p ⟩
  return (λ f → f x) ⊛  p     ∎
