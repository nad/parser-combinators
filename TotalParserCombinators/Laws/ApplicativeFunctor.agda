------------------------------------------------------------------------
-- Laws related to _⊛_, _<$>_ and return
------------------------------------------------------------------------

module TotalParserCombinators.Laws.ApplicativeFunctor where

open import Algebra
open import Codata.Musical.Notation
open import Data.List as List
import Data.List.Effectful
import Data.List.Properties as L
import Data.List.Relation.Binary.BagAndSetEquality as BSEq
open import Effect.Monad
open import Function
import Level
open import Relation.Binary.PropositionalEquality
  using (module ≡-Reasoning)

open RawMonad {f = Level.zero} Data.List.Effectful.monad
  using ()
  renaming (pure to return′;
            _<$>_ to _<$>′_; _⊛_ to _⊛′_; _>>=_ to _>>=′_)
private
  module BagMonoid {k} {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid k A)

open import TotalParserCombinators.Derivative
open import TotalParserCombinators.Congruence
  hiding (return; fail) renaming (_∣_ to _∣′_)
import TotalParserCombinators.Laws.AdditiveMonoid as AdditiveMonoid
open import TotalParserCombinators.Laws.Derivative as Derivative
import TotalParserCombinators.Laws.Monad as Monad
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

private variable
  Tok R R₁ R₂ R₃ : Set
  xs xs₁         : List R
  p p₁ p₂        : Parser Tok R xs
  x              : R
  f g            : R₁ → R₂

------------------------------------------------------------------------
-- Some lemmas related to _<$>_

module <$> where

  -- Functor laws (expressed in a certain way).

  identity : id <$> p ≅P p
  identity {p = p} =
    BagMonoid.reflexive (L.map-id _) ∷ λ t → ♯ (
      id <$> D t p  ≅⟨ identity ⟩
      D t p         ∎)

  composition : (f ∘ g) <$> p ≅P f <$> (g <$> p)
  composition {f = f} {g = g} {p = p} =
    BagMonoid.reflexive (L.map-∘ _) ∷ λ t → ♯ (
      (f ∘ g) <$> D t p    ≅⟨ composition ⟩
      f <$> (g <$> D t p)  ∎)

  -- The fail combinator is a right zero for _<$>_.

  zero : f <$> fail ≅P fail {Tok = Tok}
  zero {f = f} =
    BagMonoid.refl ∷ λ _ → ♯ (
      f <$> fail  ≅⟨ zero ⟩
      fail        ∎)

  -- A variant of the lemma homomorphism which is defined below.

  homomorphism : f <$> return x ≅P return {Tok = Tok} (f x)
  homomorphism {f = f} {x = x} =
    BagMonoid.refl ∷ λ _ → ♯ (
      f <$> fail  ≅⟨ zero ⟩
      fail        ∎)

  -- The combinator _<$>_ distributes from the left over _∣_.

  left-distributive :
    {p₁ : Parser Tok R₁ xs₁} →
    f <$> (p₁ ∣ p₂) ≅P f <$> p₁ ∣ f <$> p₂
  left-distributive {xs₁ = xs₁} {f = f} {p₂ = p₂} {p₁ = p₁} =
    BagMonoid.reflexive (L.map-++ _ xs₁ _) ∷ λ t → ♯ (
      f <$> (D t p₁ ∣ D t p₂)      ≅⟨ left-distributive ⟩
      f <$> D t p₁ ∣ f <$> D t p₂  ∎)

  -- The combinator _<$>_ can be expressed using _>>=_ and return.

  in-terms-of->>= :
    {p : Parser Tok R₁ xs} →
    f <$> p ≅P p >>= (return ∘ f)
  in-terms-of->>= {xs = xs} {f = f} {p = p} =
    BagMonoid.reflexive lemma ∷ λ t → ♯ (
      f <$> D t p                                           ≅⟨ sym (AdditiveMonoid.right-identity _) ⟩
      f <$> D t p ∣ fail                                    ≅⟨ in-terms-of->>= ∣′ sym (Derivative.right-zero->>= _) ⟩
      D t p >>= (return ∘ f) ∣ return⋆ xs >>= (λ _ → fail)  ∎)
    where
    open Data.List.Effectful.Applicative
    open Data.List.Effectful.MonadProperties

    lemma =
      List.map f xs                               ≡-Reasoning.≡⟨ unfold-<$> _ _ ⟩
      return′ f ⊛′ xs                             ≡-Reasoning.≡⟨ unfold-⊛ (return′ _) _ ⟩
      (return′ f >>=′ λ f → xs >>=′ return′ ∘ f)  ≡-Reasoning.≡⟨ left-identity _ (λ f → xs >>=′ return′ ∘ f) ⟩
      (xs >>=′ return′ ∘ f)                       ≡-Reasoning.∎

  -- The combinator _<$>_ can be expressed using _⊛_ and return.

  in-terms-of-⊛ : f <$> p ≅P return f ⊛ p
  in-terms-of-⊛ {f = f} {p = p} =
    BagMonoid.sym (BagMonoid.identityʳ _) ∷ λ t → ♯ (
      f <$> D t p         ≅⟨ in-terms-of-⊛ ⟩
      return f ⊛ D t p    ≅⟨ sym $ D-return-⊛ f p ⟩
      D t (return f ⊛ p)  ∎)

  -- A lemma related to _<$>_ and _>>=_.

  >>=-∘ :
    {p₂ : (x : R₂) → Parser Tok R₃ (g x)} →
    p₁ >>= (p₂ ∘ f) ≅P f <$> p₁ >>= p₂
  >>=-∘ {p₁ = p₁} {f = f} {p₂ = p₂} =
    (p₁ >>= λ x → p₂ (f x))             ≅⟨ ([ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ → sym $ Monad.left-identity _ _) ⟩
    (p₁ >>= λ x → return (f x) >>= p₂)  ≅⟨ Monad.associative _ _ _ ⟩
    p₁ >>= (return ∘ f) >>= p₂          ≅⟨ ([ ○ - ○ - ○ - ○ ] sym in-terms-of->>= >>= λ _ → _ ∎) ⟩
    f <$> p₁ >>= p₂                     ∎

------------------------------------------------------------------------
-- _⊛_, return, _∣_ and fail form an applicative functor "with a zero
-- and a plus"

-- Together with the additive monoid laws we get something which
-- resembles an idempotent semiring (if we restrict ourselves to
-- language equivalence).

-- First note that _⊛_ can be defined using _>>=_ and _<$>_.

private

  -- A flipped variant of "map".

  pam : ∀ {Tok R₁ R₂ xs} →
        Parser Tok R₁ xs → (f : R₁ → R₂) →
        Parser Tok R₂ (f <$>′ xs)
  pam p f = f <$> p

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
    return⋆ (flatten fs) ⊛″ D t (♭? p₂)                   ≅⟨ _ ∎ ⟩

    D t (♭? p₁) >>= pam (♭? p₂) ∣
    return⋆ (flatten fs) >>= (λ f → D t (pam (♭? p₂) f))  ≅⟨ sym $ D->>= (♭? p₁) (pam (♭? p₂)) ⟩

    D t (♭? p₁ >>= pam (♭? p₂))                           ∎)

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
  p₁ ⊛″ (p₂ ∣ p₃)                     ≅⟨ ([ ○ - ○ - ○ - ○ ] p₁ ∎ >>= λ _ → <$>.left-distributive) ⟩
  (p₁ >>= λ f → f <$> p₂ ∣ f <$> p₃)  ≅⟨ Monad.left-distributive p₁ (pam p₂) (pam p₃) ⟩
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
  id <$> p        ≅⟨ <$>.identity ⟩
  p               ∎

homomorphism : ∀ {Tok R₁ R₂} (f : R₁ → R₂) (x : R₁) →
               return f ⊛ return x ≅P return {Tok = Tok} (f x)
homomorphism f x =
  return f ⊛  return x  ≅⟨ ⊛-in-terms-of->>= (return f) (return x) ⟩
  return f ⊛″ return x  ≅⟨ Monad.left-identity f (pam (return x)) ⟩
  f <$> return x        ≅⟨ <$>.homomorphism ⟩
  return (f x)          ∎

private

  infixl 10 _⊛-cong_

  _⊛-cong_ :
    ∀ {k Tok R₁ R₂ xs₁ xs₂ fs₁ fs₂}
      {p₁ : Parser Tok (R₁ → R₂) fs₁} {p₂ : Parser Tok R₁ xs₁}
      {p₃ : Parser Tok (R₁ → R₂) fs₂} {p₄ : Parser Tok R₁ xs₂} →
    p₁ ∼[ k ]P p₃ → p₂ ∼[ k ]P p₄ → p₁ ⊛″ p₂ ∼[ k ]P p₃ ⊛″ p₄
  _⊛-cong_ {p₁ = p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄ =
    p₁ ⊛″ p₂  ≅⟨ sym $ ⊛-in-terms-of->>= p₁ p₂ ⟩
    p₁ ⊛  p₂  ∼⟨ [ ○ - ○ - ○ - ○ ] p₁≈p₃ ⊛ p₂≈p₄ ⟩
    p₃ ⊛  p₄  ≅⟨ ⊛-in-terms-of->>= p₃ p₄ ⟩
    p₃ ⊛″ p₄  ∎

composition :
  ∀ {Tok R₁ R₂ R₃ fs gs xs}
  (p₁ : Parser Tok (R₂ → R₃) fs)
  (p₂ : Parser Tok (R₁ → R₂) gs)
  (p₃ : Parser Tok R₁        xs) →
  return _∘′_ ⊛ p₁ ⊛ p₂ ⊛ p₃ ≅P p₁ ⊛ (p₂ ⊛ p₃)
composition p₁ p₂ p₃ =
  return _∘′_ ⊛  p₁ ⊛  p₂ ⊛  p₃                          ≅⟨ ⊛-in-terms-of->>= (return _∘′_ ⊛ p₁ ⊛ p₂) p₃ ⟩
  return _∘′_ ⊛  p₁ ⊛  p₂ ⊛″ p₃                          ≅⟨ ⊛-in-terms-of->>= (return _∘′_ ⊛ p₁) p₂ ⊛-cong (p₃ ∎) ⟩
  return _∘′_ ⊛  p₁ ⊛″ p₂ ⊛″ p₃                          ≅⟨ ⊛-in-terms-of->>= (return _∘′_) p₁ ⊛-cong (p₂ ∎) ⊛-cong (p₃ ∎) ⟩
  return _∘′_ ⊛″ p₁ ⊛″ p₂ ⊛″ p₃                          ≅⟨ Monad.left-identity _∘′_ (pam p₁) ⊛-cong (p₂ ∎) ⊛-cong (p₃ ∎) ⟩
  _∘′_ <$> p₁ ⊛″ p₂ ⊛″ p₃                                ≅⟨ _ ∎ ⟩
  (_∘′_ <$> p₁ >>= _<$> p₂) >>= _<$> p₃                  ≅⟨ ([ ○ - ○ - ○ - ○ ] sym <$>.>>=-∘ >>= λ _ → _ ∎) ⟩
  (p₁ >>= λ f → (f ∘′_) <$> p₂) >>= _<$> p₃              ≅⟨ sym $ Monad.associative _ _ _ ⟩
  (p₁ >>= λ f → (f ∘′_) <$> p₂ >>= _<$> p₃)              ≅⟨ ([ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ → sym <$>.>>=-∘) ⟩
  (p₁ >>= λ f → p₂ >>= λ g → (f ∘′ g) <$> p₃)            ≅⟨ ([ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ →
                                                             [ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ →
                                                             <$>.composition) ⟩
  (p₁ >>= λ f → p₂ >>= λ g → f <$> (g <$> p₃))           ≅⟨ ([ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ →
                                                             [ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ →
                                                             <$>.in-terms-of->>=) ⟩
  (p₁ >>= λ f → p₂ >>= λ g → g <$> p₃ >>= (return ∘ f))  ≅⟨ ([ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ → Monad.associative _ _ _) ⟩
  (p₁ >>= λ f → p₂ >>= _<$> p₃ >>= (return ∘ f))         ≅⟨ ([ ○ - ○ - ○ - ○ ] _ ∎ >>= λ _ → sym <$>.in-terms-of->>=) ⟩
  (p₁ >>= λ f → f <$> (p₂ >>= _<$> p₃))                  ≅⟨ _ ∎ ⟩
  p₁ ⊛″ (p₂ ⊛″ p₃)                                       ≅⟨ sym $ (p₁ ∎) ⊛-cong ⊛-in-terms-of->>= p₂ p₃ ⟩
  p₁ ⊛″ (p₂ ⊛  p₃)                                       ≅⟨ sym $ ⊛-in-terms-of->>= p₁ (p₂ ⊛ p₃) ⟩
  p₁ ⊛  (p₂ ⊛  p₃)                                       ∎

interchange : ∀ {Tok R₁ R₂ fs}
              (p : Parser Tok (R₁ → R₂) fs) (x : R₁) →
              p ⊛ return x ≅P return (λ f → f x) ⊛ p
interchange p x =
  p ⊛  return x               ≅⟨ ⊛-in-terms-of->>= p (return x) ⟩
  p ⊛″ return x               ≅⟨ ([ ○ - ○ - ○ - ○ ] p ∎ >>= λ _ → <$>.homomorphism) ⟩
  (p >>= λ f → return (f x))  ≅⟨ sym <$>.in-terms-of->>= ⟩
  (λ f → f x) <$> p           ≅⟨ sym $ Monad.left-identity (λ f → f x) (pam p) ⟩
  return (λ f → f x) ⊛″ p     ≅⟨ sym $ ⊛-in-terms-of->>= (return (λ f → f x)) p ⟩
  return (λ f → f x) ⊛  p     ∎
