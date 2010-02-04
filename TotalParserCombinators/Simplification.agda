------------------------------------------------------------------------
-- Simplification of parsers
------------------------------------------------------------------------

module TotalParserCombinators.Simplification where

open import Algebra
open import Coinduction
open import Data.List as List
import Data.List.Properties as ListProp
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality
  using (refl) renaming (_≅_ to _≅H_)

private
  module LM {A : Set} = Monoid (List.monoid A)

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Congruence.Parser as Eq
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- Helpers

private

  -- A specialised variant of _≅_.

  infix 4 _≅′_

  _≅′_ : ∀ {Tok R xs} (p₁ p₂ : Parser Tok R xs) → Set₁
  _≅′_ = _≅P_

  force : ∀ {Tok R xs} (p : ∞ (Parser Tok R xs)) → ∃ λ p′ → ♭ p ≅′ p′
  force p = (♭ p , (♭ p ∎))

  -- A variant of cast.

  cast′ : ∀ {Tok R xs₁ xs₂} →
          xs₁ ≡ xs₂ → Parser Tok R xs₁ → Parser Tok R xs₂
  cast′ refl p = p

  cast-correct′ : ∀ {Tok R xs₁ xs₂} {p : Parser Tok R xs₁} →
                  (eq : xs₁ ≡ xs₂) → cast′ eq p ≅P p
  cast-correct′ {p = p} refl = p ∎

------------------------------------------------------------------------
-- Simplification

-- The function simplify₁ simplifies the first "layer" of a parser,
-- down to the first occurrences of ♯_. The following simplifications
-- are applied in a bottom-up manner (modulo ∞ and casts):
--
-- fail         ∣ p            → p
-- p            ∣ fail         → p
-- token >>= p₁ ∣ token >>= p₂ → token >>= λ t → p₁ t ∣ p₂ t
-- f <$> fail                  → fail
-- f <$> return x              → return (f x)
-- fail     ⊛ p                → fail
-- p        ⊛ fail             → fail
-- return f ⊛ return x         → return (f x)
-- fail     >>= p              → fail
-- return x >>= p              → p x
-- fail     >>=! p             → fail
-- return x >>=! p             → p x
-- nonempty fail               → fail
-- cast eq p                   → p
--
-- An example of a possible future addition:
--
-- (p₁ >>= p₂) >>= p₃ → p₁ >>= λ x → p₂ >>= p₃

mutual

  simplify₁ : ∀ {Tok R xs} (p : Parser Tok R xs) → ∃ λ p′ → p ≅′ p′

  -- • return:

  simplify₁ (return x) = (return x , (return x ∎))

  -- • fail:

  simplify₁ fail       = (fail     , (fail ∎))

  -- • token:

  simplify₁ token      = (token    , (token ∎))

  -- • _<$>_:

  simplify₁ (f <$> p) with simplify₁ p
  ... | (fail     , p≅∅) = _ , (
                           f <$> p     ≅⟨ (λ _ → refl) <$> p≅∅ ⟩
                           f <$> fail  ≅⟨ <$>.zero ⟩
                           fail        ∎)
  ... | (return x , p≅ε) = _ , (
                           f <$> p         ≅⟨ (λ x → refl {x = f x}) <$> p≅ε ⟩
                           f <$> return x  ≅⟨ <$>.homomorphism f ⟩
                           return (f x)    ∎)
  ... | (p′       , p≅p′) = _ , (
                           f <$> p   ≅⟨ (λ _ → refl) <$> p≅p′ ⟩
                           f <$> p′  ∎)

  -- • _∣_:

  simplify₁ (p₁ ∣ p₂) with simplify₁ p₁ | simplify₁ p₂
  ... | (fail          , p₁≅∅)
      | (p₂′           , p₂≅p₂′) = _ , (
                                   p₁   ∣ p₂   ≅⟨ p₁≅∅ ∣ p₂≅p₂′ ⟩
                                   fail ∣ p₂′  ≅⟨ AdditiveMonoid.left-identity p₂′ ⟩
                                   p₂′         ∎)
  ... | (p₁′           , p₁≅p₁′)
      | (fail          , p₂≅∅)   = _ , (
                                   p₁  ∣ p₂       ≅⟨ p₁≅p₁′ ∣ p₂≅∅ ⟩
                                   p₁′ ∣ fail     ≅⟨ AdditiveMonoid.right-identity p₁′ ⟩
                                   p₁′            ≅⟨ sym $ cast-correct′ lem ⟩
                                   cast′ lem p₁′  ∎)
                                   where lem = P.sym (proj₂ LM.identity _)
  ... | (token >>= p₁′ , p₁≅…)
      | (token >>= p₂′ , p₂≅…)   = _ , (
                                   p₁            ∣ p₂                        ≅⟨ p₁≅… ∣ p₂≅… ⟩
                                   token >>= p₁′ ∣ token >>= p₂′             ≅⟨ (token ∎) >>= (λ x → ♭? (p₁′ x) ∎) ∣
                                                                                (token ∎) >>= (λ x → ♭? (p₂′ x) ∎) ⟩
                                   token ⟫= (♭? ∘ p₁′) ∣ token ⟫= (♭? ∘ p₂′) ≅⟨ sym $ Monad.left-distributive
                                                                                        token (♭? ∘ p₁′) (♭? ∘ p₂′) ⟩
                                   token ⟫= (λ t → ♭? (p₁′ t) ∣ ♭? (p₂′ t))  ∎)
  ... | (p₁′           , p₁≅p₁′)
      | (p₂′           , p₂≅p₂′) = _ , (
                                   p₁  ∣ p₂   ≅⟨ p₁≅p₁′ ∣ p₂≅p₂′ ⟩
                                   p₁′ ∣ p₂′  ∎)

  -- • _⊛_:

  simplify₁ (p₁ ⊛ p₂) =
    helper _ _ (simplify₁′ p₁) (simplify₁′ p₂) refl refl
    where
    -- token ⊛ token is never type correct, but Agda's case-splitting
    -- machinery cannot see that it is not, so instead
    -- of a with clause the following ugly machinery is used.

    cast₁ : ∀ {Tok R R₁ R₁′ xs xs′} {ys : List R} →
            (R≡  : R₁ ≡ R₁′) → xs ≅H xs′ →
            ∞? (Parser Tok R₁′ xs′) ys →
            ∞? (Parser Tok R₁  xs ) ys
    cast₁ refl refl p = p

    helper : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
               (p₁ : ∞? (Parser Tok (R₁ → R₂) fs ) xs)
               (p₂ : ∞? (Parser Tok  R₁′      xs′) fs) →
             (∃ λ p₁′ → ♭? p₁ ≅′ p₁′) →
             (∃ λ p₂′ → ♭? p₂ ≅′ p₂′) →
             (R≡  : R₁ ≡ R₁′) →
             (xs≅ : xs ≅H xs′) →
             ∃ λ p′ → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≅′ p′
    helper {xs = xs} p₁ p₂ (fail , p₁≅∅) _ refl refl = _ , (
      p₁    ⊛ p₂      ≅⟨ sym $ ApplicativeFunctor.⊙≅⊛ p₁ p₂ ⟩
      ♭? p₁ ⊙ ♭? p₂   ≅⟨ p₁≅∅ ⊙′ (♭? p₂ ∎) ⟩
      fail  ⊙ ♭? p₂   ≅⟨ ApplicativeFunctor.left-zero (♭? p₂) ⟩
      fail            ≅⟨ sym $ cast-correct′ lem ⟩
      cast′ lem fail  ∎)
      where lem = P.sym (ListProp.Monad.right-zero xs)
    helper {fs = fs} p₁ p₂ _ (fail , p₂≅∅) refl refl = _ , (
      p₁    ⊛ p₂      ≅⟨ sym $ ApplicativeFunctor.⊙≅⊛ p₁ p₂ ⟩
      ♭? p₁ ⊙ ♭? p₂   ≅⟨ (♭? p₁ ∎) ⊙′ p₂≅∅ ⟩
      ♭? p₁ ⊙ fail    ≅⟨ ApplicativeFunctor.right-zero (♭? p₁) ⟩
      fail            ∎)
    helper p₁ p₂ (return f , p₁≅ε) (return x , p₂≅ε) refl refl =
      _ , (
      p₁       ⊛ p₂        ≅⟨ p₁≅ε ⊛ p₂≅ε ⟩
      return f ⊙ return x  ≅⟨ ApplicativeFunctor.homomorphism f x ⟩
      return (f x)         ∎)
    helper p₁ p₂ (p₁′ , p₁≅p₁′) (p₂′ , p₂≅p₂′) R≡ xs≅ =
      helper′ p₁ p₂ (p₁′ , p₁≅p₁′) (p₂′ , p₂≅p₂′) R≡ xs≅
      where
      helper′ : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
                  (p₁ : ∞? (Parser Tok (R₁ → R₂) fs ) xs)
                  (p₂ : ∞? (Parser Tok  R₁′      xs′) fs) →
                (∃ λ p₁′ → ♭? p₁ ≅′ p₁′) →
                (∃ λ p₂′ → ♭? p₂ ≅′ p₂′) →
                (R≡  : R₁ ≡ R₁′) →
                (xs≅ : xs ≅H xs′) →
                ∃ λ p′ → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≅′ p′
      helper′ {fs = fs} {xs} p₁ p₂ (p₁′ , p₁≅p₁′) (p₂′ , p₂≅p₂′)
              refl refl = _ , (
        p₁    ⊛ p₂     ≅⟨ sym $ ApplicativeFunctor.⊙≅⊛ p₁ p₂ ⟩
        ♭? p₁ ⊙ ♭? p₂  ≅⟨ p₁≅p₁′ ⊙′ p₂≅p₂′ ⟩
        p₁′   ⊙ p₂′    ∎)

  -- • _>>=_:

  simplify₁ (p₁ >>= p₂) with simplify₁ p₁
  ... | (fail     , p₁≅∅) = _ , (
                            p₁  >>= p₂         ≅⟨ p₁≅∅ >>= (λ x → ♭? (p₂ x) ∎) ⟩
                            fail ⟫= (♭? ∘ p₂)  ≅⟨ Monad.left-zero (♭? ∘ p₂) ⟩
                            fail               ∎)
  ... | (return x , p₁≅ε) with simplify₁′ (p₂ x)
  ...   | (p₂′ , p₂x≅p₂′) = _ , (
                            p₁      >>= p₂         ≅⟨ p₁≅ε >>= (λ x → ♭? (p₂ x) ∎) ⟩
                            return x ⟫= (♭? ∘ p₂)  ≅⟨ Monad.left-identity x (♭? ∘ p₂) ⟩
                            ♭? (p₂ x)              ≅⟨ p₂x≅p₂′ ⟩
                            p₂′                    ≅⟨ sym $ cast-correct′ lem ⟩
                            cast′ lem p₂′          ∎)
                            where lem = P.sym (proj₂ LM.identity _)
  simplify₁ (p₁ >>= p₂)
      | (p₁′ , p₁≅p₁′)    = _ , (
                            p₁  >>= p₂  ≅⟨ p₁≅p₁′ >>= (λ x → ♭? (p₂ x) ∎) ⟩
                            p₁′ >>= p₂  ∎)

  -- • _>>=!_:

  simplify₁ (p₁ >>=! p₂) with force p₁
  ... | (fail     , p₁≅∅) = _ , (
                            p₁       >>=! p₂        ≅⟨ p₁≅∅ >>=! (λ x → ♭? (p₂ x) ∎) ⟩
                            (♯ fail) >>=! p₂        ≅⟨ Monad.>>=!≅⟫= _ p₂ ⟩
                            fail      ⟫= (♭? ∘ p₂)  ≅⟨ Monad.left-zero (♭? ∘ p₂) ⟩
                            fail                    ∎)
  ... | (return x , p₁≅ε) with simplify₁′ (p₂ x)
  ...   | (p₂′ , p₂x≅p₂′) = _ , (
                            p₁           >>=! p₂        ≅⟨ p₁≅ε >>=! (λ x → ♭? (p₂ x) ∎) ⟩
                            (♯ return x) >>=! p₂        ≅⟨ Monad.>>=!≅⟫= _ p₂ ⟩
                            return x      ⟫= (♭? ∘ p₂)  ≅⟨ Monad.left-identity x (♭? ∘ p₂) ⟩
                            ♭? (p₂ x)                   ≅⟨ p₂x≅p₂′ ⟩
                            p₂′                         ≅⟨ sym $ cast-correct′ lem ⟩
                            cast′ lem p₂′               ∎)
                            where lem = P.sym (proj₂ LM.identity _)
  simplify₁ (p₁ >>=! p₂)
      | (p₁′ , p₁≅p₁′)    = _ , (
                            p₁ >>=! p₂       ≅⟨ p₁≅p₁′ >>=! (λ x → ♭? (p₂ x) ∎) ⟩
                            (♯ p₁′ >>=! p₂)  ∎)

  -- • nonempty:

  simplify₁ (nonempty p) with simplify₁ p
  ... | (fail , p≅∅)  = _ , (
                        nonempty p     ≅⟨ nonempty p≅∅ ⟩
                        nonempty fail  ≅⟨ Nonempty.zero ⟩
                        fail           ∎)
  ... | (p′   , p≅p′) = _ , (
                        nonempty p   ≅⟨ nonempty p≅p′ ⟩
                        nonempty p′  ∎)

  -- • cast:

  simplify₁ (cast refl p) with simplify₁ p
  ... | (p′ , p≅p′) = _ , (
                      cast refl p  ≅⟨ Cast.correct ⟩
                      p            ≅⟨ p≅p′ ⟩
                      p′           ∎)

  -- Note that if an argument parser is delayed, then simplification
  -- is not applied recursively (because this could lead to
  -- non-termination). Partial simplification, for instance up to a
  -- predetermined depth, would be possible, but for simplicity
  -- delayed parsers are simply forced and returned.

  simplify₁′ : ∀ {Tok R R′ xs} {ys : List R′}
               (p : ∞? (Parser Tok R xs) ys) → ∃ λ p′ → ♭? p ≅′ p′
  simplify₁′ ⟪ p ⟫ = (♭ p , (♭ p ∎))
  simplify₁′ ⟨ p ⟩ = simplify₁ p

-- The projections of simplify₁.

simplify : ∀ {Tok R xs} → Parser Tok R xs → Parser Tok R xs
simplify p = proj₁ (simplify₁ p)

correct : ∀ {Tok R xs} {p : Parser Tok R xs} → p ≅P simplify p
correct = proj₂ (simplify₁ _)
