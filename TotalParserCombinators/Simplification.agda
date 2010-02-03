------------------------------------------------------------------------
-- Simplification of parsers
------------------------------------------------------------------------

module TotalParserCombinators.Simplification where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.Product
open import Data.List as List
import Data.List.Properties as ListProp
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (equivalent; module Equivalent)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

private module LM {Tok} = Monoid (List.monoid Tok)

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Congruence.Language
import TotalParserCombinators.Congruence.Parser as CP
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics hiding (_≅_)

open ≈-Reasoning
open ⊙ using (_⊙′_)

------------------------------------------------------------------------
-- Some laws

<$>-fail : ∀ {Tok R₁ R₂} {f : R₁ → R₂} →
           f <$> fail {Tok = Tok} ≈ fail
<$>-fail {Tok} {R₁} {f = f} =
  equivalent (λ x∈ → helper x∈ refl refl) (λ ())
  where
  helper : ∀ {x s xs} {p : Parser Tok R₁ xs} →
           x ∈ f <$> p · s → xs ≡ [] → p ≅ fail {Tok = Tok} {R = R₁} →
           x ∈ fail · s
  helper (<$> ()) refl refl

<$>-return : ∀ {Tok R₁ R₂} (f : R₁ → R₂) {x} →
             f <$> return {Tok = Tok} x ≈ return (f x)
<$>-return {Tok} {R₁} {R₂} f {x} =
  equivalent (λ x∈ → helper₁ x∈ refl refl) helper₂
  where
  helper₁ : ∀ {y s xs} {p : Parser Tok R₁ xs} →
            y ∈ f <$> p · s →
            xs ≡ [ x ] → p ≅ (Parser Tok _ _ ∶ return x) →
            y ∈ return (f x) · s
  helper₁ (<$> ∈return) refl refl with ∈return
  ... | return = return

  helper₂ : ∀ {y s} →
            y ∈ Parser Tok _ _ ∶ return (f x) · s →
            y ∈ f <$> return x · s
  helper₂ return = <$>_ {f = f} return

∣-token->>= : ∀ {Tok R} {f₁ f₂ : Tok → List R}
                {p₁ : (t : Tok) → ∞? (Parser Tok R (f₁ t)) []}
                {p₂ : (t : Tok) → ∞? (Parser Tok R (f₂ t)) []} →
              token >>= p₁ ∣ token >>= p₂ ≈
              token ⟫= λ t → ♭? (p₁ t) ∣ ♭? (p₂ t)
∣-token->>= {f₁ = f₁} {p₁ = p₁} {p₂} = equivalent helper₁ helper₂
  where
  helper₁ : token >>= p₁ ∣ token >>= p₂ ⊑
            token ⟫= λ t → ♭? (p₁ t) ∣ ♭? (p₂ t)
  helper₁ (∣ˡ     (token >>= x∈p₁))           = token >>= ∣ˡ x∈p₁
  helper₁ (∣ʳ .[] (_>>=_ {x = x} token x∈p₂)) =
    token >>= ∣ʳ (f₁ x) x∈p₂

  helper₂ : token ⟫= (λ t → ♭? (p₁ t) ∣ ♭? (p₂ t)) ⊑
            token >>= p₁ ∣ token >>= p₂
  helper₂ (token >>= ∣ˡ    y∈p₁x) = ∣ˡ    (token >>= y∈p₁x)
  helper₂ (token >>= ∣ʳ ._ y∈p₂x) = ∣ʳ [] (token >>= y∈p₂x)

nonempty-fail : ∀ {Tok R} →
                nonempty {Tok = Tok} {R = R} fail ≈ fail
nonempty-fail = equivalent helper (λ ())
  where
  helper : nonempty fail ⊑ fail
  helper (nonempty ())

cast-correct : ∀ {Tok R xs₁ xs₂} {eq : xs₁ ≡ xs₂} {p : Parser Tok R xs₁} →
               cast eq p ≈ p
cast-correct {eq = eq} {p} = equivalent helper cast
  where
  helper : cast eq p ⊑ p
  helper (cast x∈p) = x∈p

------------------------------------------------------------------------
-- Helpers

private

  -- A specialised variant of _≈_.

  infix 4 _≈_

  _≈′_ : ∀ {Tok R xs} (p₁ p₂ : Parser Tok R xs) → Set₁
  _≈′_ = _≈_

  force : ∀ {Tok R xs} (p : ∞ (Parser Tok R xs)) → ∃ λ p′ → ♭ p ≈′ p′
  force p = (♭ p , λ {_} → Equivalence.refl)

  -- A variant of cast.

  cast′ : ∀ {Tok R xs₁ xs₂} →
          xs₁ ≡ xs₂ → Parser Tok R xs₁ → Parser Tok R xs₂
  cast′ refl p = p

  cast-correct′ : ∀ {Tok R xs₁ xs₂} {p : Parser Tok R xs₁} →
                  (eq : xs₁ ≡ xs₂) → cast′ eq p ≈ p
  cast-correct′ refl = Equivalence.refl

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
--
-- Note that I have not proved that the simplifications preserve
-- /parser/ equivalence, only /language/ equivalence.

mutual

  simplify₁ : ∀ {Tok R xs} (p : Parser Tok R xs) → ∃ λ p′ → p ≈′ p′

  -- • return:

  simplify₁ (return x) = (return x , λ {_} → Equivalence.refl)

  -- • fail:

  simplify₁ fail       = (fail     , λ {_} → Equivalence.refl)

  -- • token:

  simplify₁ token      = (token    , λ {_} → Equivalence.refl)

  -- • _<$>_:

  simplify₁ (f <$> p) with simplify₁ p
  ... | (fail     , p≈∅) = _ , λ {_} → begin
                           f <$> p     ≈⟨ <$>-cong (λ _ → refl) p≈∅ ⟩
                           f <$> fail  ≈⟨ <$>-fail ⟩
                           fail        ∎
  ... | (return x , p≈ε) = _ , λ {_} → begin
                           f <$> p         ≈⟨ <$>-cong (λ x → refl {x = f x}) p≈ε ⟩
                           f <$> return x  ≈⟨ <$>-return f ⟩
                           return (f x)    ∎
  ... | (p′       , p≈p′) = _ , λ {_} → begin
                           f <$> p   ≈⟨ <$>-cong (λ _ → refl) p≈p′ ⟩
                           f <$> p′  ∎

  -- • _∣_:

  simplify₁ (p₁ ∣ p₂) with simplify₁ p₁ | simplify₁ p₂
  ... | (fail          , p₁≈∅)
      | (p₂′           , p₂≈p₂′) = _ , λ {_} → begin
                                   p₁   ∣ p₂   ≈⟨ ∣-cong p₁≈∅ p₂≈p₂′ ⟩
                                   fail ∣ p₂′  ≈⟨ AdditiveMonoid.left-identity p₂′ ⟩
                                   p₂′         ∎
  ... | (p₁′           , p₁≈p₁′)
      | (fail          , p₂≈∅)   = _ , λ {_} → begin
                                   p₁  ∣ p₂       ≈⟨ ∣-cong p₁≈p₁′ p₂≈∅ ⟩
                                   p₁′ ∣ fail     ≈⟨ AdditiveMonoid.right-identity p₁′ ⟩
                                   p₁′            ≈⟨ Equivalence.sym $ cast-correct′ lem ⟩
                                   cast′ lem p₁′  ∎
                                   where lem = sym (proj₂ LM.identity _)
  ... | (token >>= p₁′ , p₁≈…)
      | (token >>= p₂′ , p₂≈…)   = _ , λ {_} → begin
                                   p₁            ∣ p₂                        ≈⟨ ∣-cong p₁≈… p₂≈… ⟩
                                   token >>= p₁′ ∣ token >>= p₂′             ≈⟨ ∣-token->>= ⟩
                                   token ⟫= (λ t → ♭? (p₁′ t) ∣ ♭? (p₂′ t))  ∎
  ... | (p₁′           , p₁≈p₁′)
      | (p₂′           , p₂≈p₂′) = _ , λ {_} → begin
                                   p₁  ∣ p₂   ≈⟨ ∣-cong p₁≈p₁′ p₂≈p₂′ ⟩
                                   p₁′ ∣ p₂′  ∎

  -- • _⊛_:

  simplify₁ (p₁ ⊛ p₂) =
    helper _ _ (simplify₁′ p₁) (simplify₁′ p₂) refl refl
    where
    -- token ⊛ token is never type correct, but Agda's case-splitting
    -- machinery cannot see that it is not, so instead
    -- of a with clause the following ugly machinery is used.

    cast₁ : ∀ {Tok R R₁ R₁′ xs xs′} {ys : List R} →
            (R≡  : R₁ ≡ R₁′) → xs ≅ xs′ →
            ∞? (Parser Tok R₁′ xs′) ys →
            ∞? (Parser Tok R₁  xs ) ys
    cast₁ refl refl p = p

    helper : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
               (p₁ : ∞? (Parser Tok (R₁ → R₂) fs ) xs)
               (p₂ : ∞? (Parser Tok  R₁′      xs′) fs) →
             (∃ λ p₁′ → ♭? p₁ ≈′ p₁′) →
             (∃ λ p₂′ → ♭? p₂ ≈′ p₂′) →
             (R≡  : R₁ ≡ R₁′) →
             (xs≅ : xs ≅ xs′) →
             ∃ λ p′ → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≈′ p′
    helper {xs = xs} p₁ p₂ (fail , p₁≈∅) _ refl refl = _ , λ {_} → begin
      p₁      ⊛ p₂    ≈⟨ ⊛-cong (begin
                           ♭? p₁                   ≈⟨ p₁≈∅ ⟩
                           fail                    ≅⟨ CP.Equivalence.sym $ ♭♯.correct xs ⟩
                           ♭? {xs = xs} (♯? fail)  ∎)
                           (Equivalence.refl {p = ♭? p₂}) ⟩
      ♯? fail ⊛ p₂    ≈⟨ ⊙-IdempotentSemiring.left-zero-⊛ p₂ ⟩
      fail            ≈⟨ Equivalence.sym $ cast-correct′ lem ⟩
      cast′ lem fail  ∎
      where lem = sym (ListProp.Monad.right-zero xs)
    helper {fs = fs} p₁ p₂ _ (fail , p₂≈∅) refl refl = _ , λ {_} → begin
      p₁ ⊛ p₂       ≈⟨ ⊛-cong (Equivalence.refl {p = ♭? p₁}) (begin
                         ♭? p₂                   ≈⟨ p₂≈∅ ⟩
                         fail                    ≅⟨ CP.Equivalence.sym $ ♭♯.correct fs ⟩
                         ♭? {xs = fs} (♯? fail)  ∎) ⟩
      p₁ ⊛ ♯? fail  ≈⟨ ⊙-IdempotentSemiring.right-zero-⊛ p₁ ⟩
      fail          ∎
    helper p₁ p₂ (return f , p₁≈ε) (return x , p₂≈ε) refl refl =
      _ , λ {_} → begin
      p₁       ⊛ p₂        ≈⟨ ⊛-cong p₁≈ε p₂≈ε ⟩
      return f ⊙ return x  ≈⟨ ApplicativeFunctor.homomorphism f x ⟩
      return (f x)         ∎
    helper p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′) R≡ xs≅ =
      helper′ p₁ p₂ (p₁′ , λ {_} → p₁≈p₁′) (p₂′ , λ {_} → p₂≈p₂′) R≡ xs≅
      where
      helper′ : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
                  (p₁ : ∞? (Parser Tok (R₁ → R₂) fs ) xs)
                  (p₂ : ∞? (Parser Tok  R₁′      xs′) fs) →
                (∃ λ p₁′ → ♭? p₁ ≈′ p₁′) →
                (∃ λ p₂′ → ♭? p₂ ≈′ p₂′) →
                (R≡  : R₁ ≡ R₁′) →
                (xs≅ : xs ≅ xs′) →
                ∃ λ p′ → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≈′ p′
      helper′ {fs = fs} {xs} p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′)
              refl refl = _ , λ {_} → begin
        p₁  ⊛ p₂   ≈⟨ ⊛-cong
                        (begin
                           ♭? p₁                  ≈⟨ p₁≈p₁′ ⟩
                           p₁′                    ≅⟨ CP.Equivalence.sym $ ♭♯.correct xs ⟩
                           ♭? {xs = xs} (♯? p₁′)  ∎)
                        (begin
                           ♭? p₂                  ≈⟨ p₂≈p₂′ ⟩
                           p₂′                    ≅⟨ CP.Equivalence.sym $ ♭♯.correct fs ⟩
                           ♭? {xs = fs} (♯? p₂′)  ∎) ⟩
        p₁′ ⊙ p₂′  ∎

  -- • _>>=_:

  simplify₁ (p₁ >>= p₂) with simplify₁ p₁
  ... | (fail     , p₁≈∅) = _ , λ {_} → begin
                            p₁   >>= p₂  ≈⟨ >>=-cong p₁≈∅ (λ _ → Equivalence.refl) ⟩
                            fail >>= p₂  ≈⟨ ⟫=-IdempotentSemiring.left-zero->>= p₂ ⟩
                            fail         ∎
  ... | (return x , p₁≈ε) with simplify₁′ (p₂ x)
  ...   | (p₂′ , p₂x≈p₂′) = _ , λ {_} → begin
                            p₁       >>= p₂  ≈⟨ >>=-cong
                                                  p₁≈ε
                                                  (λ x → Equivalence.refl {p = ♭? (p₂ x)}) ⟩
                            return x >>= p₂  ≈⟨ Monad.left-identity->>= x p₂ ⟩
                            ♭? (p₂ x)        ≈⟨ p₂x≈p₂′ ⟩
                            p₂′              ≈⟨ Equivalence.sym $ cast-correct′ lem ⟩
                            cast′ lem p₂′    ∎
                            where lem = sym (proj₂ LM.identity _)
  simplify₁ (p₁ >>= p₂)
      | (p₁′ , p₁≈p₁′)    = _ , λ {_} → begin
                            p₁  >>= p₂  ≈⟨ >>=-cong p₁≈p₁′ (λ _ → Equivalence.refl) ⟩
                            p₁′ >>= p₂  ∎

  -- • _>>=!_:

  simplify₁ (p₁ >>=! p₂) with force p₁
  ... | (fail     , p₁≈∅) = _ , λ {_} → begin
                            p₁ >>=! p₂  ≈⟨ >>=!-cong p₁≈∅ (λ _ → Equivalence.refl) ⟩
                            ∅  >>=! p₂  ≈⟨ equivalent helper (λ ()) ⟩
                            fail        ∎
                            where
                            ∅ = ♯ fail

                            helper : ∅ >>=! p₂ ⊑ fail
                            helper (() >>=! _)
  ... | (return x , p₁≈ε) with simplify₁′ (p₂ x)
  ...   | (p₂′ , p₂x≈p₂′) = _ , λ {_} → begin
                            p₁       >>=! p₂  ≈⟨ >>=!-cong p₁≈ε
                                                   (λ x → Equivalence.refl {p = ♭? (p₂ x)}) ⟩
                            return-x >>=! p₂  ≈⟨ equivalent helper
                                                            (λ y∈p₂x → return >>=! y∈p₂x) ⟩
                            ♭? (p₂ x)         ≈⟨ p₂x≈p₂′ ⟩
                            p₂′               ≈⟨ Equivalence.sym $ cast-correct′ lem ⟩
                            cast′ lem p₂′     ∎
                            where
                            lem = sym (proj₂ LM.identity _)

                            return-x = ♯ return x

                            helper : return-x >>=! p₂ ⊑ ♭? (p₂ x)
                            helper (return >>=! y∈p₂x) = y∈p₂x
  simplify₁ (p₁ >>=! p₂)
      | (p₁′ , p₁≈p₁′)    = _ , λ {_} → begin
                            p₁ >>=! p₂  ≈⟨ >>=!-cong p₁≈p₁′ (λ _ → Equivalence.refl) ⟩
                            p₁′>>=!p₂   ∎
                            where p₁′>>=!p₂ = ♯ p₁′ >>=! p₂

  -- • nonempty:

  simplify₁ (nonempty p) with simplify₁ p
  ... | (fail , p≈∅)  = _ , λ {_} → begin
                        nonempty p     ≈⟨ nonempty-cong p≈∅ ⟩
                        nonempty fail  ≈⟨ nonempty-fail ⟩
                        fail           ∎
  ... | (p′   , p≈p′) = _ , λ {_} → begin
                        nonempty p   ≈⟨ nonempty-cong p≈p′ ⟩
                        nonempty p′  ∎

  -- • cast:

  simplify₁ (cast refl p) with simplify₁ p
  ... | (p′ , p≈p′) = _ , λ {_} → begin
                      cast refl p   ≈⟨ cast-cong p≈p′ ⟩
                      cast refl p′  ≈⟨ cast-correct ⟩
                      p′            ∎

  -- Note that if an argument parser is delayed, then simplification
  -- is not applied recursively (because this could lead to
  -- non-termination). Partial simplification, for instance up to a
  -- predetermined depth, would be possible, but for simplicity
  -- delayed parsers are simply forced and returned.

  simplify₁′ : ∀ {Tok R R′ xs} {ys : List R′}
               (p : ∞? (Parser Tok R xs) ys) → ∃ λ p′ → ♭? p ≈′ p′
  simplify₁′ ⟪ p ⟫ = (♭ p , λ {_} → Equivalence.refl)
  simplify₁′ ⟨ p ⟩ = simplify₁ p

-- The projections of simplify₁.

simplify : ∀ {Tok R xs} → Parser Tok R xs → Parser Tok R xs
simplify p = proj₁ (simplify₁ p)

correct : ∀ {Tok R xs} {p : Parser Tok R xs} → p ≈ simplify p
correct = proj₂ (simplify₁ _)
