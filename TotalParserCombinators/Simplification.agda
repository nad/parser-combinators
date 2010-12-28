------------------------------------------------------------------------
-- Simplification of parsers
------------------------------------------------------------------------

module TotalParserCombinators.Simplification where

open import Algebra
open import Coinduction
open import Data.List using (List; [])
import Data.List.Any.BagAndSetEquality as BSEq
open import Data.Maybe using (Maybe); open Data.Maybe.Maybe
open import Data.Nat
open import Data.Product
open import Data.Product.N-ary
open import Function
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; _with-≡_)
open import Relation.Binary.HeterogeneousEquality
  using (refl) renaming (_≅_ to _≅H_)

private
  module BSMonoid {k} {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid k A)

open import TotalParserCombinators.Congruence
  hiding (return; fail; token) renaming (_∣_ to _∣′_)
import TotalParserCombinators.Congruence.Sound as C
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics using (parser)

------------------------------------------------------------------------
-- Simplification

-- The function simplify₁ simplifies the first "layer" of a parser,
-- down to the first occurrences of ♯_. Right-hand sides of bind are
-- not simplified, except if the return x >>= p → p x rule is
-- triggered. The following simplifications are applied in a bottom-up
-- manner (some of them also if one argument is delayed):
--
-- f <$> fail                  → fail
-- f <$> return x              → return (f x)
-- fail         ∣ p            → p
-- p            ∣ fail         → p
-- token >>= p₁ ∣ token >>= p₂ → token >>= λ t → ♭? (p₁ t) ∣ ♭? (p₂ t)
-- fail     ⊛ p                → fail
-- p        ⊛ fail             → fail
-- return f ⊛ return x         → return (f x)
-- fail     >>= p              → fail
-- return x >>= p              → p x
-- nonempty fail               → fail
-- cast eq p                   → p
--
-- Some ♯_'s may be removed, but care is taken to ensure that
-- non-simplified parsers in the result are either delayed or on the
-- right-hand side of a bind constructor.

private
 mutual

  simplify₁ : ∀ {Tok R xs} (p : Parser Tok R xs) →
              ∃₂ λ xs (p′ : Parser Tok R xs) → p ≅P p′

  -- • return:

  simplify₁ (return x) = (_ , return x , (return x ∎))

  -- • fail:

  simplify₁ fail       = (_ , fail     , (fail ∎))

  -- • token:

  simplify₁ token      = (_ , token    , (token ∎))

  -- • _<$>_:

  simplify₁ (f <$> p) with simplify₁ p
  ... | (._ , fail     , p≅∅)  = _ , _ , (
                                 f <$> p     ≅⟨ (λ _ → refl) <$> p≅∅ ⟩
                                 f <$> fail  ≅⟨ <$>.zero ⟩
                                 fail        ∎)
  ... | (._ , return x , p≅ε)  = _ , _ , (
                                 f <$> p         ≅⟨ (λ x → refl {x = f x}) <$> p≅ε ⟩
                                 f <$> return x  ≅⟨ <$>.homomorphism f ⟩
                                 return (f x)    ∎)
  ... | (_  , p′       , p≅p′) = _ , _ , (
                                 f <$> p   ≅⟨ (λ _ → refl) <$> p≅p′ ⟩
                                 f <$> p′  ∎)

  -- • _∣_:

  simplify₁ (p₁ ∣ p₂) with simplify₁ p₁ | simplify₁ p₂
  ... | (._ , fail        , p₁≅∅)
      | (_  , p₂′         , p₂≅p₂′) = _ , _ , (
                                      p₁   ∣ p₂   ≅⟨ p₁≅∅ ∣′ p₂≅p₂′ ⟩
                                      fail ∣ p₂′  ≅⟨ AdditiveMonoid.left-identity p₂′ ⟩
                                      p₂′         ∎)
  ... | (_  , p₁′         , p₁≅p₁′)
      | (._ , fail        , p₂≅∅)   = _ , _ , (
                                      p₁  ∣ p₂    ≅⟨ p₁≅p₁′ ∣′ p₂≅∅ ⟩
                                      p₁′ ∣ fail  ≅⟨ AdditiveMonoid.right-identity p₁′ ⟩
                                      p₁′         ∎)
  ... | (._ , p₁₁ >>= p₁₂ , p₁≅…)
      | (._ , p₂₁ >>= p₂₂ , p₂≅…) = let h = helper p₁₁ refl p₁₂ p₂₁ refl p₂₂ in
                                    _ , _ , (
                                    p₁          ∣ p₂           ≅⟨ p₁≅… ∣′ p₂≅… ⟩
                                    p₁₁ >>= p₁₂ ∣ p₂₁ >>= p₂₂  ≅⟨ proj₂ (proj₂ h) ⟩
                                    proj₁ (proj₂ h)            ∎)
    where
    helper : ∀ {Tok R₁ R₂ R xs₁ xs₁′ xs₂ xs₂′ f₁ f₂}
             (p₁₁ : ∞⟨ f₁ ⟩Parser Tok R₁ xs₁′)
             (eq₁ : xs₁′ ≡ flatten xs₁)
             (p₁₂ : (x : R₁) → ∞⟨ xs₁ ⟩Parser Tok R (apply f₁ x))
             (p₂₁ : ∞⟨ f₂ ⟩Parser Tok R₂ xs₂′)
             (eq₂ : xs₂′ ≡ flatten xs₂)
             (p₂₂ : (x : R₂) → ∞⟨ xs₂ ⟩Parser Tok R (apply f₂ x)) →
             ∃₂ λ xs (p : Parser Tok R xs) →
                P.subst (∞⟨ f₁ ⟩Parser Tok R₁) eq₁ p₁₁ >>= p₁₂ ∣
                P.subst (∞⟨ f₂ ⟩Parser Tok R₂) eq₂ p₂₁ >>= p₂₂
                ≅P p
    helper p₁₁ eq₁ p₁₂ p₂₁ eq₂ p₂₂
      with P.inspect (♭? p₁₁) | P.inspect (♭? p₂₁)
    helper {Tok} {f₁ = f₁} {f₂} p₁₁ eq₁ p₁₂ p₂₁ eq₂ p₂₂
      | token with-≡ eq₁′ | token with-≡ eq₂′ = _ , _ , (
      cast₁ p₁₁ >>= p₁₂ ∣ cast₂ p₂₁ >>= p₂₂          ≅⟨ [ forced? p₁₁ - ○ - forced?′ p₁₂ - ○ ] Subst.correct∞ eq₁ p₁₁ >>=
                                                                                               (λ t → ♭? (p₁₂ t) ∎) ∣′
                                                        [ forced? p₂₁ - ○ - forced?′ p₂₂ - ○ ] Subst.correct∞ eq₂ p₂₁ >>=
                                                                                               (λ t → ♭? (p₂₂ t) ∎) ⟩
      ♭? p₁₁ >>= (♭? ∘ p₁₂) ∣ ♭? p₂₁ >>= (♭? ∘ p₂₂)  ≅⟨ [ ○ - ○ - ○ - ○ ]
                                                          P.subst (λ p → p ≅P token) (P.sym eq₁′) (token ∎) >>= (λ t → ♭? (p₁₂ t) ∎) ∣′
                                                        [ ○ - ○ - ○ - ○ ]
                                                          P.subst (λ p → p ≅P token) (P.sym eq₂′) (token ∎) >>= (λ t → ♭? (p₂₂ t) ∎) ⟩
      token >>= (♭? ∘ p₁₂) ∣ token >>= (♭? ∘ p₂₂)    ≅⟨ sym $ Monad.left-distributive token (♭? ∘ p₁₂) (♭? ∘ p₂₂) ⟩
      token >>= (λ t → ♭? (p₁₂ t) ∣ ♭? (p₂₂ t))      ∎)
      where
      cast₁ = P.subst (∞⟨ f₁ ⟩Parser Tok Tok) eq₁
      cast₂ = P.subst (∞⟨ f₂ ⟩Parser Tok Tok) eq₂
    helper _ _ _ _ _ _ | _ | _ = _ , _ , (_ ∎)

  simplify₁ (p₁ ∣ p₂) | (_  , p₁′ , p₁≅p₁′) | (_  , p₂′ , p₂≅p₂′) =
     _ , _ , (
     p₁  ∣ p₂   ≅⟨ p₁≅p₁′ ∣′ p₂≅p₂′ ⟩
     p₁′ ∣ p₂′  ∎)

  -- • _⊛_:

  simplify₁ (p₁ ⊛ p₂) =
    helper _ _ p₁ p₂ (simplify₁′ p₁) (simplify₁′ p₂) refl refl
    where
    -- token ⊛ token is never type correct, but Agda's case-splitting
    -- machinery cannot see this, so instead of a with clause the
    -- following ugly machinery is used.

    cast₁ : ∀ {Tok R R₁ R₁′ xs xs′} {ys : Maybe (List R)} →
            (R≡  : R₁ ≡ R₁′) → xs ≅H xs′ →
            ∞⟨ ys ⟩Parser Tok R₁′ (flatten xs′) →
            ∞⟨ ys ⟩Parser Tok R₁  (flatten xs)
    cast₁ refl refl p = p

    helper : ∀ {Tok R₁ R₁′ R₂} fs xs {xs′}
               (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs))
               (p₂ : ∞⟨ fs ⟩Parser Tok  R₁′      (flatten xs′)) →
             (∃₂ λ xs (p₁′ : Parser _ _ xs) → ♭? p₁ ≅P p₁′) →
             (∃₂ λ xs (p₂′ : Parser _ _ xs) → ♭? p₂ ≅P p₂′) →
             (R≡  : R₁ ≡ R₁′) →
             (xs≅ : xs ≅H xs′) →
             ∃₂ λ xs (p′ : Parser _ _ xs) → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≅P p′
    helper fs xs p₁ p₂ (._ , fail , p₁≅∅) _ refl refl = _ , _ , (
      p₁   ⊛ p₂     ≅⟨ [ xs - ○ - fs - ○ ] p₁≅∅ ⊛ (♭? p₂ ∎) ⟩
      fail ⊛ ♭? p₂  ≅⟨ ApplicativeFunctor.left-zero (♭? p₂) ⟩
      fail          ∎)
    helper fs xs p₁ p₂ _ (._ , fail , p₂≅∅) refl refl = _ , _ , (
      p₁    ⊛ p₂    ≅⟨ [ xs - ○ - fs - ○ ] ♭? p₁ ∎ ⊛ p₂≅∅ ⟩
      ♭? p₁ ⊛ fail  ≅⟨ ApplicativeFunctor.right-zero (♭? p₁) ⟩
      fail          ∎)
    helper fs xs p₁ p₂ (._ , return f , p₁≅ε) (._ , return x , p₂≅ε)
           refl refl = _ , _ , (
      p₁       ⊛ p₂        ≅⟨ [ xs - ○ - fs - ○ ] p₁≅ε ⊛ p₂≅ε ⟩
      return f ⊛ return x  ≅⟨ ApplicativeFunctor.homomorphism f x ⟩
      return (f x)         ∎)
    helper fs xs p₁ p₂ p₁′ p₂′ R≡ xs≅ =
      helper′ fs xs p₁ p₂ p₁′ p₂′ R≡ xs≅
      where
      helper′ :
        ∀ {Tok R₁ R₁′ R₂} fs xs {xs′}
          (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs))
          (p₂ : ∞⟨ fs ⟩Parser Tok  R₁′      (flatten xs′)) →
        (∃₂ λ xs (p₁′ : Parser _ _ xs) → ♭? p₁ ≅P p₁′) →
        (∃₂ λ xs (p₂′ : Parser _ _ xs) → ♭? p₂ ≅P p₂′) →
        (R≡  : R₁ ≡ R₁′) →
        (xs≅ : xs ≅H xs′) →
        ∃₂ λ xs (p′ : Parser _ _ xs) → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≅P p′
      helper′ nothing nothing p₁ p₂ _ _ refl refl = _ , _ , (
        p₁ ⊛ p₂  ∎)
      helper′ (just fs) nothing p₁ p₂ _ (_   , p₂′ , p₂≅p₂′) refl refl
        with BSEq.empty-unique $ I.cong $ C.sound $ sym p₂≅p₂′
      helper′ (just fs) nothing p₁ p₂ _ (.[] , p₂′ , p₂≅p₂′) refl refl
        | refl = _ , _ , (
                 p₁ ⊛ p₂   ≅⟨ [ ◌ - ◌ - ○ - ○ ] ♭ p₁ ∎ ⊛ p₂≅p₂′ ⟩
                 p₁ ⊛ p₂′  ∎)
      helper′ nothing (just xs) p₁ p₂ (_   , p₁′ , p₁≅p₁′) _ refl refl
        with BSEq.empty-unique $ I.cong $ C.sound $ sym p₁≅p₁′
      helper′ nothing (just xs) p₁ p₂ (.[] , p₁′ , p₁≅p₁′) _ refl refl
        | refl = _ , _ , (
                 p₁  ⊛ p₂  ≅⟨ [ ○ - ○ - ◌ - ◌ ] p₁≅p₁′ ⊛ (♭ p₂ ∎) ⟩
                 p₁′ ⊛ p₂  ∎)
      helper′ (just fs) (just xs)
              p₁ p₂ (_ , p₁′ , p₁≅p₁′) (_ , p₂′ , p₂≅p₂′) refl refl =
        _ , _ , (
        p₁  ⊛ p₂   ≅⟨ [ ○ - ○ - ○ - ○ ] p₁≅p₁′ ⊛ p₂≅p₂′ ⟩
        p₁′ ⊛ p₂′  ∎)

  -- • _>>=_:

  simplify₁ (_>>=_ {xs = xs} {f = f} p₁ p₂) with simplify₁′ p₁
  ... | (._ , fail     , p₁≅∅)  = _ , _ , (
                                  p₁   >>= p₂         ≅⟨ [ f - ○ - xs - ○ ] p₁≅∅ >>= (λ x → ♭? (p₂ x) ∎) ⟩
                                  fail >>= (♭? ∘ p₂)  ≅⟨ Monad.left-zero (♭? ∘ p₂) ⟩
                                  fail                ∎)
  ... | (._ , return x , p₁≅ε) with simplify₁′ (p₂ x)
  ...   | (_ , p₂x′ , p₂x≅p₂x′) = _ , _ , (
                                  p₁       >>= p₂         ≅⟨ [ f - ○ - xs - ○ ] p₁≅ε >>= (λ x → ♭? (p₂ x) ∎) ⟩
                                  return x >>= (♭? ∘ p₂)  ≅⟨ Monad.left-identity x (♭? ∘ p₂) ⟩
                                  ♭? (p₂ x)               ≅⟨ p₂x≅p₂x′ ⟩
                                  p₂x′                    ∎)
  simplify₁ (p₁ >>= p₂) | (_ , p₁′ , p₁≅p₁′) with forced? p₁
  ... | just xs = _ , _ , (
                  p₁  >>= p₂         ≅⟨ [ ○ - ○ - forced?′ p₂ - ○ ] p₁≅p₁′ >>= (λ x → ♭? (p₂ x) ∎) ⟩
                  p₁′ >>= (♭? ∘ p₂)  ∎)
  ... | nothing = _ , _ , (
                  p₁ >>= p₂ ∎)

  -- • nonempty:

  simplify₁ (nonempty p) with simplify₁ p
  ... | (._ , fail , p≅∅)  = _ , _ , (
                             nonempty p     ≅⟨ nonempty p≅∅ ⟩
                             nonempty fail  ≅⟨ Nonempty.zero ⟩
                             fail           ∎)
  ... | (_  , p′   , p≅p′) = _ , _ , (
                             nonempty p   ≅⟨ nonempty p≅p′ ⟩
                             nonempty p′  ∎)

  -- • cast:

  simplify₁ (cast xs₁≈xs₂ p) with simplify₁ p
  ... | (_ , p′ , p≅p′) = _ , _ , (
                          cast xs₁≈xs₂ p  ≅⟨ Cast.correct ⟩
                          p               ≅⟨ p≅p′ ⟩
                          p′              ∎)

  -- Note that if an argument parser is delayed, then simplification
  -- is not applied recursively (because this could lead to
  -- non-termination).

  simplify₁′ : ∀ {Tok R R′ xs} {m : Maybe R′}
               (p : ∞⟨ m ⟩Parser Tok R xs) →
               ∃₂ λ xs (p′ : Parser Tok R xs) → ♭? p ≅P p′
  simplify₁′ {m = nothing} p = (_ , ♭ p , (♭ p ∎))
  simplify₁′ {m = just _}  p = simplify₁ p

-- Deep simplification.
--
-- The function simplify simplifies the first layer, then it traverses
-- the result and simplifies the following layers, and so on. The
-- extra traversals have been implemented to satisfy Agda's
-- termination checker; they could perhaps be avoided.
--
-- Note that simplifications in an upper layer do not get to take
-- advantage of simplifications performed in lower layers. Consider
-- ♯ p ⊛ token, for instance. If p can be simplified to fail, then one
-- might believe that ♯ p ⊛ token is simplified to fail as well.
-- However, this is only the case if p actually /computes/ to fail.
--
-- If simplification of the upper layer were dependent on complete
-- simplification of lower layers, then simplification could fail to
-- terminate. This does not mean that one cannot propagate /any/
-- information from lower layers to upper layers, though: one could
-- for instance perform partial simplification of lower layers, up to
-- a certain depth, before an upper layer is simplified.

mutual

  simplify : ∀ {Tok R xs} (p : Parser Tok R xs) →
             Parser Tok R (proj₁ $ simplify₁ p)
  simplify p = simplify↓ (proj₁ $ proj₂ $ simplify₁ p)

  private

    simplify↓ : ∀ {Tok R xs} → Parser Tok R xs → Parser Tok R xs
    simplify↓ (return x)       = return x
    simplify↓ fail             = fail
    simplify↓ token            = token
    simplify↓ (p₁ ∣ p₂)        = simplify↓ p₁ ∣ simplify↓ p₂
    simplify↓ (f <$> p)        = f <$> simplify↓ p
    simplify↓ (nonempty p)     = nonempty (simplify↓ p)
    simplify↓ (cast xs₁≈xs₂ p) = cast xs₁≈xs₂ (simplify↓ p)
    simplify↓ (p₁ ⊛ p₂)        with forced? p₁ | forced? p₂
    ... | just xs | just fs =   simplify↓      p₁  ⊛   simplify↓      p₂
    ... | just xs | nothing =   simplify↓      p₁  ⊛ ♯ simplify    (♭ p₂)
    ... | nothing | just fs = ♯ simplify    (♭ p₁) ⊛   simplify↓      p₂
    ... | nothing | nothing = ♯ simplify-[] (♭ p₁) ⊛ ♯ simplify-[] (♭ p₂)
    simplify↓ (p₁ >>= p₂)      with forced? p₁ | forced?′ p₂
    ... | just f  | just xs =   simplify↓      p₁  >>= λ x →   simplify↓      (p₂ x)
    ... | just f  | nothing =   simplify↓      p₁  >>= λ x → ♯ simplify    (♭ (p₂ x))
    ... | nothing | just xs = ♯ simplify    (♭ p₁) >>= λ x →   simplify↓      (p₂ x)
    ... | nothing | nothing = ♯ simplify-[] (♭ p₁) >>= λ x → ♯ simplify-[] (♭ (p₂ x))

    simplify-[] : ∀ {Tok R} → Parser Tok R [] → Parser Tok R []
    simplify-[] p =
      simplify↓ (P.subst (Parser _ _) ([]-lemma p) $
                   proj₁ $ proj₂ $ simplify₁ p)

    []-lemma : ∀ {Tok R} (p : Parser Tok R []) →
               proj₁ (simplify₁ p) ≡ []
    []-lemma = BSEq.empty-unique ∘ I.cong ∘ C.sound ∘
                 sym ∘ proj₂ ∘ proj₂ ∘ simplify₁

-- The simplifier is correct.

mutual

  correct : ∀ {Tok R xs} (p : Parser Tok R xs) → simplify p ≅P p
  correct p =
    simplify↓ (proj₁ simp)  ≅⟨ correct↓ (proj₁ simp) ⟩
    proj₁ simp              ≅⟨ sym $ proj₂ simp ⟩
    p                       ∎
    where simp = proj₂ $ simplify₁ p

  private

    correct↓ : ∀ {Tok R xs} (p : Parser Tok R xs) → simplify↓ p ≅P p
    correct↓ (return x)       = return x ∎
    correct↓ fail             = fail ∎
    correct↓ token            = token ∎
    correct↓ (p₁ ∣ p₂)        = correct↓ p₁ ∣′ correct↓ p₂
    correct↓ (f <$> p)        = (λ _ → refl) <$> correct↓ p
    correct↓ (nonempty p)     = nonempty (correct↓ p)
    correct↓ (cast xs₁≈xs₂ p) = cast (correct↓ p)
    correct↓ (p₁ ⊛ p₂)        with forced? p₁ | forced? p₂
    ... | just xs | just fs = [ just (○ , ○) - just (○ , ○) ]   correct↓      p₁  ⊛   correct↓      p₂
    ... | just xs | nothing = [ just (○ , ○) - nothing      ]   correct↓      p₁  ⊛ ♯ correct    (♭ p₂)
    ... | nothing | just fs = [ nothing      - just (○ , ○) ] ♯ correct    (♭ p₁) ⊛   correct↓      p₂
    ... | nothing | nothing = [ nothing      - nothing      ] ♯ correct-[] (♭ p₁) ⊛ ♯ correct-[] (♭ p₂)
    correct↓ (p₁ >>= p₂)      with forced? p₁ | forced?′ p₂
    ... | just f  | just xs = [ just (○ , ○) - just (○ , ○) ]   correct↓      p₁  >>= λ x →   correct↓      (p₂ x)
    ... | just f  | nothing = [ just (○ , ○) - nothing      ]   correct↓      p₁  >>= λ x → ♯ correct    (♭ (p₂ x))
    ... | nothing | just xs = [ nothing      - just (○ , ○) ] ♯ correct    (♭ p₁) >>= λ x →   correct↓      (p₂ x)
    ... | nothing | nothing = [ nothing      - nothing      ] ♯ correct-[] (♭ p₁) >>= λ x → ♯ correct-[] (♭ (p₂ x))

    correct-[] : ∀ {Tok R} (p : Parser Tok R []) → simplify-[] p ≅P p
    correct-[] p =
      simplify-[] p         ≅⟨ correct↓ (cast-[] $ proj₁ simp) ⟩
      cast-[] (proj₁ simp)  ≅⟨ Subst.correct ([]-lemma p) ⟩
      proj₁ simp            ≅⟨ sym $ proj₂ simp ⟩
      p                     ∎
      where
      simp    = proj₂ $ simplify₁ p
      cast-[] = P.subst (Parser _ _) ([]-lemma p)
