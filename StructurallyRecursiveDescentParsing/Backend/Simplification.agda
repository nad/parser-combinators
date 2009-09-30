------------------------------------------------------------------------
-- Simplification of parsers
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Backend.Simplification where

open import Algebra
open import Coinduction
open import Data.Bool
open import Data.Product
open import Data.Product1 using (∃₁₁; _,_; proj₁₁₁; proj₁₁₂)
open import Data.List as List
private module LM {Tok} = Monoid (List.monoid Tok)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality1 as Eq₁
  using (_≡₁_; refl)

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (sound; complete)
open import StructurallyRecursiveDescentParsing.Simplified.Lemmas

------------------------------------------------------------------------
-- Helpers

private

  force : ∀ {Tok R xs} (p : ∞₁ (Parser Tok R xs)) → ∃₁₁ λ p′ → ♭₁ p ≈ p′
  force p = (♭₁ p , (λ x∈ → x∈) , λ x∈ → x∈)

  -- A variant of cast.

  cast′ : ∀ {Tok R xs₁ xs₂} →
          xs₁ ≡ xs₂ → Parser Tok R xs₁ → Parser Tok R xs₂
  cast′ refl p = p

  cast⁺ : ∀ {Tok R xs₁ xs₂ x s} {p : Parser Tok R xs₁} →
          (eq : xs₁ ≡ xs₂) → x ∈ p · s → x ∈ cast′ eq p · s
  cast⁺ refl x∈p = x∈p

  cast⁻ : ∀ {Tok R xs₁ xs₂ x s} {p : Parser Tok R xs₁} →
          (eq : xs₁ ≡ xs₂) → x ∈ cast′ eq p · s → x ∈ p · s
  cast⁻ refl x∈p = x∈p

------------------------------------------------------------------------
-- Simplification

-- The function simplify₁ simplifies the first "layer" of a parser,
-- down to the first occurrences of ♯₁_. The following simplifications
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

  simplify₁ : ∀ {Tok R xs} (p : Parser Tok R xs) → ∃₁₁ λ p′ → p ≈ p′

  -- • return:

  simplify₁ (return x) = (return x , (λ x∈ → x∈) , λ x∈ → x∈)

  -- • fail:

  simplify₁ fail       = (fail     , (λ ())      , λ ())

  -- • token:

  simplify₁ token      = (token    , (λ x∈ → x∈) , λ x∈ → x∈)

  -- • _<$>_:

  simplify₁ (f <$> p) with simplify₁ p
  ... | (fail , p≈∅) = (fail , (λ {_} → helper) , λ ())
    where
    helper : f <$> p ⊑ fail
    helper (<$> x∈p) with proj₁₁₁ p≈∅ x∈p
    ... | ()
  ... | (return x , p≈ε) =
    (return (f x) , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : f <$> p ⊑ return (f x)
    helper₁ (<$> x∈p) with proj₁₁₁ p≈ε x∈p
    ... | return = return

    helper₂ : return (f x) ⊑ f <$> p
    helper₂ return = <$>_ {f = f} (proj₁₁₂ p≈ε return)
  ... | (p′ , p≈p′) = (f <$> p′ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : f <$> p ⊑ f <$> p′
    helper₁ (<$> x∈p) = <$> proj₁₁₁ p≈p′ x∈p

    helper₂ : f <$> p′ ⊑ f <$> p
    helper₂ (<$> x∈p′) = <$> proj₁₁₂ p≈p′ x∈p′

  -- • _∣_:

  simplify₁ (p₁ ∣ p₂) with simplify₁ p₁ | simplify₁ p₂
  simplify₁ (p₁ ∣ p₂) | (fail , p₁≈∅) | (p₂′ , p₂≈p₂′) =
    (p₂′ , (λ {_} → helper) , λ x∈ → ∣ʳ [] (proj₁₁₂ p₂≈p₂′ x∈))
    where
    helper : p₁ ∣ p₂ ⊑ p₂′
    helper (∣ʳ .[] x∈p₂) = proj₁₁₁ p₂≈p₂′ x∈p₂
    helper (∣ˡ     x∈p₁) with proj₁₁₁ p₁≈∅ x∈p₁
    ... | ()
  simplify₁ (p₁ ∣ p₂) | (_>>=_ {f = f} token p₁′ , p₁≈…)
                      | (token >>= p₂′           , p₂≈…) =
    ( token >>= (λ t → ♯? (♭? (p₁′ t) ∣ ♭? (p₂′ t)))
    , (λ {_} → helper₁) , λ {_} → helper₂
    )
    where
    helper₁ : p₁ ∣ p₂ ⊑ token >>= (λ t → ♯? (♭? (p₁′ t) ∣ ♭? (p₂′ t)))
    helper₁ (∣ˡ     x∈p₁) with proj₁₁₁ p₁≈… x∈p₁
    helper₁ (∣ˡ     x∈p₁) | token >>= x∈p₁′ = token >>= ∣ˡ x∈p₁′
    helper₁ (∣ʳ .[] x∈p₂) with proj₁₁₁ p₂≈… x∈p₂
    helper₁ (∣ʳ .[] x∈p₂) | _>>=_ {x = x} token x∈p₂′ =
      token >>= ∣ʳ (f x) x∈p₂′

    helper₂ : token >>= (λ t → ♯? (♭? (p₁′ t) ∣ ♭? (p₂′ t))) ⊑ p₁ ∣ p₂
    helper₂ (token >>= ∣ˡ    y∈p₁′x) = ∣ˡ    (proj₁₁₂ p₁≈… (token >>= y∈p₁′x))
    helper₂ (token >>= ∣ʳ ._ y∈p₂′x) = ∣ʳ [] (proj₁₁₂ p₂≈… (token >>= y∈p₂′x))
  simplify₁ (p₁ ∣ p₂) | (p₁′ , p₁≈p₁′) | (fail , p₂≈∅) =
    (cast′ lem p₁′ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    lem = sym (proj₂ LM.identity _)

    helper₁ : p₁ ∣ p₂ ⊑ cast′ lem p₁′
    helper₁ (∣ˡ    x∈p₁) = cast⁺ lem (proj₁₁₁ p₁≈p₁′ x∈p₁)
    helper₁ (∣ʳ ._ x∈p₂) with proj₁₁₁ p₂≈∅ x∈p₂
    ... | ()

    helper₂ : cast′ lem p₁′ ⊑ p₁ ∣ p₂
    helper₂ x∈p₁′ = ∣ˡ (proj₁₁₂ p₁≈p₁′ (cast⁻ lem x∈p₁′))
  simplify₁ (_∣_ {xs₁ = xs₁} p₁ p₂) | (p₁′ , p₁≈p₁′) | (p₂′ , p₂≈p₂′) =
    (p₁′ ∣ p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : p₁ ∣ p₂ ⊑ p₁′ ∣ p₂′
    helper₁ (∣ˡ      x∈p₁) = ∣ˡ     (proj₁₁₁ p₁≈p₁′ x∈p₁)
    helper₁ (∣ʳ .xs₁ x∈p₂) = ∣ʳ xs₁ (proj₁₁₁ p₂≈p₂′ x∈p₂)

    helper₂ : p₁′ ∣ p₂′ ⊑ p₁ ∣ p₂
    helper₂ (∣ˡ      x∈p₁′) = ∣ˡ     (proj₁₁₂ p₁≈p₁′ x∈p₁′)
    helper₂ (∣ʳ .xs₁ x∈p₂′) = ∣ʳ xs₁ (proj₁₁₂ p₂≈p₂′ x∈p₂′)

  -- • _⊛_:

  simplify₁ (p₁ ⊛ p₂) =
    helper _ _ (simplify₁′ p₁) (simplify₁′ p₂) refl refl
    where
    -- token ⊛ token is never type correct, but Agda's case-splitting
    -- machinery cannot see that it is not, so instead
    -- of a with clause the following ugly machinery is used.

    cast₁ : ∀ {Tok R R₁ R₁′ xs xs′} {ys : List R} →
            (R≡  : R₁ ≡₁ R₁′) → xs ≅ xs′ →
            ∞? (Parser Tok R₁′ xs′) ys →
            ∞? (Parser Tok R₁  xs ) ys
    cast₁ refl refl p = p

    helper : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
               (p₁ : ∞? (Parser Tok (R₁ → R₂) fs ) xs)
               (p₂ : ∞? (Parser Tok  R₁′      xs′) fs) →
             (∃₁₁ λ p₁′ → ♭? p₁ ≈ p₁′) →
             (∃₁₁ λ p₂′ → ♭? p₂ ≈ p₂′) →
             (R≡  : R₁ ≡₁ R₁′) →
             (xs≅ : xs ≅ xs′) →
             ∃₁₁ λ p′ → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≈ p′
    helper {xs = xs} p₁ p₂ (fail , p₁≈∅) _ refl refl =
      (cast′ lem fail , (λ {_} → helper₁) , λ {_} → helper₂)
      where
      lem = sym (>>=-∅ xs)

      helper₁ : p₁ ⊛ p₂ ⊑ cast′ lem fail
      helper₁ (f∈p₁ ⊛ x∈p₂) with proj₁₁₁ p₁≈∅ f∈p₁
      ... | ()

      helper₂ : cast′ lem fail ⊑ p₁ ⊛ p₂
      helper₂ x∈∅ with cast⁻ lem x∈∅
      ... | ()
    helper p₁ p₂ _ (fail , p₂≈∅) refl refl =
      (fail , (λ {_} → helper₁) , λ ())
      where
      helper₁ : p₁ ⊛ p₂ ⊑ fail
      helper₁ (f∈p₁ ⊛ x∈p₂) with proj₁₁₁ p₂≈∅ x∈p₂
      ... | ()
    helper p₁ p₂ (return f , p₁≈ε) (return x , p₂≈ε) refl refl =
      (return (f x) , (λ {_} → helper₁) , λ {_} → helper₂)
      where
      helper₁ : p₁ ⊛ p₂ ⊑ return (f x)
      helper₁ (f∈p₁ ⊛ x∈p₂) with proj₁₁₁ p₁≈ε f∈p₁ | proj₁₁₁ p₂≈ε x∈p₂
      ... | return | return = return

      helper₂ : return (f x) ⊑ p₁ ⊛ p₂
      helper₂ return = proj₁₁₂ p₁≈ε return ⊛ proj₁₁₂ p₂≈ε return
    helper p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′) R≡ xs≅ =
      helper′ p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′) R≡ xs≅
      where
      helper′ : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
                  (p₁ : ∞? (Parser Tok (R₁ → R₂) fs ) xs)
                  (p₂ : ∞? (Parser Tok  R₁′      xs′) fs) →
                (∃₁₁ λ p₁′ → ♭? p₁ ≈ p₁′) →
                (∃₁₁ λ p₂′ → ♭? p₂ ≈ p₂′) →
                (R≡  : R₁ ≡₁ R₁′) →
                (xs≅ : xs ≅ xs′) →
                ∃₁₁ λ p′ → p₁ ⊛ cast₁ R≡ xs≅ p₂ ≈ p′
      helper′ {fs = fs} {xs} p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′)
              refl refl =
        ( ♯? p₁′ ⊛ ♯? p₂′
        , (λ {_} → helper₁) , λ {_} → helper₂
        )
        where
        helper₁ : p₁ ⊛ p₂ ⊑ ♯? p₁′ ⊛ ♯? p₂′
        helper₁ (f∈p₁ ⊛ x∈p₂) =
          cast∈ refl (Eq₁.sym (♭?♯? xs)) refl (proj₁₁₁ p₁≈p₁′ f∈p₁) ⊛
          cast∈ refl (Eq₁.sym (♭?♯? fs)) refl (proj₁₁₁ p₂≈p₂′ x∈p₂)

        helper₂ : ♯? p₁′ ⊛ ♯? p₂′ ⊑ p₁ ⊛ p₂
        helper₂ (f∈p₁′ ⊛ x∈p₂′) =
          proj₁₁₂ p₁≈p₁′ (cast∈ refl (♭?♯? xs) refl f∈p₁′) ⊛
          proj₁₁₂ p₂≈p₂′ (cast∈ refl (♭?♯? fs) refl x∈p₂′)

  -- • _>>=_:

  simplify₁ (p₁ >>= p₂) with simplify₁ p₁
  simplify₁ (p₁ >>= p₂) | (fail , p₁≈∅) = (fail , (λ {_} → helper) , λ ())
    where
    helper : p₁ >>= p₂ ⊑ fail
    helper (x∈p₁ >>= y∈p₂x) with proj₁₁₁ p₁≈∅ x∈p₁
    ... | ()
  simplify₁ (p₁ >>= p₂) | (return x , p₁≈ε) with simplify₁′ (p₂ x)
  simplify₁ (p₁ >>= p₂) | (return x , p₁≈ε) | (p₂′ , p₂x≈p₂′) =
    (cast′ lem p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    lem = sym (proj₂ LM.identity _)

    helper₁ : p₁ >>= p₂ ⊑ cast′ lem p₂′
    helper₁ (_>>=_ {y = y} {s₂ = s₂} x∈p₁ y∈p₂x) =
      cast⁺ lem (helper (proj₁₁₁ p₁≈ε x∈p₁) y∈p₂x)
      where
      helper : ∀ {x′ s₁} → x′ ∈ return x · s₁ → y ∈ ♭? (p₂ x′) · s₂ →
               y ∈ p₂′ · s₁ ++ s₂
      helper return x∈p₂ = proj₁₁₁ p₂x≈p₂′ x∈p₂

    helper₂ : cast′ lem p₂′ ⊑ p₁ >>= p₂
    helper₂ y∈p₂′ =
      _>>=_ {x = x} {p₂ = p₂} (proj₁₁₂ p₁≈ε (return {x = x}))
                              (proj₁₁₂ p₂x≈p₂′ (cast⁻ lem y∈p₂′))
  simplify₁ (p₁ >>= p₂) | (p₁′ , p₁≈p₁′) =
    (p₁′ >>= p₂ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : p₁ >>= p₂ ⊑ p₁′ >>= p₂
    helper₁ (x∈p₁ >>= y∈p₂x) = proj₁₁₁ p₁≈p₁′ x∈p₁ >>= y∈p₂x

    helper₂ : p₁′ >>= p₂ ⊑ p₁ >>= p₂
    helper₂ (x∈p₁ >>= y∈p₂x) = proj₁₁₂ p₁≈p₁′ x∈p₁ >>= y∈p₂x

  -- • _>>=!_:

  simplify₁ (p₁ >>=! p₂) with force p₁
  simplify₁ (p₁ >>=! p₂) | (fail , p₁≈∅) = (fail , (λ {_} → helper) , λ ())
    where
    helper : p₁ >>=! p₂ ⊑ fail
    helper (x∈p₁ >>=! y∈p₂x) with proj₁₁₁ p₁≈∅ x∈p₁
    ... | ()
  simplify₁ (p₁ >>=! p₂) | (return x , p₁≈ε) with simplify₁′ (p₂ x)
  simplify₁ (p₁ >>=! p₂) | (return x , p₁≈ε) | (p₂′ , p₂x≈p₂′) =
    (cast′ lem p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    lem = sym (proj₂ LM.identity _)

    helper₁ : p₁ >>=! p₂ ⊑ cast′ lem p₂′
    helper₁ (_>>=!_ {y = y} {s₂ = s₂} x∈p₁ y∈p₂x) =
      cast⁺ lem (helper (proj₁₁₁ p₁≈ε x∈p₁) y∈p₂x)
      where
      helper : ∀ {x′ s₁} → x′ ∈ return x · s₁ → y ∈ ♭? (p₂ x′) · s₂ →
               y ∈ p₂′ · s₁ ++ s₂
      helper return x∈p₂ = proj₁₁₁ p₂x≈p₂′ x∈p₂

    helper₂ : cast′ lem p₂′ ⊑ p₁ >>=! p₂
    helper₂ y∈p₂′ =
      _>>=!_ {x = x} {p₂ = p₂} (proj₁₁₂ p₁≈ε (return {x = x}))
                               (proj₁₁₂ p₂x≈p₂′ (cast⁻ lem y∈p₂′))
  simplify₁ (p₁ >>=! p₂) | (p₁′ , p₁≈p₁′) =
    (♯₁ p₁′ >>=! p₂ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : p₁ >>=! p₂ ⊑ _ >>=! p₂
    helper₁ (x∈p₁ >>=! y∈p₂x) = proj₁₁₁ p₁≈p₁′ x∈p₁ >>=! y∈p₂x

    helper₂ : _ >>=! p₂ ⊑ p₁ >>=! p₂
    helper₂ (x∈p₁ >>=! y∈p₂x) = proj₁₁₂ p₁≈p₁′ x∈p₁ >>=! y∈p₂x

  -- • nonempty:

  simplify₁ (nonempty p) with simplify₁ p
  simplify₁ (nonempty p) | (fail , p≈∅) =
    (fail , (λ {_} → helper) , λ ())
    where
    helper : nonempty p ⊑ fail
    helper (nonempty x∈p) with proj₁₁₁ p≈∅ x∈p
    ... | ()
  simplify₁ (nonempty p) | (p′ , p≈p′) =
    (nonempty p′ , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : nonempty p ⊑ nonempty p′
    helper₁ (nonempty x∈p) = nonempty (proj₁₁₁ p≈p′ x∈p)

    helper₂ : nonempty p′ ⊑ nonempty p
    helper₂ (nonempty x∈p′) = nonempty (proj₁₁₂ p≈p′ x∈p′)

  -- • cast:

  simplify₁ (cast refl p) with simplify₁ p
  simplify₁ (cast refl p) | (p′ , p≈p′) =
    (p′ , (λ {_} → helper) , λ x∈ → cast (proj₁₁₂ p≈p′ x∈))
    where
    helper : cast refl p ⊑ p′
    helper (cast x∈p) = proj₁₁₁ p≈p′ x∈p

  -- Note that if an argument parser is delayed, then simplification
  -- is not applied recursively (because this could lead to
  -- non-termination). Partial simplification, for instance up to a
  -- predetermined depth, would be possible, but for simplicity
  -- delayed parsers are simply forced and returned.

  simplify₁′ : ∀ {Tok R R′ xs} {ys : List R′}
               (p : ∞? (Parser Tok R xs) ys) → ∃₁₁ λ p′ → ♭? p ≈ p′
  simplify₁′ ⟪ p ⟫ = (♭₁ p , (λ x∈ → x∈) , λ x∈ → x∈)
  simplify₁′ ⟨ p ⟩ = simplify₁ p

-- The projections of simplify₁.

simplify : ∀ {Tok R xs} → Parser Tok R xs → Parser Tok R xs
simplify p = proj₁₁₁ (simplify₁ p)

sound : ∀ {Tok R xs} {p : Parser Tok R xs} → simplify p ⊑ p
sound = proj₁₁₂ (proj₁₁₂ (simplify₁ _))

complete : ∀ {Tok R xs} {p : Parser Tok R xs} → p ⊑ simplify p
complete = proj₁₁₁ (proj₁₁₂ (simplify₁ _))
