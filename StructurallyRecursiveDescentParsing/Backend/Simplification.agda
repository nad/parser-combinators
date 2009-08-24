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

private

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

  -- A workaround for the nominal equality which Agda uses to compare
  -- expressions.

  infix 10 ♯′_

  ♯′_ : ∀ {T} → T → ∞₁ T
  ♯′_ = ♯₁_

-- The functions below simplify parsers. The following simplifications
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
-- cast eq p                   → p
--
-- Note that simplification is not performed (co)recursively under
-- ♯₁_.
--
-- An example of a possible future addition:
--
-- (p₁ >>= p₂) >>= p₃ → p₁ >>= λ x → p₂ >>= p₃

simplify′ : ∀ {Tok R xs} (p : Parser Tok R xs) → ∃₁₁ λ p′ → p ≈ p′
simplify′ (return x) = (return x , (λ x∈ → x∈) , λ x∈ → x∈)
simplify′ fail       = (fail     , (λ ())      , λ ())
simplify′ token      = (token    , (λ x∈ → x∈) , λ x∈ → x∈)

simplify′ (f <$> p) with simplify′ p
... | (fail , p≈∅) = (fail , (λ {_} → helper) , λ ())
  where
  helper : ∀ {x s} → x ∈ f <$> p · s → x ∈ fail · s
  helper (.f <$> x∈p) with proj₁₁₁ p≈∅ x∈p
  ... | ()
... | (return x , p≈ε) =
  (return (f x) , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : ∀ {y s} → y ∈ f <$> p · s → y ∈ return (f x) · s
  helper₁ (.f <$> x∈p) with proj₁₁₁ p≈ε x∈p
  ... | return = return

  helper₂ : ∀ {y s} → y ∈ return (f x) · s → y ∈ f <$> p · s
  helper₂ return = f <$> proj₁₁₂ p≈ε return
... | (p′ , p≈p′) = (f <$> p′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : ∀ {x s} → x ∈ f <$> p · s → x ∈ f <$> p′ · s
  helper₁ (.f <$> x∈p) = f <$> proj₁₁₁ p≈p′ x∈p

  helper₂ : ∀ {x s} → x ∈ f <$> p′ · s → x ∈ f <$> p · s
  helper₂ (.f <$> x∈p′) = f <$> proj₁₁₂ p≈p′ x∈p′

simplify′ (p₁ ∣ p₂) with simplify′ p₁ | simplify′ p₂
simplify′ (p₁ ∣ p₂) | (fail , p₁≈∅) | (p₂′ , p₂≈p₂′) =
  (p₂′ , (λ {_} → helper) , λ x∈ → ∣ʳ [] (proj₁₁₂ p₂≈p₂′ x∈))
  where
  helper : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ p₂′ · s
  helper (∣ʳ .[] x∈p₂) = proj₁₁₁ p₂≈p₂′ x∈p₂
  helper (∣ˡ     x∈p₁) with proj₁₁₁ p₁≈∅ x∈p₁
  ... | ()
simplify′ (p₁ ∣ p₂) | (_>>=_ {f = f} token p₁′ , p₁≈…)
                    | (token >>= p₂′           , p₂≈…) =
  ( token >>= (λ t → ♯′ (♭₁ (p₁′ t) ∣ ♭₁ (p₂′ t)))
  , (λ {_} → helper₁) , λ {_} → helper₂
  )
  where
  helper₁ : ∀ {x s} →
            x ∈ p₁ ∣ p₂ · s →
            x ∈ token >>= (λ t → ♯′ (♭₁ (p₁′ t) ∣ ♭₁ (p₂′ t))) · s
  helper₁ (∣ˡ     x∈p₁) with proj₁₁₁ p₁≈… x∈p₁
  helper₁ (∣ˡ     x∈p₁) | token >>= x∈p₁′ = token >>= ∣ˡ x∈p₁′
  helper₁ (∣ʳ .[] x∈p₂) with proj₁₁₁ p₂≈… x∈p₂
  helper₁ (∣ʳ .[] x∈p₂) | _>>=_ {x = x} token x∈p₂′ =
    token >>= ∣ʳ (f x) x∈p₂′

  helper₂ : ∀ {x s} →
            x ∈ token >>= (λ t → ♯′ (♭₁ (p₁′ t) ∣ ♭₁ (p₂′ t))) · s →
            x ∈ p₁ ∣ p₂ · s
  helper₂ (token >>= ∣ˡ    y∈p₁′x) = ∣ˡ    (proj₁₁₂ p₁≈… (token >>= y∈p₁′x))
  helper₂ (token >>= ∣ʳ ._ y∈p₂′x) = ∣ʳ [] (proj₁₁₂ p₂≈… (token >>= y∈p₂′x))
simplify′ (p₁ ∣ p₂) | (p₁′ , p₁≈p₁′) | (fail , p₂≈∅) =
  (cast′ lem p₁′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  lem = sym (proj₂ LM.identity _)

  helper₁ : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ cast′ lem p₁′ · s
  helper₁ (∣ˡ    x∈p₁) = cast⁺ lem (proj₁₁₁ p₁≈p₁′ x∈p₁)
  helper₁ (∣ʳ ._ x∈p₂) with proj₁₁₁ p₂≈∅ x∈p₂
  ... | ()

  helper₂ : ∀ {x s} → x ∈ cast′ lem p₁′ · s → x ∈ p₁ ∣ p₂ · s
  helper₂ x∈p₁′ = ∣ˡ (proj₁₁₂ p₁≈p₁′ (cast⁻ lem x∈p₁′))
simplify′ (_∣_ {xs₁ = xs₁} p₁ p₂) | (p₁′ , p₁≈p₁′) | (p₂′ , p₂≈p₂′) =
  (p₁′ ∣ p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ p₁′ ∣ p₂′ · s
  helper₁ (∣ˡ      x∈p₁) = ∣ˡ     (proj₁₁₁ p₁≈p₁′ x∈p₁)
  helper₁ (∣ʳ .xs₁ x∈p₂) = ∣ʳ xs₁ (proj₁₁₁ p₂≈p₂′ x∈p₂)

  helper₂ : ∀ {x s} → x ∈ p₁′ ∣ p₂′ · s → x ∈ p₁ ∣ p₂ · s
  helper₂ (∣ˡ      x∈p₁′) = ∣ˡ     (proj₁₁₂ p₁≈p₁′ x∈p₁′)
  helper₂ (∣ʳ .xs₁ x∈p₂′) = ∣ʳ xs₁ (proj₁₁₂ p₂≈p₂′ x∈p₂′)

simplify′ (_∶_⊛_ xs {fs} p₁ p₂) =
  helper _ _ (simplify″ (null xs) p₁) (simplify″ (null fs) p₂)
         refl refl
  where
  -- Note that if an argument parser is delayed, then simplification
  -- is not applied recursively (because this could lead to
  -- non-termination). Partial simplification, for instance up to a
  -- predetermined depth, would be possible, but for simplicity
  -- delayed parsers are simply forced and returned.

  simplify″ : ∀ {Tok R xs} b (p : ∞? b (Parser Tok R xs)) →
              ∃₁₁ λ p′ → ♭? b p ≈ p′
  simplify″ true  p = (♭₁ p , (λ x∈ → x∈) , λ x∈ → x∈)
  simplify″ false p = simplify′ p

  -- [] ∶ token ⊛ token is never type correct, but Agda's
  -- case-splitting machinery cannot see that it is not, so instead
  -- of a with clause the following ugly machinery is used.

  cast₁ : ∀ b {Tok R₁ R₁′ xs xs′} →
          (R≡  : R₁ ≡₁ R₁′) → xs ≅ xs′ →
          ∞? b (Parser Tok R₁′ xs′) →
          ∞? b (Parser Tok R₁  xs)
  cast₁ _ refl refl p = p

  helper : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
             (p₁ : ∞? (null xs) (Parser Tok (R₁ → R₂) fs) )
             (p₂ : ∞? (null fs) (Parser Tok  R₁′      xs′)) →
           (∃₁₁ λ p₁′ → ♭? (null xs) p₁ ≈ p₁′) →
           (∃₁₁ λ p₂′ → ♭? (null fs) p₂ ≈ p₂′) →
           (R≡  : R₁ ≡₁ R₁′) →
           (xs≅ : xs ≅ xs′) →
           ∃₁₁ λ p′ → xs ∶ p₁ ⊛ cast₁ (null fs) R≡ xs≅ p₂ ≈ p′
  helper {xs = xs} p₁ p₂ (fail , p₁≈∅) _ refl refl =
    (cast′ lem fail , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    lem = sym (>>=-∅ xs)

    helper₁ : ∀ {x s} → x ∈ xs ∶ p₁ ⊛ p₂ · s → x ∈ cast′ lem fail · s
    helper₁ (f∈p₁ ⊛ x∈p₂) with proj₁₁₁ p₁≈∅ f∈p₁
    ... | ()

    helper₂ : ∀ {x s} → x ∈ cast′ lem fail · s → x ∈ xs ∶ p₁ ⊛ p₂ · s
    helper₂ x∈∅ with cast⁻ lem x∈∅
    ... | ()
  helper p₁ p₂ _ (fail , p₂≈∅) refl refl =
    (fail , (λ {_} → helper₁) , λ ())
    where
    helper₁ : ∀ {x s} → x ∈ [] ∶ p₁ ⊛ p₂ · s → x ∈ fail · s
    helper₁ (f∈p₁ ⊛ x∈p₂) with proj₁₁₁ p₂≈∅ x∈p₂
    ... | ()
  helper p₁ p₂ (return f , p₁≈ε) (return x , p₂≈ε) refl refl =
    (return (f x) , (λ {_} → helper₁) , λ {_} → helper₂)
    where
    helper₁ : ∀ {y s} → y ∈ [ x ] ∶ p₁ ⊛ p₂ · s → y ∈ return (f x) · s
    helper₁ (f∈p₁ ⊛ x∈p₂) with proj₁₁₁ p₁≈ε f∈p₁ | proj₁₁₁ p₂≈ε x∈p₂
    ... | return | return = return

    helper₂ : ∀ {y s} → y ∈ return (f x) · s → y ∈ [ x ] ∶ p₁ ⊛ p₂ · s
    helper₂ return = proj₁₁₂ p₁≈ε return ⊛ proj₁₁₂ p₂≈ε return
  helper {fs = fs} {xs} p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′) R≡ xs≅ =
    helper′ p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′) R≡ xs≅
    where
    helper′ : ∀ {Tok R₁ R₁′ R₂ fs xs xs′}
                (p₁ : ∞? (null xs) (Parser Tok (R₁ → R₂) fs) )
                (p₂ : ∞? (null fs) (Parser Tok  R₁′      xs′)) →
              (∃₁₁ λ p₁′ → ♭? (null xs) p₁ ≈ p₁′) →
              (∃₁₁ λ p₂′ → ♭? (null fs) p₂ ≈ p₂′) →
              (R≡  : R₁ ≡₁ R₁′) →
              (xs≅ : xs ≅ xs′) →
              ∃₁₁ λ p′ → xs ∶ p₁ ⊛ cast₁ (null fs) R≡ xs≅ p₂ ≈ p′
    helper′ {fs = fs} {xs} p₁ p₂ (p₁′ , p₁≈p₁′) (p₂′ , p₂≈p₂′)
            refl refl =
      ( xs ∶ ♯? (null xs) p₁′ ⊛ ♯? (null fs) p₂′
      , (λ {_} → helper₁) , λ {_} → helper₂
      )
      where
      helper₁ : ∀ {x s} →
                x ∈ xs ∶              p₁  ⊛              p₂  · s →
                x ∈ xs ∶ ♯? (null xs) p₁′ ⊛ ♯? (null fs) p₂′ · s
      helper₁ (f∈p₁ ⊛ x∈p₂) =
        cast∈ refl (Eq₁.sym (♭?♯? (null xs))) refl (proj₁₁₁ p₁≈p₁′ f∈p₁)
          ⊛
        cast∈ refl (Eq₁.sym (♭?♯? (null fs))) refl (proj₁₁₁ p₂≈p₂′ x∈p₂)

      helper₂ : ∀ {x s} →
                x ∈ xs ∶ ♯? (null xs) p₁′ ⊛ ♯? (null fs) p₂′ · s →
                x ∈ xs ∶              p₁  ⊛              p₂  · s
      helper₂ (f∈p₁′ ⊛ x∈p₂′) =
        proj₁₁₂ p₁≈p₁′ (cast∈ refl (♭?♯? (null xs)) refl f∈p₁′)
          ⊛
        proj₁₁₂ p₂≈p₂′ (cast∈ refl (♭?♯? (null fs)) refl x∈p₂′)

simplify′ (p₁ >>= p₂) with simplify′ p₁
simplify′ (p₁ >>= p₂) | (fail , p₁≈∅) = (fail , (λ {_} → helper) , λ ())
  where
  helper : ∀ {x s} → x ∈ p₁ >>= p₂ · s → x ∈ fail · s
  helper (x∈p₁ >>= y∈p₂x) with proj₁₁₁ p₁≈∅ x∈p₁
  ... | ()
simplify′ (p₁ >>= p₂) | (return x , p₁≈ε) with simplify′ (p₂ x)
simplify′ (p₁ >>= p₂) | (return x , p₁≈ε) | (p₂′ , p₂x≈p₂′) =
  (cast′ lem p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  lem = sym (proj₂ LM.identity _)

  helper₁ : ∀ {y s} → y ∈ p₁ >>= p₂ · s → y ∈ cast′ lem p₂′ · s
  helper₁ (_>>=_ {y = y} {s₂ = s₂} x∈p₁ y∈p₂x) =
    cast⁺ lem (helper (proj₁₁₁ p₁≈ε x∈p₁) y∈p₂x)
    where
    helper : ∀ {x′ s₁} → x′ ∈ return x · s₁ → y ∈ p₂ x′ · s₂ →
             y ∈ p₂′ · s₁ ++ s₂
    helper return x∈p₂ = proj₁₁₁ p₂x≈p₂′ x∈p₂

  helper₂ : ∀ {y s} → y ∈ cast′ lem p₂′ · s → y ∈ p₁ >>= p₂ · s
  helper₂ y∈p₂′ =
    _>>=_ {x = x} {p₂ = p₂} (proj₁₁₂ p₁≈ε (return {x = x}))
                            (proj₁₁₂ p₂x≈p₂′ (cast⁻ lem y∈p₂′))
simplify′ (p₁ >>= p₂) | (p₁′ , p₁≈p₁′) =
  (p₁′ >>= p₂ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : ∀ {y s} → y ∈ p₁ >>= p₂ · s → y ∈ p₁′ >>= p₂ · s
  helper₁ (x∈p₁ >>= y∈p₂x) = proj₁₁₁ p₁≈p₁′ x∈p₁ >>= y∈p₂x

  helper₂ : ∀ {y s} → y ∈ p₁′ >>= p₂ · s → y ∈ p₁ >>= p₂ · s
  helper₂ (x∈p₁ >>= y∈p₂x) = proj₁₁₂ p₁≈p₁′ x∈p₁ >>= y∈p₂x

simplify′ (cast refl p) with simplify′ p
simplify′ (cast refl p) | (p′ , p≈p′) =
  (p′ , (λ {_} → helper) , λ x∈ → cast (proj₁₁₂ p≈p′ x∈))
  where
  helper : ∀ {x s} → x ∈ cast refl p · s → x ∈ p′ · s
  helper (cast x∈p) = proj₁₁₁ p≈p′ x∈p

simplify : ∀ {Tok R xs} → Parser Tok R xs → Parser Tok R xs
simplify p = proj₁₁₁ (simplify′ p)

correct : ∀ {Tok R xs} {p : Parser Tok R xs} → p ≈ simplify p
correct = proj₁₁₂ (simplify′ _)
