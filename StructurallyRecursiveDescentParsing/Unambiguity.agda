------------------------------------------------------------------------
-- Unambiguity
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Unambiguity where

open import Data.Bool
open import Data.List hiding (map)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1 using (refl)

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (sound; complete)

------------------------------------------------------------------------
-- Definition

-- A parser is unambiguous if it can yield at most one result for any
-- given input.
--
-- Note that this definition is a bit more general than the following
-- definition of unambiguity: "A grammar is unambiguous if there is at
-- most one parse tree which flattens to any given string."
--
-- Note also that this definition uses propositional equality, both
-- for the return values (x₁ and x₂) and for the input string (s). In
-- some cases other choices may be more useful.

Unambiguous : ∀ {Tok R xs} → Parser Tok R xs → Set1
Unambiguous p = ∀ {x₁ x₂ s} → x₁ ∈ p · s → x₂ ∈ p · s → x₁ ≡ x₂

------------------------------------------------------------------------
-- A more concrete characterisation of unambiguity

-- Note that this definition is inductive.

data Unambiguous′ {Tok} : ∀ {R xs} → Parser Tok R xs → Set1 where
  return   : ∀ {R} {x : R} → Unambiguous′ (return x)
  fail     : ∀ {R} → Unambiguous′ (fail {R = R})
  token    : Unambiguous′ token
  choice   : ∀ {R xs₁ xs₂} {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (u₁ : Unambiguous′ p₁) (u₂ : Unambiguous′ p₂) →
             (u : ∀ {x₁ x₂ s} → x₁ ∈ p₁ · s → x₂ ∈ p₂ · s → x₁ ≡ x₂) →
             Unambiguous′ (p₁ ∣ p₂)
  map      : ∀ {R₁ R₂ xs} {f : R₁ → R₂} {p : Parser Tok R₁ xs}
             (u : ∀ {x₁ x₂ s} → x₁ ∈ p · s → x₂ ∈ p · s → f x₁ ≡ f x₂) →
             Unambiguous′ (f <$> p)
  app      : ∀ {R₁ R₂ fs} xs
               {p₁ : ∞? (Parser Tok (R₁ → R₂) fs) xs}
               {p₂ : ∞? (Parser Tok R₁        xs) fs}
             (u : ∀ {f₁ f₂ x₁ x₂ s s₁ s₂ s₃ s₄} →
                f₁ ∈ ♭? p₁ · s₁ → x₁ ∈ ♭? p₂ · s₂ → s₁ ++ s₂ ≡ s →
                f₂ ∈ ♭? p₁ · s₃ → x₂ ∈ ♭? p₂ · s₄ → s₃ ++ s₄ ≡ s →
                f₁ x₁ ≡ f₂ x₂) →
             Unambiguous′ (p₁ ⊛ p₂)
  bind     : ∀ {R₁ R₂ xs} {f : R₁ → List R₂}
               {p₁ : Parser Tok R₁ xs}
               {p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs}
             (u : ∀ {x₁ x₂ y₁ y₂ s s₁ s₂ s₃ s₄} →
                x₁ ∈ p₁ · s₁ → y₁ ∈ ♭? (p₂ x₁) · s₂ → s₁ ++ s₂ ≡ s →
                x₂ ∈ p₁ · s₃ → y₂ ∈ ♭? (p₂ x₂) · s₄ → s₃ ++ s₄ ≡ s →
                y₁ ≡ y₂) →
             Unambiguous′ (p₁ >>= p₂)
  nonempty : ∀ {R xs} {p : Parser Tok R xs}
             (u : ∀ {x₁ x₂ t s} →
                  x₁ ∈ p · t ∷ s → x₂ ∈ p · t ∷ s → x₁ ≡ x₂) →
             Unambiguous′ (nonempty p)
  cast     : ∀ {R xs₁ xs₂} {eq : xs₁ ≡ xs₂} {p : Parser Tok R xs₁}
             (u : Unambiguous′ p) → Unambiguous′ (cast eq p)

-- The two definitions are equivalent.

sound : ∀ {Tok R xs} {p : Parser Tok R xs} →
        Unambiguous′ p → Unambiguous p
sound return           return      return       = refl
sound fail             ()          ()
sound token            token       token        = refl
sound (choice u₁ u₂ u) (∣ˡ   x∈p₁) (∣ˡ    y∈p₁) =      sound u₁ x∈p₁ y∈p₁
sound (choice u₁ u₂ u) (∣ˡ   x∈p₁) (∣ʳ _  y∈p₂) =      u        x∈p₁ y∈p₂
sound (choice u₁ u₂ u) (∣ʳ _ x∈p₂) (∣ˡ    y∈p₁) = sym (u        y∈p₁ x∈p₂)
sound (choice u₁ u₂ u) (∣ʳ _ x∈p₂) (∣ʳ ._ y∈p₂) =      sound u₂ x∈p₂ y∈p₂
sound (map u)          (f <$> x∈p) (.f <$> y∈p) = u x∈p y∈p
sound (app xs {p₁ = p₁} {p₂} u) x∈p y∈p = helper x∈p y∈p refl
  where
  helper : ∀ {fx₁ fx₂ s₁ s₂} →
           fx₁ ∈ p₁ ⊛ p₂ · s₁ → fx₂ ∈ p₁ ⊛ p₂ · s₂ →
           s₁ ≡ s₂ → fx₁ ≡ fx₂
  helper (f∈p₁ ⊛ x∈p₂) (f′∈p₁ ⊛ x′∈p₂) eq =
    u f∈p₁ x∈p₂ eq f′∈p₁ x′∈p₂ refl
sound (bind   {p₁ = p₁} {p₂} u) x∈p y∈p = helper x∈p y∈p refl
  where
  helper : ∀ {x₁ x₂ s₁ s₂} →
           x₁ ∈ p₁ >>= p₂ · s₁ → x₂ ∈ p₁ >>= p₂ · s₂ →
           s₁ ≡ s₂ → x₁ ≡ x₂
  helper (x∈p₁ >>= y∈p₂x) (x′∈p₁ >>= y′∈p₂x′) eq =
    u x∈p₁ y∈p₂x eq x′∈p₁ y′∈p₂x′ refl
sound (nonempty u) (nonempty x∈p) (nonempty y∈p) = u x∈p y∈p
sound (cast u)     (cast x∈p)     (cast y∈p)     = sound u x∈p y∈p

complete : ∀ {Tok R xs} (p : Parser Tok R xs) →
           Unambiguous p → Unambiguous′ p
complete (return x)              _ = return
complete fail                    _ = fail
complete token                   _ = token
complete (_∣_ {xs₁ = xs₁} p₁ p₂) u = choice (complete p₁ (λ x₁∈ x₂∈ → u (∣ˡ     x₁∈) (∣ˡ     x₂∈)))
                                            (complete p₂ (λ x₁∈ x₂∈ → u (∣ʳ xs₁ x₁∈) (∣ʳ xs₁ x₂∈)))
                                            (λ x₁∈ x₂∈ → u (∣ˡ x₁∈) (∣ʳ xs₁ x₂∈))
complete (f <$> p)               u = map (λ x₁∈ x₂∈ → u (f <$> x₁∈) (f <$> x₂∈))
complete (_⊛_ {xs = xs} p₁ p₂)   u = app xs (λ f₁∈ x₁∈ eq₁ f₂∈ x₂∈ eq₂ →
                                               u (cast∈ refl refl eq₁ (f₁∈ ⊛ x₁∈))
                                                 (cast∈ refl refl eq₂ (f₂∈ ⊛ x₂∈)))
complete (p₁ >>= p₂)             u = bind (λ x₁∈ y₁∈ eq₁ x₂∈ y₂∈ eq₂ →
                                             u (cast∈ refl refl eq₁ (_>>=_ {p₁ = p₁} x₁∈ y₁∈))
                                               (cast∈ refl refl eq₂ (_>>=_           x₂∈ y₂∈)))
complete (nonempty p)            u = nonempty (λ x₁∈ x₂∈ → u (nonempty x₁∈) (nonempty x₂∈))
complete (cast refl p)           u = cast (complete p (λ x₁∈ x₂∈ → u (cast x₁∈) (cast x₂∈)))
