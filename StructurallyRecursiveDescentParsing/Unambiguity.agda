------------------------------------------------------------------------
-- Unambiguity
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Unambiguity where

open import Data.Bool
open import Data.List
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
  return : ∀ {R} {x : R} → Unambiguous′ (return x)
  fail   : ∀ {R} → Unambiguous′ (fail {R = R})
  token  : Unambiguous′ token
  choice : ∀ {R xs₁ xs₂} {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
           (u₁ : Unambiguous′ p₁) (u₂ : Unambiguous′ p₂) →
           (u : ∀ {x₁ x₂ s} → x₁ ∈ p₁ · s → x₂ ∈ p₂ · s → x₁ ≡ x₂) →
           Unambiguous′ (p₁ ∣ p₂)
  bind   : ∀ {R₁ R₂ xs} {f : R₁ → List R₂}
             {p₁ : Parser Tok R₁ xs}
             {p₂ : (x : R₁) → ∞? (null xs) (Parser Tok R₂ (f x))}
           (u : ∀ {x₁ x₂ y₁ y₂ s s₁ s₂ s₃ s₄} →
              x₁ ∈ p₁ · s₁ → y₁ ∈ ♭? (null xs) (p₂ x₁) · s₂ → s₁ ++ s₂ ≡ s →
              x₂ ∈ p₁ · s₃ → y₂ ∈ ♭? (null xs) (p₂ x₂) · s₄ → s₃ ++ s₄ ≡ s →
              y₁ ≡ y₂) →
           Unambiguous′ (p₁ >>= p₂)
  cast   : ∀ {R xs₁ xs₂} {eq : xs₁ ≡ xs₂} {p : Parser Tok R xs₁}
           (u : Unambiguous′ p) → Unambiguous′ (cast eq p)

-- The two definitions are equivalent.

sound : ∀ {Tok R xs} {p : Parser Tok R xs} →
        Unambiguous′ p → Unambiguous p
sound return           return        return         = refl
sound fail             ()            ()
sound token            token         token          = refl
sound (choice u₁ u₂ u) (∣ˡ   x∈p₁·s) (∣ˡ    y∈p₁·s) =      sound u₁ x∈p₁·s y∈p₁·s
sound (choice u₁ u₂ u) (∣ˡ   x∈p₁·s) (∣ʳ _  y∈p₂·s) =      u        x∈p₁·s y∈p₂·s
sound (choice u₁ u₂ u) (∣ʳ _ x∈p₂·s) (∣ˡ    y∈p₁·s) = sym (u        y∈p₁·s x∈p₂·s)
sound (choice u₁ u₂ u) (∣ʳ _ x∈p₂·s) (∣ʳ ._ y∈p₂·s) =      sound u₂ x∈p₂·s y∈p₂·s
sound (bind {p₁ = p₁} {p₂} u) x∈p·s y∈p·s           = helper x∈p·s y∈p·s refl
  where
  helper : ∀ {x₁ x₂ s₁ s₂} →
           x₁ ∈ p₁ >>= p₂ · s₁ → x₂ ∈ p₁ >>= p₂ · s₂ →
           s₁ ≡ s₂ → x₁ ≡ x₂
  helper (x∈p₁·s₁₁ >>= y∈p₂x·s₁₂) (x∈p₁·s₂₁ >>= y∈p₂x·s₂₂) eq =
    u x∈p₁·s₁₁ y∈p₂x·s₁₂ eq x∈p₁·s₂₁ y∈p₂x·s₂₂ refl
sound (cast u) (cast x∈p) (cast y∈p) = sound u x∈p y∈p

complete : ∀ {Tok R xs} (p : Parser Tok R xs) →
           Unambiguous p → Unambiguous′ p
complete (return x)              _ = return
complete fail                    _ = fail
complete token                   _ = token
complete (_∣_ {xs₁ = xs₁} p₁ p₂) u = choice (complete p₁ (λ x₁∈ x₂∈ → u (∣ˡ     x₁∈) (∣ˡ     x₂∈)))
                                            (complete p₂ (λ x₁∈ x₂∈ → u (∣ʳ xs₁ x₁∈) (∣ʳ xs₁ x₂∈)))
                                            (λ x₁∈ x₂∈ → u (∣ˡ x₁∈) (∣ʳ xs₁ x₂∈))
complete (p₁ >>= p₂)             u = bind (λ x₁∈ y₁∈ eq₁ x₂∈ y₂∈ eq₂ →
                                             u (cast∈ refl refl eq₁ (_>>=_ {p₁ = p₁} x₁∈ y₁∈))
                                               (cast∈ refl refl eq₂ (_>>=_           x₂∈ y₂∈)))
complete (cast refl p)           u = cast (complete p (λ x₁∈ x₂∈ → u (cast x₁∈) (cast x₂∈)))
