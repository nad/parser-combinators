------------------------------------------------------------------------
-- Simplification of parsers
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Backend.Simplification where

open import Algebra
open import Data.Product
open import Data.Product1 using (∃₁₁; _,_; proj₁₁₁; proj₁₁₂)
open import Data.List as List
private module LM {Tok} = Monoid (List.monoid Tok)
open import Relation.Binary.PropositionalEquality

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (sound; complete)

-- The functions below simplify parsers. The following simplifications
-- are applied in a bottom-up manner (note that some casts may be
-- introduced in the process):
--
-- fail ∣ p       → p
-- p ∣ fail       → p
-- fail     >>= p → fail
-- return x >>= p → p x
-- cast eq p      → p
--
-- No simplifications are performed under ♯₁_.
--
-- Examples of possible future additions (modulo ∞ and casts):
--
-- token >>= p₁ ∣ token >>= p₂ → token >>= λ t → p₁ t ∣ p₂ t
-- (p₁ >>= p₂) >>= p₃          → p₁ >>= λ x → p₂ >>= p₃

-- Note that the code below contains its own correctness proof. This
-- makes the code somewhat messy, but there are several reasons for
-- not separating out the proof:
-- • Correctness is used to establish that simplification preserves
--   nullability. (An alternative would be to compute the index of
--   simplify p, and establish preservation later.)
-- • It is awkward to prove things about pattern matching when
--   overlapping patterns are used. Unless some workaround (like a
--   view) were employed the three cases in simplify (p₁ ∣ p₂) would
--   have to be expanded to 21 cases in the correctness proof.

simplify′ : ∀ {Tok R xs} (p : Parser Tok R xs) → ∃₁₁ λ p′ → p ≈ p′
simplify′ (return x) = (return x , (λ x∈ → x∈) , λ x∈ → x∈)
simplify′ fail       = (fail     , (λ ())      , λ ())
simplify′ token      = (token    , (λ x∈ → x∈) , λ x∈ → x∈)

simplify′ (p₁ ∣ p₂) with simplify′ p₁ | simplify′ p₂
simplify′ (p₁ ∣ p₂) | (fail , p₁≈∅) | (p₂′ , p₂≈p₂′) =
  (p₂′ , (λ {_} → helper) , λ x∈ → ∣ʳ [] (proj₁₁₂ p₂≈p₂′ x∈))
  where
  helper : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ p₂′ · s
  helper (∣ʳ .[] x∈p₂) = proj₁₁₁ p₂≈p₂′ x∈p₂
  helper (∣ˡ     x∈p₁) with proj₁₁₁ p₁≈∅ x∈p₁
  ... | ()
simplify′ (p₁ ∣ p₂) | (p₁′ , p₁≈p₁′) | (fail , p₂≈∅) =
  (cast lem p₁′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  lem = sym (proj₂ LM.identity _)

  helper₁ : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ cast lem p₁′ · s
  helper₁ (∣ˡ    x∈p₁) = cast (proj₁₁₁ p₁≈p₁′ x∈p₁)
  helper₁ (∣ʳ ._ x∈p₂) with proj₁₁₁ p₂≈∅ x∈p₂
  ... | ()

  helper₂ : ∀ {x s} → x ∈ cast lem p₁′ · s → x ∈ p₁ ∣ p₂ · s
  helper₂ (cast x∈p₁′) = ∣ˡ (proj₁₁₂ p₁≈p₁′ x∈p₁′)
simplify′ (_∣_ {xs₁ = xs₁} p₁ p₂) | (p₁′ , p₁≈p₁′) | (p₂′ , p₂≈p₂′) =
  (p₁′ ∣ p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ p₁′ ∣ p₂′ · s
  helper₁ (∣ˡ      x∈p₁) = ∣ˡ     (proj₁₁₁ p₁≈p₁′ x∈p₁)
  helper₁ (∣ʳ .xs₁ x∈p₂) = ∣ʳ xs₁ (proj₁₁₁ p₂≈p₂′ x∈p₂)

  helper₂ : ∀ {x s} → x ∈ p₁′ ∣ p₂′ · s → x ∈ p₁ ∣ p₂ · s
  helper₂ (∣ˡ      x∈p₁′) = ∣ˡ     (proj₁₁₂ p₁≈p₁′ x∈p₁′)
  helper₂ (∣ʳ .xs₁ x∈p₂′) = ∣ʳ xs₁ (proj₁₁₂ p₂≈p₂′ x∈p₂′)

simplify′ (p₁ >>= p₂) with simplify′ p₁
simplify′ (p₁ >>= p₂) | (fail , p₁≈∅) = (fail , (λ {_} → helper) , λ ())
  where
  helper : ∀ {x s} → x ∈ p₁ >>= p₂ · s → x ∈ fail · s
  helper (x∈p₁ >>= y∈p₂x) with proj₁₁₁ p₁≈∅ x∈p₁
  ... | ()
simplify′ (p₁ >>= p₂) | (return x , p₁≈ε) with simplify′ (p₂ x)
simplify′ (p₁ >>= p₂) | (return x , p₁≈ε) | (p₂′ , p₂x≈p₂′) =
  (cast lem p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  lem = sym (proj₂ LM.identity _)

  helper₁ : ∀ {y s} → y ∈ p₁ >>= p₂ · s → y ∈ cast lem p₂′ · s
  helper₁ (_>>=_ {y = y} {s₂ = s₂} x∈p₁ y∈p₂x) =
    cast (helper (proj₁₁₁ p₁≈ε x∈p₁) y∈p₂x)
    where
    helper : ∀ {x′ s₁} → x′ ∈ return x · s₁ → y ∈ p₂ x′ · s₂ →
             y ∈ p₂′ · s₁ ++ s₂
    helper return x∈p₂ = proj₁₁₁ p₂x≈p₂′ x∈p₂

  helper₂ : ∀ {y s} → y ∈ cast lem p₂′ · s → y ∈ p₁ >>= p₂ · s
  helper₂ (cast y∈p₂′) =
    _>>=_ {x = x} {p₂ = p₂} (proj₁₁₂ p₁≈ε (return {x = x}))
                            (proj₁₁₂ p₂x≈p₂′ y∈p₂′)
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
