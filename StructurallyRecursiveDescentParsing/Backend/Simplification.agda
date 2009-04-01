------------------------------------------------------------------------
-- Simplification of parsers
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Backend.Simplification where

open import Algebra
open import Data.Bool
import Data.Bool.Properties as Bool
private module BCS = CommutativeSemiring Bool.commutativeSemiring-∨-∧
open import Data.Product
import Data.Product1 as Prod1
open Prod1 using (∃₁₁; Σ₁₁; _,_; proj₁₁₁; proj₁₁₂)
open import Data.List
import Data.List.Properties as List
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (sound; complete)

private

  initial-lemma : ∀ {Tok e′ R} {p₁ p₂ : Parser Tok e′ R} (e : R → Bool) →
                  p₁ ≈ p₂ → any e (initial p₁) ≡ any e (initial p₂)
  initial-lemma {Tok} {e′} {R} e p₁≈p₂ =
    Bool.⇔→≡ (helper (proj₁₁₁ p₁≈p₂) , helper (proj₁₁₂ p₁≈p₂))
    where
    helper : {p₁ p₂ : Parser Tok e′ R} →
             p₁ ⊑ p₂ →
             any e (initial p₁) ≡ true → any e (initial p₂) ≡ true
    helper {p₁ = p₁} {p₂} p₁⊑p₂ eq with List.any-∈ e (initial p₁) eq
    ... | (x , x∈is₁ , ex) = List.∈-any e x∈is₂ ex
      where
      x∈is₂ : x ∈ initial p₂
      x∈is₂ = initial-complete (p₁⊑p₂ (initial-sound p₁ x∈is₁))

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

simplify′ : ∀ {Tok e R} (p : Parser Tok e R) → ∃₁₁ λ p′ → p ≈ p′
simplify′ (return x) = (return x , (λ x∈ → x∈) , λ x∈ → x∈)
simplify′ fail       = (fail     , (λ ())      , λ ())
simplify′ token      = (token    , (λ x∈ → x∈) , λ x∈ → x∈)

simplify′ (p₁ ∣ p₂) with simplify′ p₁ | simplify′ p₂
simplify′ (p₁ ∣ p₂) | (fail , p₁≈∅) | (p₂′ , p₂≈p₂′) =
  (p₂′ , (λ {_} → helper) , λ x∈ → ∣ʳ false (proj₁₁₂ p₂≈p₂′ x∈))
  where
  helper : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ p₂′ · s
  helper (∣ʳ .false x∈p₂) = proj₁₁₁ p₂≈p₂′ x∈p₂
  helper (∣ˡ        x∈p₁) with proj₁₁₁ p₁≈∅ x∈p₁
  ... | ()
simplify′ (p₁ ∣ p₂) | (p₁′ , p₁≈p₁′) | (fail , p₂≈∅) =
  (cast lem p₁′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  lem = sym (proj₂ BCS.+-identity _)

  helper₁ : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ cast lem p₁′ · s
  helper₁ (∣ˡ    x∈p₁) = cast (proj₁₁₁ p₁≈p₁′ x∈p₁)
  helper₁ (∣ʳ ._ x∈p₂) with proj₁₁₁ p₂≈∅ x∈p₂
  ... | ()

  helper₂ : ∀ {x s} → x ∈ cast lem p₁′ · s → x ∈ p₁ ∣ p₂ · s
  helper₂ (cast x∈p₁′) = ∣ˡ (proj₁₁₂ p₁≈p₁′ x∈p₁′)
simplify′ (_∣_ {e₁} p₁ p₂) | (p₁′ , p₁≈p₁′) | (p₂′ , p₂≈p₂′) =
  (p₁′ ∣ p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  helper₁ : ∀ {x s} → x ∈ p₁ ∣ p₂ · s → x ∈ p₁′ ∣ p₂′ · s
  helper₁ (∣ˡ     x∈p₁) = ∣ˡ    (proj₁₁₁ p₁≈p₁′ x∈p₁)
  helper₁ (∣ʳ .e₁ x∈p₂) = ∣ʳ e₁ (proj₁₁₁ p₂≈p₂′ x∈p₂)

  helper₂ : ∀ {x s} → x ∈ p₁′ ∣ p₂′ · s → x ∈ p₁ ∣ p₂ · s
  helper₂ (∣ˡ     x∈p₁′) = ∣ˡ    (proj₁₁₂ p₁≈p₁′ x∈p₁′)
  helper₂ (∣ʳ .e₁ x∈p₂′) = ∣ʳ e₁ (proj₁₁₂ p₂≈p₂′ x∈p₂′)

simplify′ (p₁ >>= p₂) with simplify′ p₁
simplify′ (p₁ >>= p₂) | (fail , p₁≈∅) = (fail , (λ {_} → helper) , λ ())
  where
  helper : ∀ {x s} → x ∈ p₁ >>= p₂ · s → x ∈ fail · s
  helper (x∈p₁ >>= y∈p₂x) with proj₁₁₁ p₁≈∅ x∈p₁
  ... | ()
simplify′ (p₁ >>= p₂) | (return x , p₁≈ε) with simplify′ (p₂ x)
simplify′ (_>>=_ {e₂ = e₂} p₁ p₂) | (return x , p₁≈ε) | (p₂′ , p₂x≈p₂′) =
  (cast lem p₂′ , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  lem = begin
    e₂ x                ≡⟨ sym (proj₂ BCS.+-identity (e₂ x)) ⟩
    e₂ x ∨ false        ≡⟨ sym (initial-lemma e₂ p₁≈ε) ⟩
    any e₂ (initial p₁) ∎

  helper₁ : ∀ {y s} → y ∈ p₁ >>= p₂ · s → y ∈ cast lem p₂′ · s
  helper₁ (_>>=_ {y = y} {s₂ = s₂} x∈p₁ y∈p₂x) =
    cast (helper (proj₁₁₁ p₁≈ε x∈p₁) y∈p₂x)
    where
    helper : ∀ {x′ s₁} → x′ ∈ return x · s₁ → y ∈ p₂ x′ · s₂ →
             y ∈ p₂′ · s₁ ++ s₂
    helper return x∈p₂ = proj₁₁₁ p₂x≈p₂′ x∈p₂

  helper₂ : ∀ {y s} → y ∈ cast lem p₂′ · s → y ∈ p₁ >>= p₂ · s
  helper₂ (cast y∈p₂′) = proj₁₁₂ p₁≈ε return >>= proj₁₁₂ p₂x≈p₂′ y∈p₂′
simplify′ (_>>=_ {e₁} {e₂ = e₂} p₁ p₂) | (p₁′ , p₁≈p₁′) =
  (cast lem (p₁′ >>= p₂) , (λ {_} → helper₁) , λ {_} → helper₂)
  where
  lem = sym (cong (_∧_ e₁) (initial-lemma e₂ p₁≈p₁′))

  helper₁ : ∀ {y s} → y ∈ p₁ >>= p₂ · s → y ∈ cast lem (p₁′ >>= p₂) · s
  helper₁ (x∈p₁ >>= y∈p₂x) = cast (proj₁₁₁ p₁≈p₁′ x∈p₁ >>= y∈p₂x)

  helper₂ : ∀ {y s} → y ∈ cast lem (p₁′ >>= p₂) · s → y ∈ p₁ >>= p₂ · s
  helper₂ (cast (x∈p₁ >>= y∈p₂x)) = proj₁₁₂ p₁≈p₁′ x∈p₁ >>= y∈p₂x

simplify′ (cast refl p) with simplify′ p
simplify′ (cast refl p) | (p′ , p≈p′) =
  (p′ , (λ {_} → helper) , λ x∈ → cast (proj₁₁₂ p≈p′ x∈))
  where
  helper : ∀ {x s} → x ∈ cast refl p · s → x ∈ p′ · s
  helper (cast x∈p) = proj₁₁₁ p≈p′ x∈p

simplify : ∀ {Tok e R} → Parser Tok e R → Parser Tok e R
simplify p = proj₁₁₁ (simplify′ p)

correct : ∀ {Tok e R} {p : Parser Tok e R} → p ≈ simplify p
correct = proj₁₁₂ (simplify′ _)
