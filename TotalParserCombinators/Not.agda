------------------------------------------------------------------------
-- Not
------------------------------------------------------------------------

-- TODO: Unify with AsymmetricChoice and And.

module TotalParserCombinators.Not where

open import Coinduction
open import Data.Bool
open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.Product
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
import Function.Equivalence as Eq
open import Function.Inverse as Inv using (_⇿_)
import Function.Inverse.TypeIsomorphisms as Iso
open import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.Sigma.Pointwise as Σ

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)

open import TotalParserCombinators.BreadthFirst hiding (correct)
open import TotalParserCombinators.Congruence as C using (_≈[_]P_; _≅P_)
import TotalParserCombinators.Congruence.Sound as CS
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics using (_∈_·_)

------------------------------------------------------------------------
-- Not

infix 60 ¬_

-- ¬ p returns a result if p doesn't.

-- Note that this definition is closely related to Theorem 4.4 in
-- Brzozowski's paper "Derivatives of Regular Expressions". This paper
-- also contains a complement operator.

¬_ : ∀ {Tok R xs} → Parser Tok R xs → Parser Tok ⊤ _
¬ p = (token >>= λ t → ♯ (¬ D t p))
    ∣ return⋆ (if null (initial-bag p) then [ tt ] else [])

------------------------------------------------------------------------
-- Properties of asymmetric choice

-- D distributes over ¬_.

D-¬ : ∀ {Tok R xs t} (p : Parser Tok R xs) → D t (¬ p) ≅P ¬ D t p
D-¬ {xs = xs} {t} p =
  D t (¬ p)                                         ≅⟨ D t (¬ p) ∎ ⟩

  (return t >>= λ t → ¬ D t p) ∣
    D t (return⋆ (if null xs then [ tt ] else []))  ≅⟨ Monad.left-identity t (λ t → ¬ D t p) ∣
                                                       D.D-return⋆ (if null xs then [ tt ] else []) ⟩
  ¬ D t p ∣ fail                                    ≅⟨ AdditiveMonoid.right-identity (¬ D t p) ⟩

  ¬ D t p                                           ∎
  where open C using (_≅⟨_⟩_; _∎; _∣_)

-- ¬_ preserves equality.

¬-cong_ : ∀ {k Tok R xs xs′}
            {p : Parser Tok R xs} {p′ : Parser Tok R xs′} →
          p ≈[ k ]P p′ → ¬ p ≈[ k ]P ¬ p′
¬-cong_ {k} {R = R} {p = p} {p′} p≈p′ =
  lemma _ _ (I.same-bag/set (CS.sound p≈p′)) ∷ λ t → ♯ (
    D t (¬ p)   ≅⟨ D-¬ p ⟩
    ¬ D t p     ≈⟨ ¬-cong D-congP p≈p′ ⟩
    ¬ D t p′    ≅⟨ sym (D-¬ p′) ⟩
    D t (¬ p′)  ∎)
  where
  open C using (_≅⟨_⟩_; _≈⟨_⟩_; _∎; sym; _∷_)

  lemma : (xs xs′ : List R) → xs List-≈[ k ] xs′ →
          (if null xs  then [ tt ] else []) List-≈[ k ]
          (if null xs′ then [ tt ] else [])
  lemma []      []      eq = Inv.⇿⇒ Inv.id
  lemma (_ ∷ _) (_ ∷ _) eq = Inv.⇿⇒ Inv.id
  lemma []      (_ ∷ _) eq
    with Eq.Equivalent.from (Inv.⇒⇔ eq) ⟨$⟩ here P.refl
  ... | ()
  lemma (_ ∷ _) []      eq
    with Eq.Equivalent.to   (Inv.⇒⇔ eq) ⟨$⟩ here P.refl
  ... | ()

-- ¬_ is correct (assuming that propositional equality is
-- extensional).

correct : P.Extensionality zero       zero →
          P.Extensionality (suc zero) zero →
          ∀ {Tok R xs} s (p : Parser Tok R xs) →
          tt ∈ ¬ p · s ⇿ ∄ λ x → x ∈ p · s
correct ext₀ ext₁ (t ∷ s) p =
  tt ∈ ¬ p · t ∷ s         ⇿⟨ sym D-correct ⟩
  tt ∈ D t (¬ p) · s       ⇿⟨ CS.sound (D-¬ p) ⟩
  tt ∈ ¬ D t p · s         ⇿⟨ correct ext₀ ext₁ s (D t p) ⟩
  (∄ λ x → x ∈ D t p · s)  ⇿⟨ Iso.¬-cong ext₁ ext₁ (Σ.cong (λ {x} → D-correct {x = x})) ⟩
  (∄ λ x → x ∈ p · t ∷ s)  ∎
  where open Inv.EquationalReasoning

correct ext₀ ext₁ {R = R} {[]} [] p =
  tt ∈ ¬ p · []         ⇿⟨ I.correct ⟩
  (tt ∈ [ tt ])         ⇿⟨ lemma ⟩
  (∄ λ x → x ∈ [])      ⇿⟨ sym $ Iso.¬-cong ext₁ ext₀ (Σ.cong (λ {x} → I.correct {x = x})) ⟩
  (∄ λ x → x ∈ p · [])  ∎
  where
  open Inv.EquationalReasoning

  lemma : (tt ∈ [ tt ]) ⇿ (∄ λ (x : R) → x ∈ [])
  lemma = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = to∘from
      }
    }
    where
    to : tt ∈ [ tt ] → ∄ λ x → x ∈ []
    to _ (_ , ())

    from : (∄ λ x → x ∈ []) → tt ∈ [ tt ]
    from _ = here P.refl

    to∘from : (p : ∄ λ x → x ∈ []) → to (from p) ≡ p
    to∘from p = ext₀ helper
      where
      helper : (∈[] : ∃ λ x → x ∈ []) → to (from p) ∈[] ≡ p ∈[]
      helper (_ , ())

    from∘to : (p : tt ∈ [ tt ]) → from (to p) ≡ p
    from∘to (here P.refl) = P.refl
    from∘to (there ())

correct ext₀ ext₁ {R = R} {x ∷ xs} [] p =
  tt ∈ ¬ p · []         ⇿⟨ I.correct ⟩
  (tt ∈ [])             ⇿⟨ lemma ⟩
  (∄ λ y → y ∈ ys)      ⇿⟨ sym $ Iso.¬-cong ext₁ ext₀ (Σ.cong (λ {x} → I.correct {x = x})) ⟩
  (∄ λ y → y ∈ p · [])  ∎
  where
  open Inv.EquationalReasoning

  ys = x ∷ xs

  lemma : (tt ∈ []) ⇿ (∄ λ y → y ∈ ys)
  lemma = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = λ ()
      ; right-inverse-of = to∘from
      }
    }
    where
    to : tt ∈ [] → ∄ λ y → y ∈ ys
    to ()

    from : (∄ λ y → y ∈ ys) → tt ∈ []
    from y∉∷ with y∉∷ (, here P.refl)
    ... | ()

    to∘from : (p : ∄ λ y → y ∈ ys) → to (from p) ≡ p
    to∘from y∉∷ with y∉∷ (, here P.refl)
    ... | ()
