------------------------------------------------------------------------
-- A variant of _⊛_ (for lists)
------------------------------------------------------------------------

module TotalParserCombinators.Applicative where

open import Category.Monad
open import Data.Function
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.Properties as AnyProp
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality

open Any.Membership-≡
open AnyProp.Membership-≡
open RawMonad List.monad

-- This function has the property that fs ⊛′ [] evaluates to [].

infixl 50 _⊛′_

_⊛′_ : ∀ {A B} → List (A → B) → List A → List B
fs ⊛′ xs = xs >>= λ x → List.map (λ f → f x) fs

private

  ⊛′-[] : ∀ {A B} {fs : List (A → B)} → fs ⊛′ [] ≡ []
  ⊛′-[] = refl

-- Introduction and elimination rules for _⊛′_.

⊛′-∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x} →
        f ∈ fs → x ∈ xs → f x ∈ fs ⊛′ xs
⊛′-∈⁺ {fs = fs} f∈fs x∈xs =
  >>=-∈⁺ (λ x → List.map (λ f → f x) fs) x∈xs (map-∈⁺ f∈fs)

private

  shuffle : {A B : Set} {P : A → Set} {Q : B → Set} {R : A → B → Set} →
            (∃ λ x → P x × ∃ λ y → Q y × R x y) →
            ∃₂ λ y x → Q y × P x × R x y
  shuffle p₁ = (y , x , q , p , r)
    where
    x  = proj₁ p₁
    p  = proj₁ (proj₂ p₁)
    p₂ = proj₂ (proj₂ p₁)
    y  = proj₁ p₂
    q  = proj₁ (proj₂ p₂)
    r  = proj₂ (proj₂ p₂)

⊛′-∈⁻ : ∀ {A B} (fs : List (A → B)) xs {fx} →
        fx ∈ fs ⊛′ xs → ∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x
⊛′-∈⁻ fs xs fx∈ =
  shuffle $
    Prod.map id (Prod.map id (map-∈⁻ fs)) $
      >>=-∈⁻ (λ x → List.map (λ f → f x) fs) xs fx∈

-- The rules are inverses.

⊛′-∈⁻∘⊛′-∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x}
              (f∈fs : f ∈ fs) (x∈xs : x ∈ xs) →
              ⊛′-∈⁻ fs xs (⊛′-∈⁺ f∈fs x∈xs) ≡ (f , x , f∈fs , x∈xs , refl)
⊛′-∈⁻∘⊛′-∈⁺ {fs = fs} {xs} {f} {x} f∈fs x∈xs = begin
  ⊛′-∈⁻ fs xs (⊛′-∈⁺ f∈fs x∈xs)                 ≡⟨ P.cong (shuffle ∘ Prod.map id (Prod.map id (map-∈⁻ fs)))
                                                          (>>=-∈⁻∘>>=-∈⁺ (λ x → List.map (λ f → f x) fs)
                                                                         x∈xs (map-∈⁺ f∈fs)) ⟩
  shuffle (x , x∈xs , map-∈⁻ fs (map-∈⁺ f∈fs))  ≡⟨ P.cong (λ p → shuffle (x , x∈xs , p))
                                                          (map-∈⁻∘map-∈⁺ (λ f → f x) f∈fs) ⟩
  (f , x , f∈fs , x∈xs , refl)                  ∎
  where open ≡-Reasoning

private

  >>=-∈⁺-cong : ∀ {A B} {f : A → List B} {x y₁ y₂ xs}
                (x∈xs : x ∈ xs)
                {y₁∈fx : y₁ ∈ f x} {y₂∈fx : y₂ ∈ f x} →
                y₁∈fx ≅ y₂∈fx →
                >>=-∈⁺ f x∈xs y₁∈fx ≅ >>=-∈⁺ f x∈xs y₂∈fx
  >>=-∈⁺-cong x∈xs refl = refl

⊛′-∈⁺∘⊛′-∈⁻ : ∀ {A B} (fs : List (A → B)) xs {fx}
              (fx∈ : fx ∈ fs ⊛′ xs) →
              let p = proj₂ (proj₂ (⊛′-∈⁻ fs xs fx∈)) in
              ⊛′-∈⁺ (proj₁ p) (proj₁ (proj₂ p)) ≅ fx∈
⊛′-∈⁺∘⊛′-∈⁻ fs xs fx∈ = begin
  >>=-∈⁺ map-x-fs (proj₁ p)
         (map-∈⁺ $ proj₁ $ proj₂ $ map-∈⁻ fs $ proj₂ p)  ≅⟨ >>=-∈⁺-cong (proj₁ p)
                                                              (map-∈⁺∘map-∈⁻ $ proj₂ p) ⟩
  >>=-∈⁺ map-x-fs (proj₁ p) (proj₂ p)                    ≡⟨ >>=-∈⁺∘>>=-∈⁻ map-x-fs xs fx∈ ⟩
  fx∈                                                    ∎
  where
  open ≅-Reasoning
  map-x-fs = λ x → List.map (λ f → f x) fs
  p        = proj₂ $ >>=-∈⁻ map-x-fs xs fx∈
