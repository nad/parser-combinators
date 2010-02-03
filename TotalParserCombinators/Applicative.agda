------------------------------------------------------------------------
-- A variant of _⊛_ (for lists)
------------------------------------------------------------------------

module TotalParserCombinators.Applicative where

open import Category.Monad
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.Membership as ∈
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality

open Any.Membership-≡
open ∈.Membership-≡
open RawMonad List.monad

-- A helper function.

private

  app : ∀ {A B} → List (A → B) → A → List B
  app fs x = List.map (λ f → f x) fs

-- A variant of _⊛_. This function has the property that fs ⊛′ []
-- evaluates to [].

infixl 50 _⊛′_

_⊛′_ : ∀ {A B} → List (A → B) → List A → List B
fs ⊛′ xs = xs >>= app fs

private

  ⊛′-[] : ∀ {A B} {fs : List (A → B)} → fs ⊛′ [] ≡ []
  ⊛′-[] = refl

-- Introduction and elimination rules for _⊛′_.

⊛′-∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x} →
        f ∈ fs → x ∈ xs → f x ∈ fs ⊛′ xs
⊛′-∈⁺ {fs = fs} f∈fs x∈xs = >>=-∈⁺ (app fs) x∈xs (map-∈⁺ f∈fs)

⊛′-∈⁻ : ∀ {A B} (fs : List (A → B)) xs {fx} →
        fx ∈ fs ⊛′ xs → ∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x
⊛′-∈⁻ fs xs fx∈ with >>=-∈⁻ (app fs) xs fx∈
... | (x , x∈xs , fx∈′) with map-∈⁻ fs fx∈′
...   | (f , f∈fs , refl) = (f , x , f∈fs , x∈xs , refl)

-- The rules are inverses.

⊛′-∈⁻∘⊛′-∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x}
              (f∈fs : f ∈ fs) (x∈xs : x ∈ xs) →
              ⊛′-∈⁻ fs xs (⊛′-∈⁺ f∈fs x∈xs) ≡ (f , x , f∈fs , x∈xs , refl)
⊛′-∈⁻∘⊛′-∈⁺ {fs = fs} {x = x} f∈fs x∈xs
  rewrite >>=-∈⁻∘>>=-∈⁺ (app fs) x∈xs (map-∈⁺ f∈fs)
        | map-∈⁻∘map-∈⁺ (λ f → f x) f∈fs = refl

⊛′-∈⁺∘⊛′-∈⁻ : ∀ {A B} (fs : List (A → B)) xs {fx}
              (fx∈ : fx ∈ fs ⊛′ xs) →
              let p = proj₂ (proj₂ (⊛′-∈⁻ fs xs fx∈)) in
              ⊛′-∈⁺ (proj₁ p) (proj₁ (proj₂ p)) ≅ fx∈
⊛′-∈⁺∘⊛′-∈⁻ fs xs fx∈ with >>=-∈⁻ (app fs) xs fx∈ | >>=-∈⁺∘>>=-∈⁻ (app fs) xs fx∈
⊛′-∈⁺∘⊛′-∈⁻ fs xs .(>>=-∈⁺ (app fs) x∈xs fx∈′)          | (x , x∈xs , fx∈′          ) | refl with map-∈⁻ fs fx∈′ | map-∈⁺∘map-∈⁻ fx∈′
⊛′-∈⁺∘⊛′-∈⁻ fs xs .(>>=-∈⁺ (app fs) x∈xs (map-∈⁺ f∈fs)) | (x , x∈xs , .(map-∈⁺ f∈fs)) | refl | (f , f∈fs , refl) | refl = refl
