------------------------------------------------------------------------
-- A variant of _⊛_ (for lists)
------------------------------------------------------------------------

module TotalParserCombinators.Applicative where

open import Algebra
open import Category.Monad
open import Data.Bool
open import Data.List as List
import Data.List.Properties as ListProp
import Data.List.Any as Any
import Data.List.Any.BagEquality as BagEq
import Data.List.Any.Membership as ∈
open import Data.Product
open import Function
open import Function.Inverse using (_⇿_)
open import Relation.Binary
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl)

open Any.Membership-≡
open ∈.Membership-≡
open RawMonad List.monad
private
  open module BagS {A : Set} =
    Setoid (Any.Membership-≡.Bag-equality {A})
      using (_≈_)
  module ListMonoid {A : Set} = Monoid (List.monoid A)
  open module BagMonoid {A : Set} =
    CommutativeMonoid (BagEq.commutativeMonoid A)
      using () renaming (∙-cong to _++-cong_)

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

  right-zero : ∀ {A B} {fs : List (A → B)} → fs ⊛′ [] ≡ []
  right-zero = refl

------------------------------------------------------------------------
-- Introduction and elimination rules for _⊛′_

∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x} →
     f ∈ fs → x ∈ xs → f x ∈ fs ⊛′ xs
∈⁺ {fs = fs} f∈fs x∈xs = >>=-∈⁺ (app fs) x∈xs (map-∈⁺ f∈fs)

∈⁻ : ∀ {A B} (fs : List (A → B)) xs {fx} →
     fx ∈ fs ⊛′ xs → ∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x
∈⁻ fs xs fx∈ with >>=-∈⁻ (app fs) xs fx∈
... | (x , x∈xs , fx∈′) with map-∈⁻ fs fx∈′
...   | (f , f∈fs , refl) = (f , x , f∈fs , x∈xs , refl)

-- The rules are inverses (more or less).

∈⁻∘∈⁺ : ∀ {A B} {fs : List (A → B)} {xs f x}
        (f∈fs : f ∈ fs) (x∈xs : x ∈ xs) →
        ∈⁻ fs xs (∈⁺ f∈fs x∈xs) ≡ (f , x , f∈fs , x∈xs , refl)
∈⁻∘∈⁺ {fs = fs} {x = x} f∈fs x∈xs
  rewrite >>=-∈⁻∘>>=-∈⁺ (app fs) x∈xs (map-∈⁺ f∈fs)
        | map-∈⁻∘map-∈⁺ (λ f → f x) f∈fs = refl

∈⁺∘∈⁻ : ∀ {A B} (fs : List (A → B)) xs {fx}
        (fx∈ : fx ∈ fs ⊛′ xs) →
        let p = proj₂ (proj₂ (∈⁻ fs xs fx∈)) in
        ∈⁺ (proj₁ p) (proj₁ (proj₂ p)) ≅ fx∈
∈⁺∘∈⁻ fs xs fx∈ with >>=-∈⁻ (app fs) xs fx∈ | >>=-∈⁺∘>>=-∈⁻ (app fs) xs fx∈
∈⁺∘∈⁻ fs xs .(>>=-∈⁺ (app fs) x∈xs fx∈′)          | (x , x∈xs , fx∈′          ) | refl with map-∈⁻ fs fx∈′ | map-∈⁺∘map-∈⁻ fx∈′
∈⁺∘∈⁻ fs xs .(>>=-∈⁺ (app fs) x∈xs (map-∈⁺ f∈fs)) | (x , x∈xs , .(map-∈⁺ f∈fs)) | refl | (f , f∈fs , refl) | refl = refl

∈⇿ : ∀ {A B} {fs : List (A → B)} {xs fx} →
     (∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x) ⇿ fx ∈ fs ⊛′ xs
∈⇿ {fs = fs} {xs} {fx} = record
  { to         = P.→-to-⟶ ∈⁺′
  ; from       = P.→-to-⟶ $ ∈⁻ fs xs
  ; inverse-of = record
    { left-inverse-of  = ∈⁻∘∈⁺′
    ; right-inverse-of = ∈⁺′∘∈⁻
    }
  }
  where
  ∈⁺′ : ∀ {fx} → (∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x) → fx ∈ fs ⊛′ xs
  ∈⁺′ (f , x , f∈fs , x∈xs , refl) = ∈⁺ f∈fs x∈xs

  ∈⁻∘∈⁺′ : ∀ {fx} (p : ∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x) →
           ∈⁻ fs xs (∈⁺′ p) ≡ p
  ∈⁻∘∈⁺′ (f , x , f∈fs , x∈xs , refl) = ∈⁻∘∈⁺ f∈fs x∈xs

  ∈⁺′∘∈⁻ : ∀ {fx} (p : fx ∈ fs ⊛′ xs) → ∈⁺′ (∈⁻ fs xs p) ≡ p
  ∈⁺′∘∈⁻ p               with ∈⁻ fs xs p | ∈⁺∘∈⁻ fs xs p
  ∈⁺′∘∈⁻ .(∈⁺ f∈fs x∈xs) | (f , x , f∈fs , x∈xs , refl) | refl = refl

------------------------------------------------------------------------
-- Algebraic properties

-- A lemma.

private

  app-++-commute : ∀ {A B} (fs gs : List (A → B)) x →
                   app (fs ++ gs) x ≡ app fs x ++ app gs x
  app-++-commute fs gs x = ListProp.map-++-commute (λ f → f x) fs gs

-- _⊛′_ preserves bag equality.

cong : ∀ {A B} {fs₁ fs₂ : List (A → B)} {xs₁ xs₂} →
       fs₁ ≈ fs₂ → xs₁ ≈ xs₂ → fs₁ ⊛′ xs₁ ≈ fs₂ ⊛′ xs₂
cong fs₁≈fs₂ xs₁≈xs₂ =
  BagEq.>>=-cong xs₁≈xs₂ (λ x → BagEq.map-cong (λ f → refl) fs₁≈fs₂)

-- [] is a left zero for _⊛′_.

left-zero : ∀ {A B} xs → (List (A → B) ∶ []) ⊛′ xs ≡ []
left-zero []       = refl
left-zero (x ∷ xs) = left-zero xs

-- _⊛′_ distributes over _++_ from the left.

left-distributive :
  ∀ {A B} {fs : List (A → B)} xs₁ {xs₂} →
  fs ⊛′ (xs₁ ++ xs₂) ≡ fs ⊛′ xs₁ ++ fs ⊛′ xs₂
left-distributive           []              = refl
left-distributive {fs = fs} (x ∷ xs₁) {xs₂} = begin
  fs ⊛′ (x ∷ xs₁ ++ xs₂)                ≡⟨ refl ⟩
  app fs x ++ fs ⊛′ (xs₁ ++ xs₂)        ≡⟨ P.cong (_++_ (app fs x)) (left-distributive xs₁) ⟩
  app fs x ++ (fs ⊛′ xs₁ ++ fs ⊛′ xs₂)  ≡⟨ P.sym $ ListMonoid.assoc (app fs x) _ _ ⟩
  (app fs x ++ fs ⊛′ xs₁) ++ fs ⊛′ xs₂  ≡⟨ refl ⟩
  fs ⊛′ (x ∷ xs₁) ++ fs ⊛′ xs₂          ∎
  where open P.≡-Reasoning

-- _⊛′_ does not distribute over _++_ from the right, if list equality
-- is used.

private

  not-right-distributive :
    let xs = true ∷ true ∷ []; fs₁ = id ∷ []; fs₂ = id ∷ not ∷ [] in
    (fs₁ ++ fs₂) ⊛′ xs ≢ fs₁ ⊛′ xs ++ fs₂ ⊛′ xs
  not-right-distributive ()

-- However, if bag equality is used, then a right distributivity law
-- can be proved. The proof makes use of the commutativity of _++_.

right-distributive :
  ∀ {A B} {fs₁ fs₂ : List (A → B)} xs →
  (fs₁ ++ fs₂) ⊛′ xs ≈ fs₁ ⊛′ xs ++ fs₂ ⊛′ xs
right-distributive                   []       = BagS.refl
right-distributive {fs₁ = fs₁} {fs₂} (x ∷ xs) = begin
  (fs₁ ++ fs₂) ⊛′ (x ∷ xs)                  ≡⟨ refl ⟩
  app (fs₁ ++ fs₂) x ++ (fs₁ ++ fs₂) ⊛′ xs  ≈⟨ BagS.reflexive (app-++-commute fs₁ fs₂ x)
                                                 ++-cong
                                               right-distributive xs ⟩
  (app fs₁ x ++ app fs₂ x) ++
  (fs₁ ⊛′ xs ++ fs₂ ⊛′ xs)                  ≡⟨ ListMonoid.assoc (app fs₁ x) _ _ ⟩
  app fs₁ x ++ (app fs₂ x ++
  (fs₁ ⊛′ xs ++ fs₂ ⊛′ xs))                 ≈⟨ BagS.refl {x = app fs₁ x} ++-cong (begin
    app fs₂ x ++ (fs₁ ⊛′ xs ++ fs₂ ⊛′ xs)      ≡⟨ P.sym $ ListMonoid.assoc (app fs₂ x) _ _ ⟩
    (app fs₂ x ++ fs₁ ⊛′ xs) ++ fs₂ ⊛′ xs      ≈⟨ BagMonoid.comm (app fs₂ x) (fs₁ ⊛′ xs)
                                                    ++-cong
                                                  BagS.refl ⟩
    (fs₁ ⊛′ xs ++ app fs₂ x) ++ fs₂ ⊛′ xs      ≡⟨ ListMonoid.assoc (fs₁ ⊛′ xs) _ _ ⟩
    fs₁ ⊛′ xs ++ (app fs₂ x ++ fs₂ ⊛′ xs)      ∎) ⟩
  app fs₁ x ++ (fs₁ ⊛′ xs ++
  (app fs₂ x ++ fs₂ ⊛′ xs))                 ≡⟨ P.sym $ ListMonoid.assoc (app fs₁ x) _ _ ⟩
  (app fs₁ x ++ fs₁ ⊛′ xs) ++
  (app fs₂ x ++ fs₂ ⊛′ xs)                  ≡⟨ refl ⟩
  fs₁ ⊛′ (x ∷ xs) ++ fs₂ ⊛′ (x ∷ xs)        ∎
  where open EqR Any.Membership-≡.Bag-equality

-- Applicative functor laws.

identity : ∀ {A} (xs : List A) → return id ⊛′ xs ≡ xs
identity []       = refl
identity (x ∷ xs) = P.cong (_∷_ x) $ identity xs

composition :
  ∀ {A B C} (fs : List (B → C)) (gs : List (A → B)) xs →
  return _∘′_ ⊛′ fs ⊛′ gs ⊛′ xs ≡ fs ⊛′ (gs ⊛′ xs)
composition fs gs []       = refl
composition fs gs (x ∷ xs) = begin
  return _∘′_ ⊛′ fs ⊛′ gs ⊛′ (x ∷ xs)  ≡⟨ refl ⟩
  app (return _∘′_ ⊛′ fs ⊛′ gs) x ++
  (return _∘′_ ⊛′ fs ⊛′ gs ⊛′ xs)      ≡⟨ P.cong₂ _++_ (lemma₁ gs)
                                                       (composition fs gs xs) ⟩
  fs ⊛′ app gs x ++ fs ⊛′ (gs ⊛′ xs)   ≡⟨ P.sym $ left-distributive (app gs x) ⟩
  fs ⊛′ (app gs x ++ (gs ⊛′ xs))       ≡⟨ refl ⟩
  fs ⊛′ (gs ⊛′ (x ∷ xs))               ∎
  where
  open P.≡-Reasoning

  lemma₁ : ∀ gs → app (return _∘′_ ⊛′ fs ⊛′ gs) x ≡ fs ⊛′ app gs x
  lemma₁ []       = refl
  lemma₁ (g ∷ gs) = begin
    app (return _∘′_ ⊛′ fs ⊛′ (g ∷ gs)) x  ≡⟨ refl ⟩
    app (app (return _∘′_ ⊛′ fs) g ++
         (return _∘′_ ⊛′ fs) ⊛′ gs) x      ≡⟨ app-++-commute (app (return _∘′_ ⊛′ fs) g)
                                                             ((return _∘′_ ⊛′ fs) ⊛′ gs) x ⟩
    app (app (return _∘′_ ⊛′ fs) g) x ++
    app (return _∘′_ ⊛′ fs ⊛′ gs) x        ≡⟨ P.cong₂ _++_ (lemma₂ fs) (lemma₁ gs) ⟩
    app fs (g x) ++ fs ⊛′ app gs x         ≡⟨ refl ⟩
    fs ⊛′ app (g ∷ gs) x                   ∎
    where
    lemma₂ : (fs : List _) →
             app (app (return _∘′_ ⊛′ fs) g) x ≡ app fs (g x)
    lemma₂ []       = refl
    lemma₂ (f ∷ fs) = P.cong (_∷_ (f (g x))) $ lemma₂ fs

homomorphism : ∀ {A B : Set} (f : A → B) x →
               return f ⊛′ return x ≡ return (f x)
homomorphism f x = refl

interchange : ∀ {A B} (fs : List (A → B)) {x} →
              fs ⊛′ return x ≡ return (λ f → f x) ⊛′ fs
interchange []           = refl
interchange (f ∷ fs) {x} = begin
  (f ∷ fs) ⊛′ return x                 ≡⟨ refl ⟩
  [ f x ] ++ fs ⊛′ return x            ≡⟨ P.cong (_++_ [ f x ]) $ interchange fs ⟩
  [ f x ] ++ return (λ f → f x) ⊛′ fs  ≡⟨ refl ⟩
  return (λ f → f x) ⊛′ (f ∷ fs)       ∎
  where open P.≡-Reasoning
