------------------------------------------------------------------------
-- A variant of _⊛_ (for lists)
------------------------------------------------------------------------

module TotalParserCombinators.Applicative where

open import Algebra
open import Category.Monad
open import Data.Bool
open import Data.List as List
import Data.List.Properties as ListProp
open import Data.List.Any as Any using (Any)
import Data.List.Any.BagAndSetEquality as Eq
open import Data.List.Any.Properties as AnyProp
open import Data.List.Any.Membership
open import Data.Product
open import Function
open import Function.Inverse as Inv using (_⇿_)
import Relation.Binary.EqReasoning as EqR
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _≢_; refl)

open Any.Membership-≡
open RawMonad List.monad
private
  open module BagMonoid {A : Set} =
    CommutativeMonoid (Eq.commutativeMonoid bag A)
      using () renaming (∙-cong to _++-cong_)
  module ListMonoid {A : Set} = Monoid (List.monoid A)

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
-- _⊛′_ satisfies its (implicit) specification

abstract

  ⊛′⇿⊛ : ∀ {A B} {fs : List (A → B)} xs {fx} →
         fx ∈ fs ⊛′ xs ⇿ fx ∈ fs ⊛ xs
  ⊛′⇿⊛ {fs = fs} xs {fx} =
    fx ∈ fs ⊛′ xs                           ⇿⟨ sym >>=⇿ ⟩
    Any (λ x → fx ∈ app fs x) xs            ⇿⟨ Any-cong (λ _ → Inv.sym map⇿) (_ ∎) ⟩
    Any (λ x → Any (λ f → fx ≡ f x) fs) xs  ⇿⟨ AnyProp.swap ⟩
    Any (λ f → Any (λ x → fx ≡ f x) xs) fs  ⇿⟨ ⊛⇿ ⟩
    fx ∈ fs ⊛ xs                            ∎
    where open Inv.EquationalReasoning

  ⇿ : ∀ {A B} {fs : List (A → B)} {xs fx} →
      (∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x) ⇿ fx ∈ fs ⊛′ xs
  ⇿ {fs = fs} {xs} {fx} =
    (∃₂ λ f x → f ∈ fs × x ∈ xs × fx ≡ f x)  ⇿⟨ ⊛-∈⇿ _ ⟩
    fx ∈ fs ⊛  xs                            ⇿⟨ sym $ ⊛′⇿⊛ xs ⟩
    fx ∈ fs ⊛′ xs                            ∎
    where open Inv.EquationalReasoning

------------------------------------------------------------------------
-- Algebraic properties

abstract

  -- A lemma.

  private

    app-++-commute : ∀ {A B} (fs gs : List (A → B)) x →
                     app (fs ++ gs) x ≡ app fs x ++ app gs x
    app-++-commute fs gs x = ListProp.map-++-commute (λ f → f x) fs gs

  -- _⊛′_ preserves bag and set equality.

  cong : ∀ {k A B} {fs₁ fs₂ : List (A → B)} {xs₁ xs₂} →
         fs₁ ≈[ k ] fs₂ → xs₁ ≈[ k ] xs₂ → fs₁ ⊛′ xs₁ ≈[ k ] fs₂ ⊛′ xs₂
  cong fs₁≈fs₂ xs₁≈xs₂ =
    Eq.>>=-cong xs₁≈xs₂ (λ x → Eq.map-cong (λ f → refl) fs₁≈fs₂)

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
    (fs₁ ++ fs₂) ⊛′ xs ≈[ bag ] fs₁ ⊛′ xs ++ fs₂ ⊛′ xs
  right-distributive                   []       = BagMonoid.refl
  right-distributive {fs₁ = fs₁} {fs₂} (x ∷ xs) = begin
    (fs₁ ++ fs₂) ⊛′ (x ∷ xs)                  ≡⟨ refl ⟩
    app (fs₁ ++ fs₂) x ++ (fs₁ ++ fs₂) ⊛′ xs  ≈⟨ BagMonoid.reflexive (app-++-commute fs₁ fs₂ x)
                                                   ++-cong
                                                 right-distributive xs ⟩
    (app fs₁ x ++ app fs₂ x) ++
    (fs₁ ⊛′ xs ++ fs₂ ⊛′ xs)                  ≡⟨ ListMonoid.assoc (app fs₁ x) _ _ ⟩
    app fs₁ x ++ (app fs₂ x ++
    (fs₁ ⊛′ xs ++ fs₂ ⊛′ xs))                 ≈⟨ BagMonoid.refl {x = app fs₁ x} ++-cong (begin
      app fs₂ x ++ (fs₁ ⊛′ xs ++ fs₂ ⊛′ xs)      ≡⟨ P.sym $ ListMonoid.assoc (app fs₂ x) _ _ ⟩
      (app fs₂ x ++ fs₁ ⊛′ xs) ++ fs₂ ⊛′ xs      ≈⟨ BagMonoid.comm (app fs₂ x) (fs₁ ⊛′ xs)
                                                      ++-cong
                                                    BagMonoid.refl ⟩
      (fs₁ ⊛′ xs ++ app fs₂ x) ++ fs₂ ⊛′ xs      ≡⟨ ListMonoid.assoc (fs₁ ⊛′ xs) _ _ ⟩
      fs₁ ⊛′ xs ++ (app fs₂ x ++ fs₂ ⊛′ xs)      ∎) ⟩
    app fs₁ x ++ (fs₁ ⊛′ xs ++
    (app fs₂ x ++ fs₂ ⊛′ xs))                 ≡⟨ P.sym $ ListMonoid.assoc (app fs₁ x) _ _ ⟩
    (app fs₁ x ++ fs₁ ⊛′ xs) ++
    (app fs₂ x ++ fs₂ ⊛′ xs)                  ≡⟨ refl ⟩
    fs₁ ⊛′ (x ∷ xs) ++ fs₂ ⊛′ (x ∷ xs)        ∎
    where open EqR ([ bag ]-Equality _)

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
