------------------------------------------------------------------------
-- Some boring lemmas
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Simplified.Lemmas where

open import Algebra
open import Category.Monad
open import Data.Function
open import Data.Product

import Data.List.NonEmpty as List⁺
open List⁺ using (List⁺; _∷_; [_]; _⁺++⁺_; head; tail)
open RawMonad List⁺.monad using () renaming (_>>=_ to _>>=⁺_)
open import Data.List.NonEmpty.Properties

import Data.List as List
open List using (List; _∷_; []; _++_)
private module LM {A} = Monoid (List.monoid A)
open RawMonad List.monad using () renaming (_>>=_ to _>>=′_)
import Data.List.Properties as ListProp

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

>>=-∅ : ∀ {A B} (xs : List A) →
        (xs >>=′ const {List B} []) ≡ []
>>=-∅ []       = refl
>>=-∅ (x ∷ xs) = >>=-∅ xs

tail-++ : ∀ {A} (xs ys : List⁺ A) →
          tail xs ++ List⁺.toList ys ≡ tail (xs ⁺++⁺ ys)
tail-++ [ x ]    ys = refl
tail-++ (x ∷ xs) ys = toList-⁺++⁺ xs ys

head->>= : ∀ {A B} (f : A → List⁺ B) (xs : List⁺ A) →
           head (f (head xs)) ≡ head (xs >>=⁺ f)
head->>= f [ x ]    = refl
head->>= f (x ∷ xs) with f x
head->>= f (x ∷ xs) | [ y ]    = refl
head->>= f (x ∷ xs) | (y ∷ ys) = refl

tail->>= : ∀ {A B} (f : A → List⁺ B) (xs : List⁺ A) →
           tail (f (head xs)) ++ (tail xs >>=′ λ x → head (f x) ∷ tail (f x)) ≡
           tail (xs >>=⁺ f)
tail->>= f [ x ]    = proj₂ LM.identity _
tail->>= f (x ∷ xs) = begin
  tail (f x) ++ (List⁺.toList xs >>=′ λ x → head (f x) ∷ tail (f x)) ≡⟨ cong (λ ys → tail (f x) ++ List.concat ys)
                                                                             (ListProp.map-cong (η ∘ f) (List⁺.toList xs)) ⟩
  tail (f x) ++ (List⁺.toList xs >>=′ List⁺.toList ∘ f)              ≡⟨ cong (_++_ (tail (f x))) (toList->>= f xs) ⟩
  tail (f x) ++ (List⁺.toList (xs >>=⁺ f))                           ≡⟨ tail-++ (f x) (xs >>=⁺ f) ⟩
  tail (f x ⁺++⁺ (xs >>=⁺ f))                                        ≡⟨ refl ⟩
  tail (x ∷ xs >>=⁺ f)                                               ∎
