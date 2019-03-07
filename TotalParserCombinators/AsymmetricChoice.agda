------------------------------------------------------------------------
-- Asymmetric choice
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module TotalParserCombinators.AsymmetricChoice where

open import Data.Bool
open import Data.Empty
open import Data.List
open import Data.List.Any using (here)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties
open import Data.List.Relation.BagAndSetEquality
  using () renaming (_∼[_]_ to _List-∼[_]_)
open import Data.Product
import Data.Product.Function.Dependent.Propositional as Σ
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence using (module Equivalence; _⇔_)
open import Function.Inverse as Inv using (_↔_)
open import Function.Related as Related
open import Function.Related.TypeIsomorphisms
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≢_)
open import Relation.Nullary

open import TotalParserCombinators.Congruence using (_∼[_]P_; _≅P_)
open import TotalParserCombinators.Derivative using (D)
open import TotalParserCombinators.Parser
import TotalParserCombinators.Pointwise as Pointwise
open import TotalParserCombinators.Semantics using (_∈_·_)
open import TotalParserCombinators.Semantics.Continuation as S
  using (_⊕_∈_·_)

------------------------------------------------------------------------
-- An initial bag operator

-- first-nonempty returns the left-most non-empty initial bag, if any.

first-nonempty : {R : Set} → List R → List R → List R
first-nonempty [] ys = ys
first-nonempty xs ys = xs

-- first-nonempty preserves equality.

first-nonempty-cong :
  ∀ {k R} {xs₁ xs₁′ xs₂ xs₂′ : List R} →
  xs₁ List-∼[ ⌊ k ⌋⇔ ] xs₁′ → xs₂ List-∼[ ⌊ k ⌋⇔ ] xs₂′ →
  first-nonempty xs₁ xs₂ List-∼[ ⌊ k ⌋⇔ ] first-nonempty xs₁′ xs₂′
first-nonempty-cong {xs₁ = []}    {[]}    eq₁ eq₂ = eq₂
first-nonempty-cong {xs₁ = _ ∷ _} {_ ∷ _} eq₁ eq₂ = eq₁
first-nonempty-cong {xs₁ = []} {_ ∷ _} eq₁ eq₂
  with Equivalence.from (⇒⇔ eq₁) ⟨$⟩ here P.refl
... | ()
first-nonempty-cong {xs₁ = _ ∷ _} {[]} eq₁ eq₂
  with Equivalence.to (⇒⇔ eq₁) ⟨$⟩ here P.refl
... | ()

-- first-nonempty is correct.

first-nonempty-left :
  ∀ {k R} {xs₁ xs₂ : List R} →
  (∃ λ y → y ∈ xs₁) → first-nonempty xs₁ xs₂ List-∼[ k ] xs₁
first-nonempty-left {xs₁ = []}    (_ , ())
first-nonempty-left {xs₁ = _ ∷ _} _        = _ ∎
  where open Related.EquationalReasoning

first-nonempty-right :
  ∀ {k R} {xs₁ xs₂ : List R} →
  (∄ λ y → y ∈ xs₁) → first-nonempty xs₁ xs₂ List-∼[ k ] xs₂
first-nonempty-right {xs₁ = x ∷ _} ∉x∷ = ⊥-elim $ ∉x∷ (x , here P.refl)
first-nonempty-right {xs₁ = []}    _   = _ ∎
  where open Related.EquationalReasoning

------------------------------------------------------------------------
-- Asymmetric choice

-- _◃_ is defined as a pointwise lifting of first-nonempty. Note that
-- _◃_ preserves parser and language equality, but not the
-- sub-/superparser and sub-/superlanguage relations.

private
  module AC {R} = Pointwise R R ⌊_⌋⇔ first-nonempty first-nonempty-cong

-- p₁ ◃ p₂ returns a result if either p₁ or p₂ does. For a given
-- string results are returned either from p₁ or from p₂, not both.

infixl 5 _◃_ _◃-cong_

_◃_ : ∀ {Tok R xs₁ xs₂} →
      Parser Tok R xs₁ → Parser Tok R xs₂ →
      Parser Tok R (first-nonempty xs₁ xs₂)
_◃_ = AC.lift

-- D distributes over _◃_.

D-◃ : ∀ {Tok R xs₁ xs₂ t}
      (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
      D t (p₁ ◃ p₂) ≅P D t p₁ ◃ D t p₂
D-◃ = AC.D-lift

-- _◃_ preserves equality.

_◃-cong_ : ∀ {k Tok R xs₁ xs₁′ xs₂ xs₂′}
             {p₁  : Parser Tok R xs₁} {p₁′ : Parser Tok R xs₁′}
             {p₂  : Parser Tok R xs₂} {p₂′ : Parser Tok R xs₂′} →
           p₁ ∼[ ⌊ k ⌋⇔ ]P p₁′ → p₂ ∼[ ⌊ k ⌋⇔ ]P p₂′ →
           p₁ ◃ p₂ ∼[ ⌊ k ⌋⇔ ]P p₁′ ◃ p₂′
_◃-cong_ = AC.lift-cong

-- If p₁ accepts s, then p₁ ◃ p₂ behaves as p₁ when applied to s.

left : ∀ {Tok R xs₁ xs₂ x s}
       (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
       (∃ λ y → y ∈ p₁ · s) → x ∈ p₁ ◃ p₂ · s ↔ x ∈ p₁ · s
left {x = x} =
  AC.lift-property
    (λ F _ H → ∃ F → H x ↔ F x)
    (λ F↔F′ _ H↔H′ →
       Σ.cong Inv.id (λ {x} → ↔⇒ (F↔F′ x))
         →-cong-⇔
       Related-cong (H↔H′ x) (F↔F′ x))
    (λ ∈xs₁ → first-nonempty-left ∈xs₁)

-- If p₁ does not accept s, then p₁ ◃ p₂ behaves as p₂ when applied to
-- s.

right : ∀ {Tok R xs₁ xs₂ x s}
        (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) →
        (∄ λ y → y ∈ p₁ · s) → x ∈ p₁ ◃ p₂ · s ↔ x ∈ p₂ · s
right {x = x} =
  AC.lift-property
    (λ F G H → ∄ F → H x ↔ G x)
    (λ F↔F′ G↔G′ H↔H′ →
       ¬-cong-⇔ (Σ.cong Inv.id λ {x} → ↔⇒ (F↔F′ x))
         →-cong-⇔
       Related-cong (H↔H′ x) (G↔G′ x))
    (λ ∉xs₁ → first-nonempty-right ∉xs₁)

-- In "Parsing with First-Class Derivatives" Brachthäuser, Rendel and
-- Ostermann state that "[...] and biased alternative cannot be
-- expressed as user defined combinators". Here I give a formal proof
-- of a variant of this statement (in the present setting): it is not
-- possible to construct an asymmetric choice operator that, in a
-- certain sense, is more like the prioritised choice of parsing
-- expression grammars (see Ford's "Parsing Expression Grammars: A
-- Recognition-Based Syntactic Foundation") without changing the
-- interface of the parser combinator library.

not-PEG-choice :
  ¬ ∃₂ λ (_◅-bag_ : {R : Set} → List R → List R → List R)
         (_◅_ : ∀ {Tok R xs₁ xs₂} →
               Parser Tok R xs₁ → Parser Tok R xs₂ →
               Parser Tok R (xs₁ ◅-bag xs₂)) →
      ∀ {Tok R xs₁ xs₂ s₁}
      (p₁ : Parser Tok R xs₁)
      (p₂ : Parser Tok R xs₂) →
      ((∃₂ λ y s₂ → y ⊕ s₂ ∈ p₁ · s₁) →
       ∀ {x s₂} → x ⊕ s₂ ∈ p₁ ◅ p₂ · s₁ ⇔ x ⊕ s₂ ∈ p₁ · s₁)
        ×
      (¬ (∃₂ λ y s₂ → y ⊕ s₂ ∈ p₁ · s₁) →
       ∀ {x s₂} → x ⊕ s₂ ∈ p₁ ◅ p₂ · s₁ ⇔ x ⊕ s₂ ∈ p₂ · s₁)
not-PEG-choice (_ , _◅_ , correct) = false∉p₁⊛·[-] false∈p₁⊛·[-]
  where
  p₁ p₂ : Parser ⊤ Bool _
  p₁ = const true <$> token
  p₂ = return false

  false∈p₂·[] : false ⊕ [] ∈ p₂ · []
  false∈p₂·[] = S.return

  ∄∈p₁·[] : ¬ ∃₂ (λ b s → b ⊕ s ∈ p₁ · [])
  ∄∈p₁·[] (_ , _ , S.<$> ())

  false∈p₁◅p₂·[] : false ⊕ [] ∈ p₁ ◅ p₂ · []
  false∈p₁◅p₂·[] =
    Equivalence.from (proj₂ (correct _ _) ∄∈p₁·[]) ⟨$⟩ false∈p₂·[]

  false∈p₁◅p₂·[-] : false ⊕ [ _ ] ∈ p₁ ◅ p₂ · [ _ ]
  false∈p₁◅p₂·[-] = S.extend false∈p₁◅p₂·[]

  true∈p₁·[-] : true ⊕ [] ∈ p₁ · [ _ ]
  true∈p₁·[-] = S.<$> S.token

  false∈p₁·[-] : false ⊕ [ _ ] ∈ p₁ · [ _ ]
  false∈p₁·[-] =
    Equivalence.to (proj₁ (correct _ _) (-, -, true∈p₁·[-])) ⟨$⟩
      false∈p₁◅p₂·[-]

  false∈p₁⊛·[-] :
    false ⊕ [] ∈ const <$> p₁ ⊛ (return _ ∣ token) · [ _ ]
  false∈p₁⊛·[-] = S.[ _ - _ ] S.<$> false∈p₁·[-] ⊛ S.∣-right _ S.token

  false∉p₁⊛·[-] :
    ¬ false ⊕ [] ∈ const <$> p₁ ⊛ (return _ ∣ token) · [ _ ]
  false∉p₁⊛·[-] = flip lemma P.refl
    where
    lemma :
      ∀ {b} →
      b ⊕ [] ∈ const <$> p₁ ⊛ (return _ ∣ token) · [ _ ] → b ≢ false
    lemma (S.[ _ - _ ] S.<$> (S.<$> S.token) ⊛ _) ()
