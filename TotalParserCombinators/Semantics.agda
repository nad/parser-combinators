------------------------------------------------------------------------
-- Semantics of the parsers
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module TotalParserCombinators.Semantics where

open import Coinduction
open import Data.List hiding (drop)
open import Data.Product
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
open import Function.Inverse as Inv using (_⇿_; module Inverse)
open import Data.Unit
import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser

------------------------------------------------------------------------
-- Semantics

-- The semantics of the parsers. x ∈ p · s means that x can be the
-- result of applying the parser p to the string s. Note that the
-- semantics is defined inductively.

infix  60 <$>_
infixl 50 _⊛_
infixl 10 _>>=_ _>>=!_
infix   4 _∈_·_

data _∈_·_ {Tok} :
       ∀ {R xs} → R → Parser Tok R xs → List Tok → Set₁ where
  return   : ∀ {R} {x : R} → x ∈ return x · []
  token    : ∀ {x} → x ∈ token · [ x ]
  ∣ˡ       : ∀ {R x xs₁ xs₂ s}
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₁ : x ∈ p₁ · s) → x ∈ p₁ ∣ p₂ · s
  ∣ʳ       : ∀ {R x xs₂ s} xs₁
               {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
             (x∈p₂ : x ∈ p₂ · s) → x ∈ p₁ ∣ p₂ · s
  <$>_     : ∀ {R₁ R₂ x s xs} {p : Parser Tok R₁ xs} {f : R₁ → R₂}
             (x∈p : x ∈ p · s) → f x ∈ f <$> p · s
  _⊛_      : ∀ {R₁ R₂ f x s₁ s₂ fs xs}
               {p₁ : ∞? (Parser Tok (R₁ → R₂) fs) xs}
               {p₂ : ∞? (Parser Tok  R₁       xs) fs} →
             (f∈p₁ : f ∈ ♭? p₁ · s₁)
             (x∈p₂ : x ∈ ♭? p₂ · s₂) →
             f x ∈ p₁ ⊛ p₂ · s₁ ++ s₂
  _>>=_    : ∀ {R₁ R₂ x y s₁ s₂ xs} {f : R₁ → List R₂}
               {p₁ : Parser Tok R₁ xs}
               {p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f x)) xs}
             (x∈p₁ : x ∈ p₁ · s₁)
             (y∈p₂x : y ∈ ♭? (p₂ x) · s₂) →
             y ∈ p₁ >>= p₂ · s₁ ++ s₂
  _>>=!_   : ∀ {R₁ R₂ x y s₁ s₂ xs}
               {p₁ : ∞ (Parser Tok R₁ xs)}
               {p₂ : R₁ → ∞? (Parser Tok R₂ []) xs}
             (x∈p₁ : x ∈ ♭ p₁ · s₁)
             (y∈p₂x : y ∈ ♭? (p₂ x) · s₂) →
             y ∈ p₁ >>=! p₂ · s₁ ++ s₂
  nonempty : ∀ {R xs x y s} {p : Parser Tok R xs}
             (x∈p : y ∈ p · x ∷ s) → y ∈ nonempty p · x ∷ s
  cast     : ∀ {R xs₁ xs₂ x s} {eq : xs₁ ≡ xs₂} {p : Parser Tok R xs₁}
             (x∈p : x ∈ p · s) → x ∈ cast eq p · s

------------------------------------------------------------------------
-- Parser and language equivalence

infix 4 _⊑_ _≈_ _≅_

-- p₁ ⊑ p₂ means that the language defined by p₂ contains all the
-- string/result pairs contained in the language defined by p₁.

_⊑_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ⊑ p₂ = ∀ {x s} → x ∈ p₁ · s → x ∈ p₂ · s

-- Language equivalence.

_≈_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≈ p₂ = ∀ {x s} → x ∈ p₁ · s ⇔ x ∈ p₂ · s

-- Parser equivalence.

_≅_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≅ p₂ = ∀ {x s} → x ∈ p₁ · s ⇿ x ∈ p₂ · s

-- p₁ ≈ p₂ iff both p₁ ⊑ p₂ and p₂ ⊑ p₁.

≈⇔≤≥ : ∀ {Tok R xs₁ xs₂}
         {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
       p₁ ≈ p₂ ⇔ (p₁ ⊑ p₂ × p₂ ⊑ p₁)
≈⇔≤≥ = equivalent
         (λ p₁≈p₂  → ((λ {_} → _⟨$⟩_ (Equivalent.to   p₁≈p₂))
                     , λ {_} → _⟨$⟩_ (Equivalent.from p₁≈p₂)))
         (λ p₁≤≥p₂ {s} → equivalent (proj₁ p₁≤≥p₂ {s})
                                    (proj₂ p₁≤≥p₂ {s}))

-- Parser equivalence implies language equivalence.

≅⇒≈ : ∀ {Tok R xs₁ xs₂}
        {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
      p₁ ≅ p₂ → p₁ ≈ p₂
≅⇒≈ p₁≅p₂ = Inverse.equivalence p₁≅p₂

-- Language equivalence does not (in general) imply parser
-- equivalence.

¬≈⇒≅ : ¬ (∀ {Tok R xs₁ xs₂}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈ p₂ → p₁ ≅ p₂)
¬≈⇒≅ hyp with Inverse.injective p₁≅p₂
                {∣ˡ return} {∣ʳ [ tt ] return} (lemma _ _)
  where
  p₁ : Parser ⊤ ⊤ _
  p₁ = return tt ∣ return tt

  p₂ : Parser ⊤ ⊤ _
  p₂ = return tt

  p₁⊑p₂ : p₁ ⊑ p₂
  p₁⊑p₂ (∣ˡ    return) = return
  p₁⊑p₂ (∣ʳ ._ return) = return

  p₁≅p₂ : p₁ ≅ p₂
  p₁≅p₂ = hyp $ equivalent p₁⊑p₂ ∣ˡ

  lemma : ∀ {x s} (x∈₁ x∈₂ : x ∈ p₂ · s) → x∈₁ ≡ x∈₂
  lemma return return = refl

... | ()

------------------------------------------------------------------------
-- A simple cast lemma

cast∈ : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′} →
        x ≡ x′ → p ≡ p′ → s ≡ s′ → x ∈ p · s → x′ ∈ p′ · s′
cast∈ refl refl refl x∈ = x∈

module Cast∈ where

  drop : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′}
         (x≡x′ : x ≡ x′) (p≡p′ : p ≡ p′) (s≡s′ : s ≡ s′)
         (x∈p : x ∈ p · s) →
         H._≅_ (cast∈ x≡x′ p≡p′ s≡s′ x∈p) x∈p
  drop refl refl refl _ = H.refl

  sym∘ : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′}
         (x≡x′ : x ≡ x′) (p≡p′ : p ≡ p′) (s≡s′ : s ≡ s′)
         (x∈p : x ∈ p · s) →
         cast∈ (P.sym x≡x′) (P.sym p≡p′) (P.sym s≡s′)
               (cast∈ x≡x′ p≡p′ s≡s′ x∈p) ≡ x∈p
  sym∘ refl refl refl _ = refl

  ∘sym : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′}
         (x≡x′ : x ≡ x′) (p≡p′ : p ≡ p′) (s≡s′ : s ≡ s′)
         (x∈p : x′ ∈ p′ · s′) →
         cast∈ x≡x′ p≡p′ s≡s′
               (cast∈ (P.sym x≡x′) (P.sym p≡p′) (P.sym s≡s′) x∈p) ≡ x∈p
  ∘sym refl refl refl _ = refl

  correct : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′}
            (x≡x′ : x ≡ x′) (p≡p′ : p ≡ p′) (s≡s′ : s ≡ s′) →
            x ∈ p · s ⇿ x′ ∈ p′ · s′
  correct x≡x′ p≡p′ s≡s′ = record
    { to         = P.→-to-⟶ $ cast∈ x≡x′ p≡p′ s≡s′
    ; from       = P.→-to-⟶ $
                     cast∈ (P.sym x≡x′) (P.sym p≡p′) (P.sym s≡s′)
    ; inverse-of = record
      { left-inverse-of  = sym∘ x≡x′ p≡p′ s≡s′
      ; right-inverse-of = ∘sym x≡x′ p≡p′ s≡s′
      }
    }

------------------------------------------------------------------------
-- Lemmas about conditional coinduction

module ♭♯ where

  drop : ∀ {Tok R R′ xs′} {p : Parser Tok R′ xs′} (xs : List R) →
         ♭? (♯? {xs = xs} p) ⊑ p
  drop xs = cast∈ refl (♭?♯? xs) refl

  add : ∀ {Tok R R′ xs′} {p : Parser Tok R′ xs′} (xs : List R) →
        p ⊑ ♭? (♯? {xs = xs} p)
  add xs = cast∈ refl (P.sym $ ♭?♯? xs) refl

  correct : ∀ {Tok R R′ xs′} (xs : List R) {p : Parser Tok R′ xs′} →
            ♭? (♯? {xs = xs} p) ≅ p
  correct xs = Cast∈.correct refl (♭?♯? xs) refl
