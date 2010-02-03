------------------------------------------------------------------------
-- Parser equivalence is a congruence
------------------------------------------------------------------------

module TotalParserCombinators.Congruence.Parser where

open import Algebra
open import Coinduction
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv
  using (_⇿_; module Inverse) renaming (_∘_ to _⟪∘⟫_)
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.BagEquality as BagEq
import Data.List.Any.Membership as ∈
import Data.List.Properties as ListProp
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Prod
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)

private
  module BagMonoid {A : Set} =
    CommutativeMonoid (BagEq.commutativeMonoid A)
  open module BagS {A : Set} =
    Setoid (Any.Membership-≡.Bag-equality {A})
      using () renaming (_≈_ to _Bag-≈_)

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.CoinductiveEquality
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- _≅_ is an equivalence relation

module Equivalence where

  refl : ∀ {Tok R xs} {p : Parser Tok R xs} → p ≅ p
  refl = Inv.id

  sym : ∀ {Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂} →
          p₁ ≅ p₂ → p₂ ≅ p₁
  sym p₁≅p₂ = Inv.sym p₁≅p₂

  trans : ∀ {Tok R xs₁ xs₂ xs₃}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
            {p₃ : Parser Tok R xs₃} →
          p₁ ≅ p₂ → p₂ ≅ p₃ → p₁ ≅ p₃
  trans p₁≅p₂ p₂≅p₃ = Inv._∘_ p₂≅p₃ p₁≅p₂

-- Equational reasoning.

module ≅-Reasoning {Tok R : Set} where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≅⟨_⟩_
  infix  1 begin_

  data _IsRelatedTo_ {xs₁ xs₂}
                     (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) :
                     Set₁ where
    relTo : (p₁≅p₂ : p₁ ≅ p₂) → p₁ IsRelatedTo p₂

  begin_ : ∀ {xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ IsRelatedTo p₂ → p₁ ≅ p₂
  begin relTo p₁≅p₂ = p₁≅p₂

  _≅⟨_⟩_ : ∀ {xs₁ xs₂ xs₃}
             (p₁ : Parser Tok R xs₁) {p₂ : Parser Tok R xs₂}
             {p₃ : Parser Tok R xs₃} →
           p₁ ≅ p₂ → p₂ IsRelatedTo p₃ → p₁ IsRelatedTo p₃
  _ ≅⟨ p₁≅p₂ ⟩ relTo p₂≅p₃ = relTo (Equivalence.trans p₁≅p₂ p₂≅p₃)

  _∎ : ∀ {xs} (p : Parser Tok R xs) → p IsRelatedTo p
  _∎ _ = relTo Equivalence.refl

------------------------------------------------------------------------
-- _≅_ is compatible with all the basic combinators

♭♯-cong : ∀ {Tok R R₁ R₂ xs₁ xs₂} (ys₁ : List R₁) (ys₂ : List R₂)
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≅ p₂ → ♭? (♯? {xs = ys₁} p₁) ≅ ♭? (♯? {xs = ys₂} p₂)
♭♯-cong ys₁ ys₂ {p₁} {p₂} rewrite ♭?♯? ys₁ {p₁} | ♭?♯? ys₂ {p₂} = id

return-cong : ∀ {Tok R} {x₁ x₂ : R} →
              x₁ ≡ x₂ → return {Tok} x₁ ≅ return x₂
return-cong P.refl = Equivalence.refl

fail-cong : ∀ {Tok R} → fail {Tok} {R} ≅ fail {Tok} {R}
fail-cong = Equivalence.refl

token-cong : ∀ {Tok} → token {Tok} ≅ token {Tok}
token-cong = Equivalence.refl

∣-cong : ∀ {Tok R xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂}
           {p₃ : Parser Tok R xs₃}
           {p₄ : Parser Tok R xs₄} →
         p₁ ≅ p₃ → p₂ ≅ p₄ → p₁ ∣ p₂ ≅ p₃ ∣ p₄
∣-cong p₁≅p₃ p₂≅p₄ =
  ParserEquivalence.sound $
    ∣-cong′ (ParserEquivalence.complete p₁≅p₃)
            (ParserEquivalence.complete p₂≅p₄)
  where
  open ∈.Membership-≡

  ∣-cong′ : ∀ {Tok R xs₁ xs₂ xs₃ xs₄}
              {p₁ : Parser Tok R xs₁}
              {p₂ : Parser Tok R xs₂}
              {p₃ : Parser Tok R xs₃}
              {p₄ : Parser Tok R xs₄} →
            p₁ ≅′ p₃ → p₂ ≅′ p₄ → p₁ ∣ p₂ ≅′ p₃ ∣ p₄
  ∣-cong′ (init₁ ∷ rest₁) (init₂ ∷ rest₂) =
    (λ {_} → BagMonoid.∙-cong init₁ init₂) ∷ λ t →
    ♯ ∣-cong′ (♭ (rest₁ t)) (♭ (rest₂ t))

<$>-cong : ∀ {Tok R₁ R₂} {f₁ f₂ : R₁ → R₂} {xs₁ xs₂}
             {p₁ : Parser Tok R₁ xs₁}
             {p₂ : Parser Tok R₁ xs₂} →
           f₁ ≗ f₂ → p₁ ≅ p₂ → f₁ <$> p₁ ≅ f₂ <$> p₂
<$>-cong {Tok} {R₁} {R₂} {f₁} {f₂} f₁≗f₂ =
  ParserEquivalence.sound ∘ <$>-cong′ ∘ ParserEquivalence.complete
  where
  <$>-cong′ : ∀ {xs₁ xs₂}
                {p₁ : Parser Tok R₁ xs₁} {p₂ : Parser Tok R₁ xs₂} →
              p₁ ≅′ p₂ → f₁ <$> p₁ ≅′ f₂ <$> p₂
  <$>-cong′ (init ∷ rest) =
    (λ {_} → BagEq.map-cong f₁≗f₂ init) ∷ λ t → ♯ <$>-cong′ (♭ (rest t))

⊛-cong : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
           {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
           {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
           {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃} →
         ♭? p₁ ≅ ♭? p₃ → ♭? p₂ ≅ ♭? p₄ → p₁ ⊛ p₂ ≅ p₃ ⊛ p₄
⊛-cong p₁≅p₃ p₂≅p₄ = record
  { to         = P.→-to-⟶ $ helper          p₁≅p₃           p₂≅p₄
  ; from       = P.→-to-⟶ $ helper (Inv.sym p₁≅p₃) (Inv.sym p₂≅p₄)
  ; inverse-of = record
    { left-inverse-of  = inv          p₁≅p₃           p₂≅p₄
    ; right-inverse-of = inv (Inv.sym p₁≅p₃) (Inv.sym p₂≅p₄)
    }
  }
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
             {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
             {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
             {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
             {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃} →
           ♭? p₁ ≅ ♭? p₃ → ♭? p₂ ≅ ♭? p₄ → p₁ ⊛ p₂ ⊑ p₃ ⊛ p₄
  helper p₁≅p₃ p₂≅p₄ (∈p₁ ⊛ ∈p₂) =
    (Inverse.to p₁≅p₃ ⟨$⟩ ∈p₁) ⊛ (Inverse.to p₂≅p₄ ⟨$⟩ ∈p₂)

  inv : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
          {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
          {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
          {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
          {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃}
        (p₁≅p₃ : ♭? p₁ ≅ ♭? p₃) (p₂≅p₄ : ♭? p₂ ≅ ♭? p₄)
        {x s} (x∈ : x ∈ p₁ ⊛ p₂ · s) →
        helper (Inv.sym p₁≅p₃) (Inv.sym p₂≅p₄)
          (helper {p₁ = p₁} {p₂} {p₃} {p₄} p₁≅p₃ p₂≅p₄ x∈) ≡ x∈
  inv p₁≅p₃ p₂≅p₄ (∈p₁ ⊛ ∈p₂) =
    P.cong₂ _⊛_ (Inverse.left-inverse-of p₁≅p₃ ∈p₁)
                (Inverse.left-inverse-of p₂≅p₄ ∈p₂)

⊙-cong : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok (R₁ → R₂) xs₁}
           {p₂ : Parser Tok R₁        xs₂}
           {p₃ : Parser Tok (R₁ → R₂) xs₃}
           {p₄ : Parser Tok R₁        xs₄} →
         p₁ ≅ p₃ → p₂ ≅ p₄ → p₁ ⊙ p₂ ≅ p₃ ⊙ p₄
⊙-cong {xs₁ = xs₁} {xs₂} {xs₃} {xs₄} ₁≅₃ ₂≅₄ =
  ⊛-cong (♭♯-cong xs₂ xs₄ ₁≅₃) (♭♯-cong xs₁ xs₃ ₂≅₄)

>>=-cong : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁₁ : Parser Tok R₁ xs₁}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
             {p₂₁ : Parser Tok R₁ xs₂}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂} →
           p₁₁ ≅ p₂₁ → (∀ x → ♭? (p₁₂ x) ≅ ♭? (p₂₂ x)) →
           p₁₁ >>= p₁₂ ≅ p₂₁ >>= p₂₂
>>=-cong p₁₁≅p₂₁ p₁₂≅p₂₂ = record
  { to         = P.→-to-⟶ $ helper p₁₁≅p₂₁ p₁₂≅p₂₂
  ; from       = P.→-to-⟶ $ helper (Inv.sym p₁₁≅p₂₁)
                                   (λ x → Inv.sym (p₁₂≅p₂₂ x))
  ; inverse-of = record
    { left-inverse-of  = inv p₁₁≅p₂₁ p₁₂≅p₂₂
    ; right-inverse-of = inv (Inv.sym p₁₁≅p₂₁)
                             (λ x → Inv.sym (p₁₂≅p₂₂ x))
    }
  }
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁₁ : Parser Tok R₁ xs₁}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
             {p₂₁ : Parser Tok R₁ xs₂}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂} →
           p₁₁ ≅ p₂₁ → (∀ x → ♭? (p₁₂ x) ≅ ♭? (p₂₂ x)) →
           p₁₁ >>= p₁₂ ⊑ p₂₁ >>= p₂₂
  helper p₁₁≅p₂₁ p₁₂≅p₂₂ (∈p₁₁ >>= ∈p₁₂) =
    (Inverse.to  p₁₁≅p₂₁    ⟨$⟩ ∈p₁₁) >>=
    (Inverse.to (p₁₂≅p₂₂ _) ⟨$⟩ ∈p₁₂)

  inv : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
          {p₁₁ : Parser Tok R₁ xs₁}
          {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
          {p₂₁ : Parser Tok R₁ xs₂}
          {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂}
        (p₁₁≅p₂₁ : p₁₁ ≅ p₂₁) (p₁₂≅p₂₂ : ∀ x → ♭? (p₁₂ x) ≅ ♭? (p₂₂ x))
        {x s} (x∈ : x ∈ p₁₁ >>= p₁₂ · s) →
        helper (Inv.sym p₁₁≅p₂₁) (λ x → Inv.sym (p₁₂≅p₂₂ x))
          (helper {p₁₂ = p₁₂} {p₂₂ = p₂₂} p₁₁≅p₂₁ p₁₂≅p₂₂ x∈) ≡ x∈
  inv p₁₁≅p₂₁ p₁₂≅p₂₂ (∈p₁₁ >>= ∈p₁₂) =
    P.cong₂ _>>=_ (Inverse.left-inverse-of  p₁₁≅p₂₁    ∈p₁₁)
                  (Inverse.left-inverse-of (p₁₂≅p₂₂ _) ∈p₁₂)

⟫=-cong : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
            {p₁₁ : Parser Tok R₁ xs₁}
            {p₁₂ : (x : R₁) → Parser Tok R₂ (f₁ x)}
            {p₂₁ : Parser Tok R₁ xs₂}
            {p₂₂ : (x : R₁) → Parser Tok R₂ (f₂ x)} →
          p₁₁ ≅ p₂₁ → (∀ x → p₁₂ x ≅ p₂₂ x) →
          p₁₁ ⟫= p₁₂ ≅ p₂₁ ⟫= p₂₂
⟫=-cong {xs₁ = xs₁} {xs₂} ₁₁≅₂₁ ₁₂≅₂₂ =
  >>=-cong ₁₁≅₂₁ (♭♯-cong xs₁ xs₂ ∘ ₁₂≅₂₂)

>>=!-cong : ∀ {Tok R₁ R₂ xs₁ xs₂}
              {p₁₁ : ∞ (Parser Tok R₁ xs₁)}
              {p₁₂ : R₁ → ∞? (Parser Tok R₂ []) xs₁}
              {p₂₁ : ∞ (Parser Tok R₁ xs₂)}
              {p₂₂ : R₁ → ∞? (Parser Tok R₂ []) xs₂} →
            ♭ p₁₁ ≅ ♭ p₂₁ → (∀ x → ♭? (p₁₂ x) ≅ ♭? (p₂₂ x)) →
            p₁₁ >>=! p₁₂ ≅ p₂₁ >>=! p₂₂
>>=!-cong p₁₁≅p₂₁ p₁₂≅p₂₂ = record
  { to         = P.→-to-⟶ $ helper p₁₁≅p₂₁ p₁₂≅p₂₂
  ; from       = P.→-to-⟶ $ helper (Inv.sym p₁₁≅p₂₁)
                                   (λ x → Inv.sym (p₁₂≅p₂₂ x))
  ; inverse-of = record
    { left-inverse-of  = inv p₁₁≅p₂₁ p₁₂≅p₂₂
    ; right-inverse-of = inv (Inv.sym p₁₁≅p₂₁)
                             (λ x → Inv.sym (p₁₂≅p₂₂ x))
    }
  }
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂}
             {p₁₁ : ∞ (Parser Tok R₁ xs₁)}
             {p₁₂ : R₁ → ∞? (Parser Tok R₂ []) xs₁}
             {p₂₁ : ∞ (Parser Tok R₁ xs₂)}
             {p₂₂ : R₁ → ∞? (Parser Tok R₂ []) xs₂} →
           ♭ p₁₁ ≅ ♭ p₂₁ → (∀ x → ♭? (p₁₂ x) ≅ ♭? (p₂₂ x)) →
           p₁₁ >>=! p₁₂ ⊑ p₂₁ >>=! p₂₂
  helper p₁₁≅p₂₁ p₁₂≅p₂₂ (∈p₁₁ >>=! ∈p₁₂) =
    (Inverse.to  p₁₁≅p₂₁    ⟨$⟩ ∈p₁₁) >>=!
    (Inverse.to (p₁₂≅p₂₂ _) ⟨$⟩ ∈p₁₂)

  inv : ∀ {Tok R₁ R₂ xs₁ xs₂}
          {p₁₁ : ∞ (Parser Tok R₁ xs₁)}
          {p₁₂ : R₁ → ∞? (Parser Tok R₂ []) xs₁}
          {p₂₁ : ∞ (Parser Tok R₁ xs₂)}
          {p₂₂ : R₁ → ∞? (Parser Tok R₂ []) xs₂}
        (p₁₁≅p₂₁ : ♭ p₁₁ ≅ ♭ p₂₁)
        (p₁₂≅p₂₂ : ∀ x → ♭? (p₁₂ x) ≅ ♭? (p₂₂ x))
        {x s} (x∈ : x ∈ p₁₁ >>=! p₁₂ · s) →
        helper (Inv.sym p₁₁≅p₂₁) (λ x → Inv.sym (p₁₂≅p₂₂ x))
          (helper {p₁₁ = p₁₁} {p₁₂} {p₂₁} {p₂₂} p₁₁≅p₂₁ p₁₂≅p₂₂ x∈) ≡ x∈
  inv p₁₁≅p₂₁ p₁₂≅p₂₂ (∈p₁₁ >>=! ∈p₁₂) =
    P.cong₂ _>>=!_ (Inverse.left-inverse-of  p₁₁≅p₂₁    ∈p₁₁)
                   (Inverse.left-inverse-of (p₁₂≅p₂₂ _) ∈p₁₂)

nonempty-cong : ∀ {Tok R xs₁ xs₂}
                  {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
                p₁ ≅ p₂ → nonempty p₁ ≅ nonempty p₂
nonempty-cong =
  ParserEquivalence.sound ∘
  nonempty-cong′ ∘
  ParserEquivalence.complete
  where
  nonempty-cong′ : ∀ {Tok R xs₁ xs₂}
                     {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
                   p₁ ≅′ p₂ → nonempty p₁ ≅′ nonempty p₂
  nonempty-cong′ (_ ∷ rest) = (λ {_} → BagS.refl) ∷ rest

cast-cong : ∀ {Tok R xs₁ xs₂ xs₁′ xs₂′}
              {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
              {eq₁ : xs₁ ≡ xs₁′} {eq₂ : xs₂ ≡ xs₂′} →
            p₁ ≅ p₂ → cast eq₁ p₁ ≅ cast eq₂ p₂
cast-cong {xs₁ = xs₁} {xs₂} {p₁ = p₁} {p₂} {P.refl} {P.refl} =
  ParserEquivalence.sound ∘ cast-cong′ ∘ ParserEquivalence.complete
  where
  cast-cong′ : p₁ ≅′ p₂ → cast P.refl p₁ ≅′ cast P.refl p₂
  cast-cong′ (init ∷ rest) = (λ {_} → init) ∷ rest

⋆-cong : ∀ {Tok R} {p₁ p₂ : Parser Tok R []} →
         p₁ ≅ p₂ → p₁ ⋆ ≅ p₂ ⋆
⋆-cong {Tok} {R} {p₁} {p₂} p₁≅p₂ =
  Inv.sym KleeneStar.correct ⟪∘⟫
  record
    { to         = P.→-to-⟶ $ to          p₁≅p₂
    ; from       = P.→-to-⟶ $ to (Inv.sym p₁≅p₂)
    ; inverse-of = record
      { left-inverse-of  = to∘to          p₁≅p₂
      ; right-inverse-of = to∘to (Inv.sym p₁≅p₂)
      }
    } ⟪∘⟫
  KleeneStar.correct
  where
  to : ∀ {p₁ p₂ : Parser Tok R []} → p₁ ≅ p₂ →
       ∀ {xs s} → xs ∈[ p₁ ]⋆· s → xs ∈[ p₂ ]⋆· s
  to p₁≅p₂ []              = []
  to p₁≅p₂ (x∈p₁ ∷ xs∈p₁⋆) =
    (Inverse.to p₁≅p₂ ⟨$⟩ x∈p₁) ∷ to p₁≅p₂ xs∈p₁⋆

  to∘to : ∀ {p₁ p₂ : Parser Tok R []} (p₁≅p₂ : p₁ ≅ p₂) →
          ∀ {xs s} (xs∈ : xs ∈[ p₁ ]⋆· s) →
          to (Inv.sym p₁≅p₂) (to p₁≅p₂ xs∈) ≡ xs∈
  to∘to p₁≅p₂ []              = P.refl
  to∘to p₁≅p₂ (x∈p₁ ∷ xs∈p₁⋆)
    rewrite Inverse.left-inverse-of p₁≅p₂ x∈p₁
          | to∘to p₁≅p₂ xs∈p₁⋆ =
            P.refl

^-cong : ∀ {Tok R xs₁ xs₂ n}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≅ p₂ → p₁ ^ n ≅ p₂ ^ n
^-cong {n = n} p₁≅p₂ = record
  { to         = P.→-to-⟶ $ helper n p₁≅p₂
  ; from       = P.→-to-⟶ $ helper n (Inv.sym p₁≅p₂)
  ; inverse-of = record
    { left-inverse-of  = inv n p₁≅p₂
    ; right-inverse-of = inv n (Inv.sym p₁≅p₂)
    }
  }
  where
  open ⊙ using (_⊙′_)

  helper : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} n →
           p₁ ≅ p₂ → p₁ ^ n ⊑ p₂ ^ n
  helper             zero    p₁≅p₂ return = return
  helper {xs₁ = xs₁} (suc n) p₁≅p₂ ∈∷⊙ⁱ
    with ⊙.sound (^-initial xs₁ n) ∈∷⊙ⁱ
  ... | <$> ∈p₁ ⊙′ ∈p₁ⁱ =
    ⊙.complete (<$> (Inverse.to p₁≅p₂ ⟨$⟩ ∈p₁)) (helper n p₁≅p₂ ∈p₁ⁱ)

  inv : ∀ {Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} n
        (p₁≅p₂ : p₁ ≅ p₂) {xs s} (xs∈ : xs ∈ p₁ ^ n · s) →
        helper n (Inv.sym p₁≅p₂) (helper n p₁≅p₂ xs∈) ≡ xs∈
  inv             zero    p₁≅p₂ return = P.refl
  inv {xs₁ = xs₁} (suc n) p₁≅p₂ ∈∷⊙ⁱ
    with ⊙.sound (^-initial xs₁ n) ∈∷⊙ⁱ
       | Inverse.right-inverse-of (⊙.correct (^-initial xs₁ n)) ∈∷⊙ⁱ
  inv {xs₂ = xs₂} (suc n) p₁≅p₂ .(⊙.complete (<$> ∈p₁) ∈p₁ⁱ)
    | <$> ∈p₁ ⊙′ ∈p₁ⁱ | P.refl
    rewrite Inverse.left-inverse-of
              (⊙.correct (^-initial xs₂ n))
              (<$>_ {f = (_ → _ → Vec _ _) ∶ _∷_}
                    (Inverse.to p₁≅p₂ ⟨$⟩ ∈p₁) ⊙′ helper n p₁≅p₂ ∈p₁ⁱ)
          | Inverse.left-inverse-of p₁≅p₂ ∈p₁
          | inv n p₁≅p₂ ∈p₁ⁱ =
    P.refl

↑-cong : ∀ {Tok R xs₁ xs₂ n₁ n₂}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≅ p₂ → n₁ ≡ n₂ → p₁ ↑ n₁ ≅ p₂ ↑ n₂
↑-cong p₁≅p₂ P.refl = <$>-cong (λ _ → P.refl) (^-cong p₁≅p₂)
