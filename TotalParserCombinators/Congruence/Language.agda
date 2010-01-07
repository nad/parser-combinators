------------------------------------------------------------------------
-- Language equivalence is a congruence
------------------------------------------------------------------------

module TotalParserCombinators.Congruence.Language where

open import Coinduction
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (equivalent; module Equivalent)
open import Data.List as List
import Data.List.Any as Any
import Data.List.Any.Properties as AnyProp
open import Data.List.Any.SetEquality
import Data.List.Properties as ListProp
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product as Prod
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)

private
  module SetEq {A : Set} = Setoid (Any.Membership-≡.Set-equality {A})

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.CoinductiveEquality
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- _≈_ is an equivalence relation

module Equivalence where

  refl : ∀ {Tok R xs} {p : Parser Tok R xs} → p ≈ p
  refl = Eq.id

  sym : ∀ {Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂} →
          p₁ ≈ p₂ → p₂ ≈ p₁
  sym p₁≈p₂ = Eq.sym p₁≈p₂

  trans : ∀ {Tok R xs₁ xs₂ xs₃}
            {p₁ : Parser Tok R xs₁}
            {p₂ : Parser Tok R xs₂}
            {p₃ : Parser Tok R xs₃} →
          p₁ ≈ p₂ → p₂ ≈ p₃ → p₁ ≈ p₃
  trans p₁≈p₂ p₂≈p₃ = Eq._∘_ p₂≈p₃ p₁≈p₂

-- Equational reasoning.

module ≈-Reasoning {Tok R : Set} where

  infix  4 _IsRelatedTo_
  infix  2 _∎
  infixr 2 _≈⟨_⟩_ _≅⟨_⟩_
  infix  1 begin_

  data _IsRelatedTo_ {xs₁ xs₂}
                     (p₁ : Parser Tok R xs₁) (p₂ : Parser Tok R xs₂) :
                     Set₁ where
    relTo : (p₁≈p₂ : p₁ ≈ p₂) → p₁ IsRelatedTo p₂

  begin_ : ∀ {xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ IsRelatedTo p₂ → p₁ ≈ p₂
  begin relTo p₁≈p₂ = p₁≈p₂

  _≈⟨_⟩_ : ∀ {xs₁ xs₂ xs₃}
             (p₁ : Parser Tok R xs₁) {p₂ : Parser Tok R xs₂}
             {p₃ : Parser Tok R xs₃} →
           p₁ ≈ p₂ → p₂ IsRelatedTo p₃ → p₁ IsRelatedTo p₃
  _ ≈⟨ p₁≈p₂ ⟩ relTo p₂≈p₃ = relTo (Equivalence.trans p₁≈p₂ p₂≈p₃)

  _≅⟨_⟩_ : ∀ {xs₁ xs₂ xs₃}
             (p₁ : Parser Tok R xs₁) {p₂ : Parser Tok R xs₂}
             {p₃ : Parser Tok R xs₃} →
           p₁ ≅ p₂ → p₂ IsRelatedTo p₃ → p₁ IsRelatedTo p₃
  _ ≅⟨ p₁≅p₂ ⟩ relTo p₂≈p₃ = relTo (Equivalence.trans (≅⇒≈ p₁≅p₂) p₂≈p₃)

  _∎ : ∀ {xs} (p : Parser Tok R xs) → p IsRelatedTo p
  _∎ _ = relTo Equivalence.refl

------------------------------------------------------------------------
-- _≈_ is compatible with all the basic combinators

♭♯-cong : ∀ {Tok R R₁ R₂ xs₁ xs₂} (ys₁ : List R₁) (ys₂ : List R₂)
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
          p₁ ≈ p₂ → ♭? (♯? {xs = ys₁} p₁) ≈ ♭? (♯? {xs = ys₂} p₂)
♭♯-cong ys₁ ys₂ {p₁} {p₂} rewrite ♭?♯? ys₁ {p₁} | ♭?♯? ys₂ {p₂} = id

return-cong : ∀ {Tok R} {x₁ x₂ : R} →
              x₁ ≡ x₂ → return {Tok} x₁ ≈ return x₂
return-cong P.refl = Equivalence.refl

fail-cong : ∀ {Tok R} → fail {Tok} {R} ≈ fail {Tok} {R}
fail-cong = Equivalence.refl

token-cong : ∀ {Tok} → token {Tok} ≈ token {Tok}
token-cong = Equivalence.refl

∣-cong : ∀ {Tok R xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂}
           {p₃ : Parser Tok R xs₃}
           {p₄ : Parser Tok R xs₄} →
         p₁ ≈ p₃ → p₂ ≈ p₄ → p₁ ∣ p₂ ≈ p₃ ∣ p₄
∣-cong p₁≈p₃ p₂≈p₄ =
  LanguageEquivalence.sound $
    ∣-cong′ (LanguageEquivalence.complete p₁≈p₃)
            (LanguageEquivalence.complete p₂≈p₄)
  where
  open AnyProp.Membership-≡

  ∣-cong′ : ∀ {Tok R xs₁ xs₂ xs₃ xs₄}
              {p₁ : Parser Tok R xs₁}
              {p₂ : Parser Tok R xs₂}
              {p₃ : Parser Tok R xs₃}
              {p₄ : Parser Tok R xs₄} →
            p₁ ≈′ p₃ → p₂ ≈′ p₄ → p₁ ∣ p₂ ≈′ p₃ ∣ p₄
  ∣-cong′ (init₁ ∷ rest₁) (init₂ ∷ rest₂) =
    (λ {_} → init₁ ++-cong init₂) ∷ λ t →
    ♯ ∣-cong′ (♭ (rest₁ t)) (♭ (rest₂ t))

<$>-cong : ∀ {Tok R₁ R₂} {f₁ f₂ : R₁ → R₂} {xs₁ xs₂}
             {p₁ : Parser Tok R₁ xs₁}
             {p₂ : Parser Tok R₁ xs₂} →
           f₁ ≗ f₂ → p₁ ≈ p₂ → f₁ <$> p₁ ≈ f₂ <$> p₂
<$>-cong {Tok} {R₁} {R₂} {f₁} {f₂} f₁≗f₂ =
  LanguageEquivalence.sound ∘ <$>-cong′ ∘ LanguageEquivalence.complete
  where
  <$>-cong′ : ∀ {xs₁ xs₂}
                {p₁ : Parser Tok R₁ xs₁} {p₂ : Parser Tok R₁ xs₂} →
              p₁ ≈′ p₂ → f₁ <$> p₁ ≈′ f₂ <$> p₂
  <$>-cong′ (init ∷ rest) =
    (λ {_} → map-cong f₁≗f₂ init) ∷ λ t → ♯ <$>-cong′ (♭ (rest t))

⊛-cong : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
           {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
           {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
           {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃} →
         ♭? p₁ ≈ ♭? p₃ → ♭? p₂ ≈ ♭? p₄ → p₁ ⊛ p₂ ≈ p₃ ⊛ p₄
⊛-cong p₁≈p₃ p₂≈p₄ =
  Equivalent.from ≈⇔≤≥ ⟨$⟩
    Prod.zip helper helper
             (Equivalent.to ≈⇔≤≥ ⟨$⟩ p₁≈p₃)
             (Equivalent.to ≈⇔≤≥ ⟨$⟩ p₂≈p₄)
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
             {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
             {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
             {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
             {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃} →
           ♭? p₁ ⊑ ♭? p₃ → ♭? p₂ ⊑ ♭? p₄ → p₁ ⊛ p₂ ⊑ p₃ ⊛ p₄
  helper ₁⊑₃ ₂⊑₄ (∈p₁ ⊛ ∈p₂) = ₁⊑₃ ∈p₁ ⊛ ₂⊑₄ ∈p₂

⊙-cong : ∀ {Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok (R₁ → R₂) xs₁}
           {p₂ : Parser Tok R₁        xs₂}
           {p₃ : Parser Tok (R₁ → R₂) xs₃}
           {p₄ : Parser Tok R₁        xs₄} →
         p₁ ≈ p₃ → p₂ ≈ p₄ → p₁ ⊙ p₂ ≈ p₃ ⊙ p₄
⊙-cong {xs₁ = xs₁} {xs₂} {xs₃} {xs₄} ₁≈₃ ₂≈₄ =
  ⊛-cong (♭♯-cong xs₂ xs₄ ₁≈₃) (♭♯-cong xs₁ xs₃ ₂≈₄)

>>=-cong : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁₁ : Parser Tok R₁ xs₁}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
             {p₂₁ : Parser Tok R₁ xs₂}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂} →
           p₁₁ ≈ p₂₁ → (∀ x → ♭? (p₁₂ x) ≈ ♭? (p₂₂ x)) →
           p₁₁ >>= p₁₂ ≈ p₂₁ >>= p₂₂
>>=-cong ₁₁≈₂₁ ₁₂≈₂₂ =
  equivalent (helper       (_⟨$⟩_ (Equivalent.to    ₁₁≈₂₁))
                     (λ x → _⟨$⟩_ (Equivalent.to   (₁₂≈₂₂ x))))
             (helper       (_⟨$⟩_ (Equivalent.from  ₁₁≈₂₁))
                     (λ x → _⟨$⟩_ (Equivalent.from (₁₂≈₂₂ x))))
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁₁ : Parser Tok R₁ xs₁}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
             {p₂₁ : Parser Tok R₁ xs₂}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂} →
           p₁₁ ⊑ p₂₁ → (∀ x → ♭? (p₁₂ x) ⊑ ♭? (p₂₂ x)) →
           p₁₁ >>= p₁₂ ⊑ p₂₁ >>= p₂₂
  helper ₁₁⊑₂₁ ₁₂⊑₂₂ (∈p₁₁ >>= ∈p₁₂) = ₁₁⊑₂₁ ∈p₁₁ >>= ₁₂⊑₂₂ _ ∈p₁₂

⟫=-cong : ∀ {Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
            {p₁₁ : Parser Tok R₁ xs₁}
            {p₁₂ : (x : R₁) → Parser Tok R₂ (f₁ x)}
            {p₂₁ : Parser Tok R₁ xs₂}
            {p₂₂ : (x : R₁) → Parser Tok R₂ (f₂ x)} →
          p₁₁ ≈ p₂₁ → (∀ x → p₁₂ x ≈ p₂₂ x) →
          p₁₁ ⟫= p₁₂ ≈ p₂₁ ⟫= p₂₂
⟫=-cong {xs₁ = xs₁} {xs₂} ₁₁≈₂₁ ₁₂≈₂₂ =
  >>=-cong ₁₁≈₂₁ (♭♯-cong xs₁ xs₂ ∘ ₁₂≈₂₂)

>>=!-cong : ∀ {Tok R₁ R₂ xs₁ xs₂}
              {p₁₁ : ∞ (Parser Tok R₁ xs₁)}
              {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₁}
              {p₂₁ : ∞ (Parser Tok R₁ xs₂)}
              {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₂} →
            ♭ p₁₁ ≈ ♭ p₂₁ → (∀ x → ♭? (p₁₂ x) ≈ ♭? (p₂₂ x)) →
            p₁₁ >>=! p₁₂ ≈ p₂₁ >>=! p₂₂
>>=!-cong ₁₁≈₂₁ ₁₂≈₂₂ =
  equivalent (helper       (_⟨$⟩_ (Equivalent.to    ₁₁≈₂₁))
                     (λ x → _⟨$⟩_ (Equivalent.to   (₁₂≈₂₂ x))))
             (helper       (_⟨$⟩_ (Equivalent.from  ₁₁≈₂₁))
                     (λ x → _⟨$⟩_ (Equivalent.from (₁₂≈₂₂ x))))
  where
  helper : ∀ {Tok R₁ R₂ xs₁ xs₂}
             {p₁₁ : ∞ (Parser Tok R₁ xs₁)}
             {p₁₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₁}
             {p₂₁ : ∞ (Parser Tok R₁ xs₂)}
             {p₂₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₂} →
           ♭ p₁₁ ⊑ ♭ p₂₁ → (∀ x → ♭? (p₁₂ x) ⊑ ♭? (p₂₂ x)) →
           p₁₁ >>=! p₁₂ ⊑ p₂₁ >>=! p₂₂
  helper ₁₁⊑₂₁ ₁₂⊑₂₂ (∈p₁₁ >>=! ∈p₁₂) = ₁₁⊑₂₁ ∈p₁₁ >>=! ₁₂⊑₂₂ _ ∈p₁₂

nonempty-cong : ∀ {Tok R xs₁ xs₂}
                  {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
                p₁ ≈ p₂ → nonempty p₁ ≈ nonempty p₂
nonempty-cong =
  LanguageEquivalence.sound ∘
  nonempty-cong′ ∘
  LanguageEquivalence.complete
  where
  nonempty-cong′ : ∀ {Tok R xs₁ xs₂}
                     {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
                   p₁ ≈′ p₂ → nonempty p₁ ≈′ nonempty p₂
  nonempty-cong′ (_ ∷ rest) = (λ {_} → SetEq.refl) ∷ rest

cast-cong : ∀ {Tok R xs₁ xs₂ xs₁′ xs₂′}
              {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
              {eq₁ : xs₁ ≡ xs₁′} {eq₂ : xs₂ ≡ xs₂′} →
            p₁ ≈ p₂ → cast eq₁ p₁ ≈ cast eq₂ p₂
cast-cong {xs₁ = xs₁} {xs₂} {p₁ = p₁} {p₂} {P.refl} {P.refl} =
  LanguageEquivalence.sound ∘ cast-cong′ ∘ LanguageEquivalence.complete
  where
  cast-cong′ : p₁ ≈′ p₂ → cast P.refl p₁ ≈′ cast P.refl p₂
  cast-cong′ (init ∷ rest) = (λ {_} → init) ∷ rest

⋆-cong : ∀ {Tok R} {p₁ p₂ : Parser Tok R []} →
         p₁ ≈ p₂ → p₁ ⋆ ≈ p₂ ⋆
⋆-cong p₁≈p₂ =
  Equivalent.from ≈⇔≤≥ ⟨$⟩
    Prod.map helper helper
             (Equivalent.to ≈⇔≤≥ ⟨$⟩ p₁≈p₂)
  where
  helper : ∀ {Tok R} {p₁ p₂ : Parser Tok R []} →
           p₁ ⊑ p₂ → p₁ ⋆ ⊑ p₂ ⋆
  helper {p₁ = p₁} {p₂} p₁⊑p₂ =
    KleeneStar.complete ∘ helper′ ∘ KleeneStar.sound
    where
    helper′ : ∀ {xs s} → xs ∈[ p₁ ]⋆· s → xs ∈[ p₂ ]⋆· s
    helper′ []           = []
    helper′ (∈p₁ ∷ ∈p₁⋆) = p₁⊑p₂ ∈p₁ ∷ helper′ ∈p₁⋆

^-cong : ∀ {Tok R xs₁ xs₂ n}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈ p₂ → p₁ ^ n ≈ p₂ ^ n
^-cong {n = n} p₁≈p₂ =
  Equivalent.from ≈⇔≤≥ ⟨$⟩
    Prod.map (helper n) (helper n)
             (Equivalent.to ≈⇔≤≥ ⟨$⟩ p₁≈p₂)
  where
  open ⊙ using (_⊙′_)

  helper : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} n →
           p₁ ⊑ p₂ → p₁ ^ n ⊑ p₂ ^ n
  helper             zero    p₁⊑p₂ return = return
  helper {xs₁ = xs₁} (suc n) p₁⊑p₂ ∈∷⊙ⁱ
    with ⊙.sound (^-initial xs₁ n) ∈∷⊙ⁱ
  ... | <$> ∈p₁ ⊙′ ∈p₁ⁱ =
    ⊙.complete (<$> p₁⊑p₂ ∈p₁) (helper n p₁⊑p₂ ∈p₁ⁱ)

↑-cong : ∀ {Tok R xs₁ xs₂ n₁ n₂}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈ p₂ → n₁ ≡ n₂ → p₁ ↑ n₁ ≈ p₂ ↑ n₂
↑-cong p₁≈p₂ P.refl = <$>-cong (λ _ → P.refl) (^-cong p₁≈p₂)
