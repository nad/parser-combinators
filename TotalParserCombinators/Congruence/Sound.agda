------------------------------------------------------------------------
-- The parser equivalence proof language is sound
------------------------------------------------------------------------

module TotalParserCombinators.Congruence.Sound where

open import Algebra
open import Coinduction
open import Data.List
import Data.List.Any as Any
import Data.List.Any.BagAndSetEquality as BSEq
open import Function
import Function.Inverse as Inv
open import Relation.Binary.PropositionalEquality as P using (_≡_; _≗_)

open Any.Membership-≡ using (_∈_; bag) renaming (_≈[_]_ to _List-≈[_]_)
open Inv.EquationalReasoning
  renaming (_≈⟨_⟩_ to _≈⟨_⟩′_; _∎ to _∎′; sym to sym′)
private
  module BSMonoid {k} {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid k A)

import TotalParserCombinators.Applicative as ⊛
open import TotalParserCombinators.BreadthFirst hiding (sound)
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.CoinductiveEquality as CE
  using (_≈[_]′_; _∷_)
open import TotalParserCombinators.Congruence as Eq
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

open ∂

private

  -- WHNFs of equality proof programs.

  infix 4 _≈[_]W_

  record _≈[_]W_ {Tok R xs₁ xs₂}
                 (p₁ : Parser Tok R xs₁) (k : Kind)
                 (p₂ : Parser Tok R xs₂) : Set₁ where
    constructor _∷_
    field
      head : xs₁ List-≈[ k ] xs₂
      tail : ∀ t → ∂ p₁ t ≈[ k ]P ∂ p₂ t

  open _≈[_]W_

  forget : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ]W p₂ → p₁ ≈[ k ]P p₂
  forget (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) = xs₁≈xs₂ ∷ λ t → ♯ ∂p₁≈∂p₂ t

  reflW : ∀ {k Tok R xs} (p : Parser Tok R xs) → p ≈[ k ]W p
  reflW p = (_ ∎′) ∷ λ t → ∂ p t ∎

  transW : ∀ {k Tok R xs₁ xs₂ xs₃}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂}
             {p₃ : Parser Tok R xs₃} →
           p₁ ≈[ k ]W p₂ → p₂ ≈[ k ]W p₃ → p₁ ≈[ k ]W p₃
  transW (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) (xs₂≈xs₃ ∷ ∂p₂≈∂p₃) =
    (_ ≈⟨ xs₁≈xs₂ ⟩′ xs₂≈xs₃) ∷ λ t → _ ≈⟨ ∂p₁≈∂p₂ t ⟩ ∂p₂≈∂p₃ t

  transW≅ : ∀ {k Tok R xs₁ xs₂ xs₃}
              {p₁ : Parser Tok R xs₁}
              {p₂ : Parser Tok R xs₂}
              {p₃ : Parser Tok R xs₃} →
            p₁ ≈[ parser ]W p₂ → p₂ ≈[ k ]W p₃ → p₁ ≈[ k ]W p₃
  transW≅ (xs₁≅xs₂ ∷ ∂p₁≅∂p₂) (xs₂≈xs₃ ∷ ∂p₂≈∂p₃) =
    (_ ⇿⟨ xs₁≅xs₂ ⟩ xs₂≈xs₃) ∷ λ t → _ ≅⟨ ∂p₁≅∂p₂ t ⟩ ∂p₂≈∂p₃ t

  symW : ∀ {k Tok R xs₁ xs₂}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂} →
         p₁ ≈[ k ]W p₂ → p₂ ≈[ k ]W p₁
  symW (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) = sym′ xs₁≈xs₂ ∷ λ t → sym (∂p₁≈∂p₂ t)

  ♭♯W : ∀ {k Tok R R₁ R₂ xs₁ xs₂} (ys₁ : List R₁) (ys₂ : List R₂)
          {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
       p₁ ≈[ k ]W p₂ → ♭? (♯? {xs = ys₁} p₁) ≈[ k ]W ♭? (♯? {xs = ys₂} p₂)
  ♭♯W ys₁ ys₂ {p₁} {p₂} (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) = xs₁≈xs₂ ∷ λ t →
     ∂ (♭? {xs = ys₁} (♯? p₁)) t  ≅⟨ Eq.complete (∂-cong (♭♯.correct ys₁)) ⟩
     ∂ p₁ t                       ≈⟨ ∂p₁≈∂p₂ t ⟩
     ∂ p₂ t                       ≅⟨ sym $ Eq.complete (∂-cong (♭♯.correct ys₂)) ⟩
     ∂ (♭? {xs = ys₂} (♯? p₂)) t  ∎

  _∣W_ : ∀ {k Tok R xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂}
           {p₃ : Parser Tok R xs₃}
           {p₄ : Parser Tok R xs₄} →
         p₁ ≈[ k ]W p₃ → p₂ ≈[ k ]W p₄ → p₁ ∣ p₂ ≈[ k ]W p₃ ∣ p₄
  (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) ∣W (xs₃≈xs₄ ∷ ∂p₃≈∂p₄) =
    BSMonoid.∙-cong xs₁≈xs₂ xs₃≈xs₄ ∷ λ t → ∂p₁≈∂p₂ t ∣ ∂p₃≈∂p₄ t

  _<$>W_ : ∀ {k Tok R₁ R₂} {f₁ f₂ : R₁ → R₂} {xs₁ xs₂}
             {p₁ : Parser Tok R₁ xs₁}
             {p₂ : Parser Tok R₁ xs₂} →
          f₁ ≗ f₂ → p₁ ≈[ k ]W p₂ → f₁ <$> p₁ ≈[ k ]W f₂ <$> p₂
  f₁≗f₂ <$>W (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) =
    BSEq.map-cong f₁≗f₂ xs₁≈xs₂ ∷ λ t → f₁≗f₂ <$> ∂p₁≈∂p₂ t

  _⊛W_ : ∀ {k Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : ∞? (Parser Tok (R₁ → R₂) xs₁) xs₂}
           {p₂ : ∞? (Parser Tok R₁        xs₂) xs₁}
           {p₃ : ∞? (Parser Tok (R₁ → R₂) xs₃) xs₄}
           {p₄ : ∞? (Parser Tok R₁        xs₄) xs₃} →
        ♭? p₁ ≈[ k ]W ♭? p₃ → ♭? p₂ ≈[ k ]W ♭? p₄ → p₁ ⊛ p₂ ≈[ k ]W p₃ ⊛ p₄
  _⊛W_ {xs₁ = fs₁} {xs₃ = fs₃} {p₁ = p₁} {p₂} {p₃} {p₄}
       (fs₁≈fs₃ ∷ ∂p₁≈∂p₃) (xs₂≈xs₄ ∷ ∂p₂≈∂p₄) =
    ⊛.cong fs₁≈fs₃ xs₂≈xs₄ ∷ λ t →
      ∂ (p₁ ⊛ p₂) t                                    ≅⟨ ∂-⊛ p₁ p₂ ⟩
      ∂ (♭? p₁) t ⊙ ♭? p₂ ∣ return⋆ fs₁ ⊙ ∂ (♭? p₂) t  ≈⟨ ∂p₁≈∂p₃ t ⊙′ (xs₂≈xs₄ ∷ λ t → ♯ ∂p₂≈∂p₄ t) ∣
                                                          Return⋆.cong fs₁≈fs₃ ⊙′ ∂p₂≈∂p₄ t ⟩
      ∂ (♭? p₃) t ⊙ ♭? p₄ ∣ return⋆ fs₃ ⊙ ∂ (♭? p₄) t  ≅⟨ sym $ ∂-⊛ p₃ p₄ ⟩
      ∂ (p₃ ⊛ p₄) t                                    ∎

  _⊙W_ : ∀ {k Tok R₁ R₂ xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok (R₁ → R₂) xs₁}
           {p₂ : Parser Tok R₁        xs₂}
           {p₃ : Parser Tok (R₁ → R₂) xs₃}
           {p₄ : Parser Tok R₁        xs₄} →
         p₁ ≈[ k ]W p₃ → p₂ ≈[ k ]W p₄ → p₁ ⊙ p₂ ≈[ k ]W p₃ ⊙ p₄
  _⊙W_ {xs₁ = fs₁} {xs₃ = fs₃} {p₁ = p₁} {p₂} {p₃} {p₄}
       (fs₁≈fs₃ ∷ ∂p₁≈∂p₃) (xs₂≈xs₄ ∷ ∂p₂≈∂p₄) =
    ⊛.cong fs₁≈fs₃ xs₂≈xs₄ ∷ λ t →
      ∂ (p₁ ⊙ p₂) t                       ≅⟨ ∂-⊙ p₁ p₂ ⟩
      ∂ p₁ t ⊙ p₂ ∣ return⋆ fs₁ ⊙ ∂ p₂ t  ≈⟨ ∂p₁≈∂p₃ t ⊙′ (xs₂≈xs₄ ∷ λ t → ♯ ∂p₂≈∂p₄ t) ∣
                                             Return⋆.cong fs₁≈fs₃ ⊙′ ∂p₂≈∂p₄ t ⟩
      ∂ p₃ t ⊙ p₄ ∣ return⋆ fs₃ ⊙ ∂ p₄ t  ≅⟨ sym $ ∂-⊙ p₃ p₄ ⟩
      ∂ (p₃ ⊙ p₄) t                       ∎

  _>>=W_ : ∀ {k Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁ : Parser Tok R₁ xs₁}
             {p₂ : (x : R₁) → ∞? (Parser Tok R₂ (f₁ x)) xs₁}
             {p₃ : Parser Tok R₁ xs₂}
             {p₄ : (x : R₁) → ∞? (Parser Tok R₂ (f₂ x)) xs₂} →
           p₁ ≈[ k ]W p₃ → (∀ x → ♭? (p₂ x) ≈[ k ]W ♭? (p₄ x)) →
           p₁ >>= p₂ ≈[ k ]W p₃ >>= p₄
  _>>=W_ {xs₁ = xs₁} {xs₂} {p₁ = p₁} {p₂} {p₃} {p₄}
         (xs₁≈xs₂ ∷ ∂p₁≈∂p₃) p₂≈p₄ = BSEq.>>=-cong xs₁≈xs₂ (head ∘ p₂≈p₄) ∷ λ t →
    ∂ (p₁ >>= p₂) t                                               ≅⟨ ∂->>= p₁ p₂ ⟩
    ∂ p₁ t ≫= (♭? ∘ p₂) ∣ return⋆ xs₁ ≫= (λ x → ∂ (♭? (p₂ x)) t)  ≈⟨ ∂p₁≈∂p₃ t ≫=′ (forget ∘ p₂≈p₄) ∣
                                                                     Return⋆.cong xs₁≈xs₂ ≫=′ (λ x → tail (p₂≈p₄ x) t) ⟩
    ∂ p₃ t ≫= (♭? ∘ p₄) ∣ return⋆ xs₂ ≫= (λ x → ∂ (♭? (p₄ x)) t)  ≅⟨ sym $ ∂->>= p₃ p₄ ⟩
    ∂ (p₃ >>= p₄) t                                               ∎

  _∞>>=W_ : ∀ {k Tok R₁ R₂ xs₁ xs₂}
              {p₁ : ∞ (Parser Tok R₁ xs₁)}
              {p₂ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₁}
              {p₃ : ∞ (Parser Tok R₁ xs₂)}
              {p₄ : (x : R₁) → ∞? (Parser Tok R₂ []) xs₂} →
            ♭ p₁ ≈[ k ]W ♭ p₃ → (∀ x → ♭? (p₂ x) ≈[ k ]W ♭? (p₄ x)) →
            p₁ ∞>>= p₂ ≈[ k ]W p₃ ∞>>= p₄
  _∞>>=W_ {xs₁ = xs₁} {xs₂} {p₁} {p₂} {p₃} {p₄}
          (xs₁≈xs₂ ∷ ∂p₁≈∂p₃) p₂≈p₄ = (_ ∎′) ∷ λ t →
    ∂ (p₁ ∞>>= p₂) t                                                  ≅⟨ ∂-∞>>= p₁ p₂ ⟩
    ∂ (♭ p₁) t ≫= (♭? ∘ p₂) ∣ return⋆ xs₁ ≫= (λ x → ∂ (♭? (p₂ x)) t)  ≈⟨ ∂p₁≈∂p₃ t ≫=′ (forget ∘ p₂≈p₄) ∣
                                                                         Return⋆.cong xs₁≈xs₂ ≫=′ (λ x → tail (p₂≈p₄ x) t) ⟩
    ∂ (♭ p₃) t ≫= (♭? ∘ p₄) ∣ return⋆ xs₂ ≫= (λ x → ∂ (♭? (p₄ x)) t)  ≅⟨ sym $ ∂-∞>>= p₃ p₄ ⟩
    ∂ (p₃ ∞>>= p₄) t                                                  ∎

  _≫=W_ : ∀ {k Tok R₁ R₂ xs₁ xs₂} {f₁ f₂ : R₁ → List R₂}
             {p₁ : Parser Tok R₁ xs₁}
             {p₂ : (x : R₁) → Parser Tok R₂ (f₁ x)}
             {p₃ : Parser Tok R₁ xs₂}
             {p₄ : (x : R₁) → Parser Tok R₂ (f₂ x)} →
           p₁ ≈[ k ]W p₃ → (∀ x → p₂ x ≈[ k ]W p₄ x) → p₁ ≫= p₂ ≈[ k ]W p₃ ≫= p₄
  _≫=W_ {xs₁ = xs₁} {xs₂} {p₁ = p₁} {p₂} {p₃} {p₄}
        (xs₁≈xs₂ ∷ ∂p₁≈∂p₃) p₂≈p₄ =
    BSEq.>>=-cong xs₁≈xs₂ (head ∘ p₂≈p₄) ∷ λ t →
      ∂ (p₁ ≫= p₂) t                                    ≅⟨ ∂-≫= p₁ p₂ ⟩
      ∂ p₁ t ≫= p₂ ∣ return⋆ xs₁ ≫= (λ x → ∂ (p₂ x) t)  ≈⟨ ∂p₁≈∂p₃ t ≫=′ (forget ∘ p₂≈p₄) ∣
                                                           Return⋆.cong xs₁≈xs₂ ≫=′ (λ x → tail (p₂≈p₄ x) t) ⟩
      ∂ p₃ t ≫= p₄ ∣ return⋆ xs₂ ≫= (λ x → ∂ (p₄ x) t)  ≅⟨ sym $ ∂-≫= p₃ p₄ ⟩
      ∂ (p₃ ≫= p₄) t                                    ∎

  nonemptyW : ∀ {k Tok R xs₁ xs₂}
                {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
             p₁ ≈[ k ]W p₂ → nonempty p₁ ≈[ k ]W nonempty p₂
  nonemptyW (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) = (_ ∎′) ∷ ∂p₁≈∂p₂

  castW : ∀ {k Tok R xs₁ xs₂ xs₁′ xs₂′}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
            {xs₁≈xs₁′ : xs₁ List-≈[ bag ] xs₁′}
            {xs₂≈xs₂′ : xs₂ List-≈[ bag ] xs₂′} →
         p₁ ≈[ k ]W p₂ → cast xs₁≈xs₁′ p₁ ≈[ k ]W cast xs₂≈xs₂′ p₂
  castW {xs₁ = xs₁} {xs₂} {xs₁′} {xs₂′}
        {xs₁≈xs₁′ = xs₁≈xs₁′} {xs₂≈xs₂′} (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) =
    (λ {x} →
      x ∈ xs₁′  ⇿⟨ sym′ xs₁≈xs₁′ ⟩
      x ∈ xs₁   ≈⟨ xs₁≈xs₂ ⟩′
      x ∈ xs₂   ⇿⟨ xs₂≈xs₂′ ⟩
      x ∈ xs₂′  ∎′) ∷ ∂p₁≈∂p₂

  whnf : ∀ {k Tok R xs₁ xs₂}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂} →
         p₁ ≈[ k ]P p₂ → p₁ ≈[ k ]W p₂
  whnf (xs₁≈xs₂ ∷ ∂p₁≈∂p₂)   = xs₁≈xs₂ ∷ λ t → ♭ (∂p₁≈∂p₂ t)
  whnf (p ∎)                 = reflW p
  whnf (p₁ ≈⟨ p₁≈p₂ ⟩ p₂≈p₃) = transW  (whnf p₁≈p₂) (whnf p₂≈p₃)
  whnf (p₁ ≅⟨ p₁≅p₂ ⟩ p₂≈p₃) = transW≅ (whnf p₁≅p₂) (whnf p₂≈p₃)
  whnf (sym p₁≈p₂)           = symW (whnf p₁≈p₂)
  whnf (♭♯ ys₁ ys₂ p₁≈p₂)    = ♭♯W ys₁ ys₂ (whnf p₁≈p₂)
  whnf (return P.refl)       = reflW (return _)
  whnf fail                  = reflW fail
  whnf token                 = reflW token
  whnf (p₁≈p₃ ∣ p₂≈p₄)       = whnf p₁≈p₃ ∣W whnf p₂≈p₄
  whnf (f₁≗f₂ <$> p₁≈p₂)     = f₁≗f₂ <$>W whnf p₁≈p₂
  whnf (p₁≈p₃ ⊛ p₂≈p₄)       = whnf p₁≈p₃ ⊛W whnf p₂≈p₄
  whnf (p₁≈p₃ ⊙′ p₂≈p₄)      = whnf p₁≈p₃ ⊙W whnf p₂≈p₄
  whnf (p₁≈p₃ >>= p₂≈p₄)     = whnf p₁≈p₃ >>=W  λ x → whnf (p₂≈p₄ x)
  whnf (p₁≈p₃ ≫=′ p₂≈p₄)     = whnf p₁≈p₃ ≫=W   λ x → whnf (p₂≈p₄ x)
  whnf (p₁≈p₃ ∞>>= p₂≈p₄)    = whnf p₁≈p₃ ∞>>=W λ x → whnf (p₂≈p₄ x)
  whnf (nonempty p₁≈p₂)      = nonemptyW (whnf p₁≈p₂)
  whnf (cast p₁≈p₂)          = castW (whnf p₁≈p₂)

sound : ∀ {k Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂} →
        p₁ ≈[ k ]P p₂ → p₁ ≈[ k ] p₂
sound = CE.sound ∘ soundW ∘ whnf
  where
  soundW : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ]W p₂ → p₁ ≈[ k ]′  p₂
  soundW (xs₁≈xs₂ ∷ ∂p₁≈∂p₂) =
    (λ {_} → xs₁≈xs₂) ∷ λ t → ♯ soundW (whnf (∂p₁≈∂p₂ t))
