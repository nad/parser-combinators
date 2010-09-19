------------------------------------------------------------------------
-- The parser equivalence proof language is sound
------------------------------------------------------------------------

module TotalParserCombinators.Congruence.Sound where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Properties as ListProp
import Data.List.Any as Any
import Data.List.Any.BagAndSetEquality as BSEq
open import Data.Maybe as Maybe using (Maybe); open Maybe.Maybe
open import Function
import Function.Inverse as Inv
open import Relation.Binary.PropositionalEquality as P using (_≗_)

open Any.Membership-≡ using (_∈_; bag) renaming (_≈[_]_ to _List-≈[_]_)
open Inv.EquationalReasoning
  renaming (_≈⟨_⟩_ to _≈⟨_⟩′_; _∎ to _∎′; sym to sym′)
open RawMonad List.monad
  using () renaming (_⊛_ to _⊛′_; _>>=_ to _>>=′_)
private
  module BSMonoid {k} {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid k A)

open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.CoinductiveEquality as CE
  using (_≈[_]c_; _∷_)
open import TotalParserCombinators.Congruence
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

open D

------------------------------------------------------------------------
-- Some lemmas

private

  >>=-[]-lemma : ∀ {A B : Set} xs (f : A → List B) {k} →
                 (∀ x → [] List-≈[ k ] f x) →
                 [] List-≈[ k ] (xs >>=′ f)
  >>=-[]-lemma xs f []≈f {x} =
    x ∈ []                  ≈⟨ BSMonoid.reflexive $ P.sym $
                                 ListProp.Monad.right-zero xs ⟩′
    x ∈ (xs >>=′ λ _ → [])  ≈⟨ BSEq.>>=-cong (BSMonoid.refl {x = xs})
                                             []≈f ⟩′
    x ∈ (xs >>=′ f)         ∎′

  ⊛-[]-lemma : ∀ {A B : Set} (fs : List (A → B)) xs {k} →
               [] List-≈[ k ] xs →
               [] List-≈[ k ] (fs ⊛′ xs)
  ⊛-[]-lemma fs xs []≈xs {x} =
    x ∈ []          ≈⟨ BSMonoid.reflexive $ P.sym $
                         ListProp.Applicative.right-zero fs ⟩′
    x ∈ (fs ⊛′ [])  ≈⟨ BSEq.⊛-cong (BSMonoid.refl {x = fs}) []≈xs ⟩′
    x ∈ (fs ⊛′ xs)  ∎′

------------------------------------------------------------------------
-- Soundness

private

  -- WHNFs of equality proof programs.

  infix 4 _≈[_]W_

  record _≈[_]W_ {Tok R xs₁ xs₂}
                 (p₁ : Parser Tok R xs₁) (k : Kind)
                 (p₂ : Parser Tok R xs₂) : Set₁ where
    constructor _∷_
    field
      head : xs₁ List-≈[ k ] xs₂
      tail : ∀ t → D t p₁ ≈[ k ]P D t p₂

  open _≈[_]W_

  forget : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ]W p₂ → p₁ ≈[ k ]P p₂
  forget (xs₁≈xs₂ ∷ Dp₁≈Dp₂) = xs₁≈xs₂ ∷ λ t → ♯ Dp₁≈Dp₂ t

  reflW : ∀ {k Tok R xs} (p : Parser Tok R xs) → p ≈[ k ]W p
  reflW p = (_ ∎′) ∷ λ t → D t p ∎

  transW : ∀ {k Tok R xs₁ xs₂ xs₃}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂}
             {p₃ : Parser Tok R xs₃} →
           p₁ ≈[ k ]W p₂ → p₂ ≈[ k ]W p₃ → p₁ ≈[ k ]W p₃
  transW (xs₁≈xs₂ ∷ Dp₁≈Dp₂) (xs₂≈xs₃ ∷ Dp₂≈Dp₃) =
    (_ ≈⟨ xs₁≈xs₂ ⟩′ xs₂≈xs₃) ∷ λ t → _ ≈⟨ Dp₁≈Dp₂ t ⟩ Dp₂≈Dp₃ t

  transW≅ : ∀ {k Tok R xs₁ xs₂ xs₃}
              {p₁ : Parser Tok R xs₁}
              {p₂ : Parser Tok R xs₂}
              {p₃ : Parser Tok R xs₃} →
            p₁ ≈[ parser ]W p₂ → p₂ ≈[ k ]W p₃ → p₁ ≈[ k ]W p₃
  transW≅ (xs₁≅xs₂ ∷ Dp₁≅Dp₂) (xs₂≈xs₃ ∷ Dp₂≈Dp₃) =
    (_ ⇿⟨ xs₁≅xs₂ ⟩ xs₂≈xs₃) ∷ λ t → _ ≅⟨ Dp₁≅Dp₂ t ⟩ Dp₂≈Dp₃ t

  symW : ∀ {k Tok R xs₁ xs₂}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂} →
         p₁ ≈[ k ]W p₂ → p₂ ≈[ k ]W p₁
  symW (xs₁≈xs₂ ∷ Dp₁≈Dp₂) = sym′ xs₁≈xs₂ ∷ λ t → sym (Dp₁≈Dp₂ t)

  _∣W_ : ∀ {k Tok R xs₁ xs₂ xs₃ xs₄}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂}
           {p₃ : Parser Tok R xs₃}
           {p₄ : Parser Tok R xs₄} →
         p₁ ≈[ k ]W p₃ → p₂ ≈[ k ]W p₄ → p₁ ∣ p₂ ≈[ k ]W p₃ ∣ p₄
  (xs₁≈xs₂ ∷ Dp₁≈Dp₂) ∣W (xs₃≈xs₄ ∷ Dp₃≈Dp₄) =
    BSMonoid.∙-cong xs₁≈xs₂ xs₃≈xs₄ ∷ λ t → Dp₁≈Dp₂ t ∣ Dp₃≈Dp₄ t

  _<$>W_ : ∀ {k Tok R₁ R₂} {f₁ f₂ : R₁ → R₂} {xs₁ xs₂}
             {p₁ : Parser Tok R₁ xs₁}
             {p₂ : Parser Tok R₁ xs₂} →
          f₁ ≗ f₂ → p₁ ≈[ k ]W p₂ → f₁ <$> p₁ ≈[ k ]W f₂ <$> p₂
  f₁≗f₂ <$>W (xs₁≈xs₂ ∷ Dp₁≈Dp₂) =
    BSEq.map-cong f₁≗f₂ xs₁≈xs₂ ∷ λ t → f₁≗f₂ <$> Dp₁≈Dp₂ t

  [_-_-_-_]_⊛W_ :
    ∀ {k Tok R₁ R₂} xs₁ xs₂ fs₁ fs₂
      {p₁ : ∞⟨ xs₁ ⟩Parser Tok (R₁ → R₂) (flatten fs₁)}
      {p₂ : ∞⟨ fs₁ ⟩Parser Tok  R₁       (flatten xs₁)}
      {p₃ : ∞⟨ xs₂ ⟩Parser Tok (R₁ → R₂) (flatten fs₂)}
      {p₄ : ∞⟨ fs₂ ⟩Parser Tok  R₁       (flatten xs₂)} →
    ♭? p₁ ≈[ k ]W ♭? p₃ → ♭? p₂ ≈[ k ]W ♭? p₄ → p₁ ⊛ p₂ ≈[ k ]W p₃ ⊛ p₄
  [_-_-_-_]_⊛W_ {k} {R₁ = R₁} xs₁ xs₂ fs₁ fs₂ {p₁} {p₂} {p₃} {p₄}
       (fs₁≈fs₂ ∷ Dp₁≈Dp₃) (xs₁≈xs₂ ∷ Dp₂≈Dp₄) =
    lemma xs₁ xs₂ xs₁≈xs₂ ∷ λ t →
      D t (p₁ ⊛ p₂)                                              ≅⟨ D-⊛ p₁ p₂ ⟩
      D t (♭? p₁) ⊛ ♭? p₂ ∣ return⋆ (flatten fs₁) ⊛ D t (♭? p₂)  ≈⟨ [ ○ - ○ - ○ - ○ ] Dp₁≈Dp₃ t ⊛ (xs₁≈xs₂ ∷ λ t → ♯ Dp₂≈Dp₄ t) ∣
                                                                    [ ○ - ○ - ○ - ○ ] Return⋆.cong fs₁≈fs₂ ⊛ Dp₂≈Dp₄ t ⟩
      D t (♭? p₃) ⊛ ♭? p₄ ∣ return⋆ (flatten fs₂) ⊛ D t (♭? p₄)  ≅⟨ sym $ D-⊛ p₃ p₄ ⟩
      D t (p₃ ⊛ p₄)                                              ∎
    where
    lemma : (xs₁ xs₂ : Maybe (List R₁)) →
            flatten xs₁ List-≈[ k ] flatten xs₂ →
            flatten fs₁ ⊛flatten xs₁ List-≈[ k ]
            flatten fs₂ ⊛flatten xs₂
    lemma nothing    nothing     []≈[]  = BSMonoid.refl
    lemma nothing    (just xs₂)  []≈xs₂ = ⊛-[]-lemma (flatten fs₂) xs₂ []≈xs₂
    lemma (just xs₁) nothing    xs₁≈[]  = BSMonoid.sym $ ⊛-[]-lemma (flatten fs₁) xs₁ (BSMonoid.sym xs₁≈[])
    lemma (just xs₁) (just xs₂) xs₁≈xs₂ = BSEq.⊛-cong fs₁≈fs₂ xs₁≈xs₂

  [_-_-_-_]_>>=W_ :
    ∀ {k Tok R₁ R₂} (f₁ f₂ : Maybe (R₁ → List R₂)) xs₁ xs₂
      {p₁ : ∞⟨ f₁ ⟩Parser Tok R₁ (flatten xs₁)}
      {p₂ : (x : R₁) → ∞⟨ xs₁ ⟩Parser Tok R₂ (apply f₁ x)}
      {p₃ : ∞⟨ f₂ ⟩Parser Tok R₁ (flatten xs₂)}
      {p₄ : (x : R₁) → ∞⟨ xs₂ ⟩Parser Tok R₂ (apply f₂ x)} →
    ♭? p₁ ≈[ k ]W ♭? p₃ → (∀ x → ♭? (p₂ x) ≈[ k ]W ♭? (p₄ x)) →
    p₁ >>= p₂ ≈[ k ]W p₃ >>= p₄
  [_-_-_-_]_>>=W_ {k} {R₁ = R₁} {R₂} f₁ f₂ xs₁ xs₂ {p₁} {p₂} {p₃} {p₄}
                  (xs₁≈xs₂ ∷ Dp₁≈Dp₃) p₂≈p₄ = lemma f₁ f₂ (head ∘ p₂≈p₄) ∷ λ t →
    D t (p₁ >>= p₂)                                                                ≅⟨ D->>= p₁ p₂ ⟩
    D t (♭? p₁) >>= (♭? ∘ p₂) ∣ return⋆ (flatten xs₁) >>= (λ x → D t (♭? (p₂ x)))  ≈⟨ [ ○ - ○ - ○ - ○ ] Dp₁≈Dp₃ t >>= (forget ∘ p₂≈p₄) ∣
                                                                                      [ ○ - ○ - ○ - ○ ] Return⋆.cong xs₁≈xs₂ >>=
                                                                                                        (λ x → tail (p₂≈p₄ x) t) ⟩
    D t (♭? p₃) >>= (♭? ∘ p₄) ∣ return⋆ (flatten xs₂) >>= (λ x → D t (♭? (p₄ x)))  ≅⟨ sym $ D->>= p₃ p₄ ⟩
    D t (p₃ >>= p₄)                                                                ∎
    where
    lemma : (f₁ f₂ : Maybe (R₁ → List R₂)) →
            (∀ x → apply f₁ x List-≈[ k ] apply f₂ x) →
            bind xs₁ f₁ List-≈[ k ] bind xs₂ f₂
    lemma nothing   nothing   f₁≈f₂ = BSMonoid.refl
    lemma nothing   (just f₂) f₁≈f₂ = >>=-[]-lemma (flatten xs₂) f₂ f₁≈f₂
    lemma (just f₁) nothing   f₁≈f₂ = BSMonoid.sym $ >>=-[]-lemma (flatten xs₁) f₁ (BSMonoid.sym ∘ f₁≈f₂)
    lemma (just f₁) (just f₂) f₁≈f₂ = BSEq.>>=-cong xs₁≈xs₂ f₁≈f₂

  nonemptyW : ∀ {k Tok R xs₁ xs₂}
                {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
             p₁ ≈[ k ]W p₂ → nonempty p₁ ≈[ k ]W nonempty p₂
  nonemptyW (xs₁≈xs₂ ∷ Dp₁≈Dp₂) = (_ ∎′) ∷ Dp₁≈Dp₂

  castW : ∀ {k Tok R xs₁ xs₂ xs₁′ xs₂′}
            {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂}
            {xs₁≈xs₁′ : xs₁ List-≈[ bag ] xs₁′}
            {xs₂≈xs₂′ : xs₂ List-≈[ bag ] xs₂′} →
         p₁ ≈[ k ]W p₂ → cast xs₁≈xs₁′ p₁ ≈[ k ]W cast xs₂≈xs₂′ p₂
  castW {xs₁ = xs₁} {xs₂} {xs₁′} {xs₂′}
        {xs₁≈xs₁′ = xs₁≈xs₁′} {xs₂≈xs₂′} (xs₁≈xs₂ ∷ Dp₁≈Dp₂) =
    (λ {x} →
      x ∈ xs₁′  ⇿⟨ sym′ xs₁≈xs₁′ ⟩
      x ∈ xs₁   ≈⟨ xs₁≈xs₂ ⟩′
      x ∈ xs₂   ⇿⟨ xs₂≈xs₂′ ⟩
      x ∈ xs₂′  ∎′) ∷ Dp₁≈Dp₂

  whnf : ∀ {k Tok R xs₁ xs₂}
           {p₁ : Parser Tok R xs₁}
           {p₂ : Parser Tok R xs₂} →
         p₁ ≈[ k ]P p₂ → p₁ ≈[ k ]W p₂
  whnf (xs₁≈xs₂ ∷ Dp₁≈Dp₂)                         = xs₁≈xs₂ ∷ λ t → ♭ (Dp₁≈Dp₂ t)
  whnf (p ∎)                                       = reflW p
  whnf (p₁ ≈⟨ p₁≈p₂ ⟩ p₂≈p₃)                       = transW  (whnf p₁≈p₂) (whnf p₂≈p₃)
  whnf (p₁ ≅⟨ p₁≅p₂ ⟩ p₂≈p₃)                       = transW≅ (whnf p₁≅p₂) (whnf p₂≈p₃)
  whnf (sym p₁≈p₂)                                 = symW (whnf p₁≈p₂)
  whnf (return P.refl)                             = reflW (return _)
  whnf fail                                        = reflW fail
  whnf token                                       = reflW token
  whnf (p₁≈p₃ ∣ p₂≈p₄)                             = whnf p₁≈p₃ ∣W whnf p₂≈p₄
  whnf (f₁≗f₂ <$> p₁≈p₂)                           = f₁≗f₂ <$>W whnf p₁≈p₂
  whnf ([ fs₁ - fs₂ - xs₁ - xs₂ ] p₁≈p₃ ⊛ p₂≈p₄)   = [ fs₁ - fs₂ - xs₁ - xs₂ ] whnf p₁≈p₃ ⊛W whnf p₂≈p₄
  whnf ([  f₁ -  f₂ - xs₁ - xs₂ ] p₁≈p₃ >>= p₂≈p₄) = [  f₁ -  f₂ - xs₁ - xs₂ ] whnf p₁≈p₃ >>=W λ x → whnf (p₂≈p₄ x)
  whnf (nonempty p₁≈p₂)                            = nonemptyW (whnf p₁≈p₂)
  whnf (cast p₁≈p₂)                                = castW (whnf p₁≈p₂)

sound : ∀ {k Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂} →
        p₁ ≈[ k ]P p₂ → p₁ ≈[ k ] p₂
sound = CE.sound ∘ soundW ∘ whnf
  where
  soundW : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ]W p₂ → p₁ ≈[ k ]c  p₂
  soundW (xs₁≈xs₂ ∷ Dp₁≈Dp₂) =
    (λ {_} → xs₁≈xs₂) ∷ λ t → ♯ soundW (whnf (Dp₁≈Dp₂ t))
