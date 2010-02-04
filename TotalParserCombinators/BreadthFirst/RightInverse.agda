------------------------------------------------------------------------
-- The backend does not remove any ambiguity
------------------------------------------------------------------------

-- This module contains a proof showing that
-- TotalParserCombinators.BreadthFirst.Derivative.complete is a right
-- inverse of TotalParserCombinators.BreadthFirst.Derivative.sound.
-- This implies that the (finite) type x ∈ parseComplete p s contains
-- at least as many proofs as x ∈ p · s. In other words, if the output
-- of parseComplete p s contains n copies of x, then there are at most
-- n distinct parse trees in x ∈ p · s.

module TotalParserCombinators.BreadthFirst.RightInverse where

open import Category.Monad
open import Coinduction
open import Function
open import Data.List as List
open import Data.List.Any as Any
open import Data.Product
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡
private
  open RawMonad List.monad using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.BreadthFirst.SoundComplete
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Lib
import TotalParserCombinators.InitialSet as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics hiding (_≅_)

mutual

  ∂-sound∘∂-complete : ∀ {Tok R xs x s t} {p : Parser Tok R xs} →
                       (x∈p : x ∈ p · t ∷ s) →
                       ∂-sound p (∂-complete x∈p) ≡ x∈p
  ∂-sound∘∂-complete x∈p = H.≅-to-≡ (∂-sound∘∂-complete′ _ x∈p refl)

  ∂-sound∘∂-complete′ :
    ∀ {Tok R xs x s′ s t}
    (p : Parser Tok R xs) (x∈p : x ∈ p · s′) (eq : s′ ≡ t ∷ s) →
    ∂-sound p (∂-complete′ p x∈p eq) ≅ x∈p
  ∂-sound∘∂-complete′ token     token       refl = refl

  ∂-sound∘∂-complete′ (p₁ ∣ p₂) (∣ˡ   x∈p₁) refl rewrite ∂-sound∘∂-complete x∈p₁ = refl
  ∂-sound∘∂-complete′ (p₁ ∣ p₂) (∣ʳ _ x∈p₂) refl rewrite ∂-sound∘∂-complete x∈p₂ = refl

  ∂-sound∘∂-complete′ (f <$> p) (<$> x∈p)   refl rewrite ∂-sound∘∂-complete x∈p = refl

  ∂-sound∘∂-complete′ (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫) (_⊛_ {s₁ = t ∷ _} f∈p₁ x∈p₂) refl
    rewrite ∂-sound∘∂-complete f∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial p₁ t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫) (_⊛_ {s₁ = t ∷ _} f∈p₁ x∈p₂) refl
    rewrite ∂-sound∘∂-complete f∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial (♭ p₁) t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩) (_⊛_ {s₁ = t ∷ _} f∈p₁ x∈p₂) refl
    rewrite ∂-sound∘∂-complete f∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial p₁ t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ {Tok = Tok} {t = t} (_⊛_ {fs = f ∷ fs} {xs = x ∷ xs} ⟨ p₁ ⟩ ⟨ p₂ ⟩) (_⊛_ {s₁ = []} f∈p₁ x∈p₂) refl
    with lhs | lemma
    where
    f∈f∷fs = I.complete f∈p₁
    c      = ⋁.complete {Tok = Tok} return f∈f∷fs return
    lhs    = ⋁.sound return (f ∷ fs) $
               cast∈ refl (♭?♯? (∂-initial p₂ t)) refl $
                 cast∈ refl (sym (♭?♯? (∂-initial p₂ t))) refl c
    lemma : lhs ≡ (_ , f∈f∷fs , return)
    lemma rewrite Cast∈.∘sym refl (♭?♯? (∂-initial p₂ t)) refl c =
          ⋁.sound∘complete return f∈f∷fs return
  ... | .(_ , I.complete f∈p₁ , return) | refl
    rewrite I.sound∘complete f∈p₁ | ∂-sound∘∂-complete x∈p₂ = refl

  ∂-sound∘∂-complete′ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩) (_⊛_ {s₁ = t ∷ _} f∈p₁ x∈p₂) refl
    rewrite ∂-sound∘∂-complete f∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial (♭ p₁) t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ {Tok = Tok} {t = t} (_⊛_ {fs = f ∷ fs} ⟪ p₁ ⟫ ⟨ p₂ ⟩) (_⊛_ {s₁ = []} f∈p₁ x∈p₂) refl
    with lhs | lemma
    where
    f∈f∷fs = I.complete f∈p₁
    c      = ⋁.complete {Tok = Tok} return f∈f∷fs return
    lhs    = ⋁.sound return (f ∷ fs) $
               cast∈ refl (♭?♯? (∂-initial p₂ t)) refl $
                 cast∈ refl (sym (♭?♯? (∂-initial p₂ t))) refl c
    lemma : lhs ≡ (_ , f∈f∷fs , return)
    lemma rewrite Cast∈.∘sym refl (♭?♯? (∂-initial p₂ t)) refl c =
          ⋁.sound∘complete return f∈f∷fs return
  ... | .(_ , I.complete f∈p₁ , return) | refl
    rewrite I.sound∘complete f∈p₁ | ∂-sound∘∂-complete x∈p₂ = refl

  ∂-sound∘∂-complete′ (_>>=_ {xs = x ∷ xs} {f} p₁ p₂) (_>>=_ {s₁ = []} x∈p₁ y∈p₂x) refl
    rewrite ∂-⋁-sound∘∂-⋁-complete p₂ (I.complete x∈p₁) y∈p₂x
          | I.sound∘complete x∈p₁ =
    refl
  ∂-sound∘∂-complete′ (_>>=_ {xs = x ∷ xs} p₁ p₂) (_>>=_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial p₁ t)) refl y∈p₂x =
    refl
  ∂-sound∘∂-complete′ (_>>=_ {R₁} {xs = []} p₁ p₂) (_>>=_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial p₁ t)) refl y∈p₂x =
    refl

  ∂-sound∘∂-complete′ (_>>=!_ {xs = x ∷ xs} p₁ p₂) (_>>=!_ {s₁ = []} x∈p₁ y∈p₂x) refl
    rewrite ∂-⋁-sound∘∂-⋁-complete p₂ (I.complete x∈p₁) y∈p₂x
          | I.sound∘complete x∈p₁ =
    refl
  ∂-sound∘∂-complete′ (_>>=!_ {xs = x ∷ xs} p₁ p₂) (_>>=!_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial (♭ p₁) t)) refl y∈p₂x =
    refl
  ∂-sound∘∂-complete′ (_>>=!_ {R₁} {xs = []} p₁ p₂) (_>>=!_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | Cast∈.∘sym refl (♭?♯? (∂-initial (♭ p₁) t)) refl y∈p₂x =
    refl

  ∂-sound∘∂-complete′ (nonempty p) (nonempty x∈p) refl rewrite ∂-sound∘∂-complete x∈p = refl

  ∂-sound∘∂-complete′ (cast _ p) (cast x∈p) refl rewrite ∂-sound∘∂-complete x∈p = refl

  ∂-sound∘∂-complete′ (return _) () refl
  ∂-sound∘∂-complete′ fail       () refl
  ∂-sound∘∂-complete′ (_ ⊛ ⟪ _ ⟫)            (_⊛_    {s₁ = []} f∈p₁ _) _ with I.complete f∈p₁
  ... | ()
  ∂-sound∘∂-complete′ (_>>=_  {xs = []} _ _) (_>>=_  {s₁ = []} x∈p₁ _) _ with I.complete x∈p₁
  ... | ()
  ∂-sound∘∂-complete′ (_>>=!_ {xs = []} _ _) (_>>=!_ {s₁ = []} x∈p₁ _) _ with I.complete x∈p₁
  ... | ()

  ∂-⋁-sound∘∂-⋁-complete :
    ∀ {Tok R₁ R₂ x t z s xs y} {ys : List R₁}
      {f : R₁ → List R₂}
    (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys))
    (x∈xs : x ∈ xs) (z∈px : z ∈ ♭? (p x) · t ∷ s) →
    ∂-⋁-sound xs p (∂-⋁-complete p x∈xs z∈px) ≡ (x , x∈xs , z∈px)
  ∂-⋁-sound∘∂-⋁-complete p (here refl)  y∈px rewrite ∂!-sound∘∂!-complete (p _) y∈px = refl
  ∂-⋁-sound∘∂-⋁-complete p (there x∈xs) y∈px rewrite ∂-⋁-sound∘∂-⋁-complete p x∈xs y∈px = refl

  ∂!-sound∘∂!-complete :
    ∀ {Tok R₁ R₂ z t s xs y} {ys : List R₁}
    (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) (z∈p : z ∈ ♭? p · t ∷ s) →
    ∂!-sound p (∂!-complete p z∈p) ≡ z∈p
  ∂!-sound∘∂!-complete ⟨ p ⟩ z∈p = ∂-sound∘∂-complete z∈p

sound∘complete : ∀ {Tok R xs x} {p : Parser Tok R xs}
                 (s : List Tok) (x∈p : x ∈ p · s) →
                 sound s (complete s x∈p) ≡ x∈p
sound∘complete []      x∈p = I.sound∘complete x∈p
sound∘complete (t ∷ s) x∈p
  rewrite sound∘complete s (∂-complete x∈p) = ∂-sound∘∂-complete x∈p
