------------------------------------------------------------------------
-- The backend does not introduce any unneeded ambiguity
------------------------------------------------------------------------

-- This module contains a proof showing that
-- TotalParserCombinators.BreadthFirst.Derivative.complete is a left
-- inverse of TotalParserCombinators.BreadthFirst.Derivative.sound.
-- This implies that the (finite) type x ∈ parseComplete p s contains
-- at most as many proofs as x ∈ p · s. In other words, the output of
-- parseComplete p s can only contain n copies of x if there are at
-- least n distinct parse trees in x ∈ p · s.

module TotalParserCombinators.BreadthFirst.LeftInverse where

open import Category.Monad
open import Coinduction
open import Function
open import Data.List as List
open import Data.List.Any as Any
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (refl)

open Any.Membership-≡
private
  open RawMonad List.monad using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.Applicative using (_⊛′_)
open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.BreadthFirst.SoundComplete
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Lib
import TotalParserCombinators.InitialSet as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

mutual

  ∂-complete∘∂-sound : ∀ {Tok R xs x s}
                       (p : Parser Tok R xs) {t} (x∈ : x ∈ ∂ p t · s) →
                       ∂-complete (∂-sound p x∈) ≡ x∈
  ∂-complete∘∂-sound token                      return                   = refl
  ∂-complete∘∂-sound (p₁ ∣ p₂)                  (∣ˡ    x∈p₁)             = cong ∣ˡ $ ∂-complete∘∂-sound p₁ x∈p₁
  ∂-complete∘∂-sound (p₁ ∣ p₂)                  (∣ʳ ._ x∈p₂)             = cong (∣ʳ (∂-initial p₁ _)) $ ∂-complete∘∂-sound p₂ x∈p₂
  ∂-complete∘∂-sound (f <$> p)                  (<$> x∈p)                = cong <$>_ $ ∂-complete∘∂-sound p  x∈p
  ∂-complete∘∂-sound (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)                 (f∈p₁′  ⊛ x∈p₂)   = cong₂ _⊛_ (∂-complete∘∂-sound p₁ f∈p₁′)
                                                                                     (Cast∈.sym∘ refl (♭?♯? (∂-initial p₁ _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)                 (f∈p₁′  ⊛ x∈p₂)   = cong₂ _⊛_
                                                                                 (∂-complete∘∂-sound (♭ p₁) f∈p₁′)
                                                                                 (Cast∈.sym∘ refl (♭?♯? (∂-initial (♭ p₁) _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)          (∣ˡ    (f∈p₁′  ⊛ x∈p₂))  = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ ⊛ pr₂))
                                                                                 (∂-complete∘∂-sound p₁ f∈p₁′)
                                                                                 (Cast∈.sym∘ refl (♭?♯? (∂-initial p₁ _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟨ p₁ ⟩ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))
    with                                  f∈ret⋆′
       | Cast∈.sym∘ refl (♭?♯? (∂-initial p₂ _)) refl f∈ret⋆
       |          Return⋆.sound (f ∷ fs) f∈ret⋆′
       | Return⋆.complete∘sound (f ∷ fs) f∈ret⋆′
    where f∈ret⋆′ = cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈ret⋆
  ∂-complete∘∂-sound (⟨_⟩ {x} {xs} p₁ ⊛ ⟨ p₂ ⟩)
                     (∣ʳ ._ (.(cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                     (Return⋆.complete f∈f∷fs)) ⊛ x∈p₂′))
    | ._ | refl | (refl , f∈f∷fs) | refl = cong₂ (λ pr₁ pr₂ → ∣ʳ (∂-initial p₁ _ ⊛′ (x ∷ xs))
                                                                 (cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                                                        (Return⋆.complete pr₁) ⊛ pr₂))
                                                 (I.complete∘sound p₁ f∈f∷fs)
                                                 (∂-complete∘∂-sound p₂ x∈p₂′)
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)          (∣ˡ    (f∈p₁′  ⊛ x∈p₂))  = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ ⊛ pr₂))
                                                                                 (∂-complete∘∂-sound (♭ p₁) f∈p₁′)
                                                                                 (Cast∈.sym∘ refl (♭?♯? (∂-initial (♭ p₁) _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))
    with                                  f∈ret⋆′
       | Cast∈.sym∘ refl (♭?♯? (∂-initial p₂ _)) refl f∈ret⋆
       |          Return⋆.sound (f ∷ fs) f∈ret⋆′
       | Return⋆.complete∘sound (f ∷ fs) f∈ret⋆′
    where f∈ret⋆′ = cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈ret⋆
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)
                     (∣ʳ ._ (.(cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                     (Return⋆.complete f∈f∷fs)) ⊛ x∈p₂′))
    | ._ | refl | (refl , f∈f∷fs) | refl = cong₂ (λ pr₁ pr₂ → ∣ʳ []
                                                                 (cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                                                        (Return⋆.complete pr₁) ⊛ pr₂))
                                                 (I.complete∘sound (♭ p₁) f∈f∷fs)
                                                 (∂-complete∘∂-sound p₂ x∈p₂′)
  ∂-complete∘∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y))
    with          Return⋆.sound (x ∷ xs) y∈ret⋆
       | Return⋆.complete∘sound (x ∷ xs) y∈ret⋆
  ∂-complete∘∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ (.(Return⋆.complete y∈x∷xs) >>= z∈p₂′y))
    | (refl , y∈x∷xs) | refl
    rewrite I.complete∘sound p₁ y∈x∷xs
          | ∂!-complete∘∂!-sound (p₂ _) z∈p₂′y = refl
  ∂-complete∘∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ˡ (x∈p₁′ >>=  y∈p₂x)) = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ >>= pr₂))
                                                                                  (∂-complete∘∂-sound p₁ x∈p₁′)
                                                                                  (Cast∈.sym∘ refl (♭?♯? (∂-initial p₁ _)) refl y∈p₂x)
  ∂-complete∘∂-sound (_>>=_  {xs = []}     p₁ p₂)     (x∈p₁′ >>=  y∈p₂x)  = cong₂ _>>=_
                                                                                  (∂-complete∘∂-sound p₁ x∈p₁′)
                                                                                  (Cast∈.sym∘ refl (♭?♯? (∂-initial p₁ _)) refl y∈p₂x)
  ∂-complete∘∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y))
    with          Return⋆.sound (x ∷ xs) y∈ret⋆
       | Return⋆.complete∘sound (x ∷ xs) y∈ret⋆
  ∂-complete∘∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ (.(Return⋆.complete y∈x∷xs) >>= z∈p₂′y))
    | (refl , y∈x∷xs) | refl
    rewrite I.complete∘sound (♭ p₁) y∈x∷xs
          | ∂!-complete∘∂!-sound (p₂ _) z∈p₂′y = refl
  ∂-complete∘∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ˡ (x∈p₁′ >>=! y∈p₂x)) = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ >>=! pr₂))
                                                                                  (∂-complete∘∂-sound (♭ p₁) x∈p₁′)
                                                                                  (Cast∈.sym∘ refl (♭?♯? (∂-initial (♭ p₁) _)) refl y∈p₂x)
  ∂-complete∘∂-sound (_>>=!_ {xs = []}     p₁ p₂)     (x∈p₁′ >>=! y∈p₂x)  = cong₂ _>>=!_
                                                                                  (∂-complete∘∂-sound (♭ p₁) x∈p₁′)
                                                                                  (Cast∈.sym∘ refl (♭?♯? (∂-initial (♭ p₁) _)) refl y∈p₂x)
  ∂-complete∘∂-sound (nonempty p)                 x∈p                     = ∂-complete∘∂-sound p x∈p
  ∂-complete∘∂-sound (cast _ p)                   x∈p                     = ∂-complete∘∂-sound p x∈p

  ∂-complete∘∂-sound (return _) ()
  ∂-complete∘∂-sound fail       ()

  ∂!-complete∘∂!-sound : ∀ {Tok R₁ R₂ z t s xs y} {ys : List R₁}
                         (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) →
                         (z∈p′ : z ∈ ∂! p t · s) →
                         ∂!-complete p (∂!-sound p z∈p′) ≡ z∈p′
  ∂!-complete∘∂!-sound ⟨ p ⟩ z∈p′ = ∂-complete∘∂-sound p z∈p′

complete∘sound : ∀ {Tok R xs x} s
                 (p : Parser Tok R xs) (x∈p : x ∈ parseComplete p s) →
                 complete s (sound s x∈p) ≡ x∈p
complete∘sound []      p x∈p = I.complete∘sound p x∈p
complete∘sound (t ∷ s) p x∈p rewrite ∂-complete∘∂-sound p (sound s x∈p) =
  complete∘sound s (∂ p t) x∈p
