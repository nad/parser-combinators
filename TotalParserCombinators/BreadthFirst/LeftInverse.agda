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

open import Coinduction
open import Data.List
import Data.List.Any as Any
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (refl)

open Any.Membership-≡

open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.BreadthFirst.SoundComplete
open import TotalParserCombinators.Lib
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

∂-complete∘∂-sound : ∀ {Tok R xs x s}
                     (p : Parser Tok R xs) {t} (x∈ : x ∈ ∂ p t · s) →
                     ∂-complete (∂-sound p x∈) ≡ x∈
∂-complete∘∂-sound token     return       = refl
∂-complete∘∂-sound (p₁ ∣ p₂) (∣ˡ    x∈p₁) rewrite ∂-complete∘∂-sound p₁ x∈p₁ = refl
∂-complete∘∂-sound (p₁ ∣ p₂) (∣ʳ ._ x∈p₂) rewrite ∂-complete∘∂-sound p₂ x∈p₂ = refl
∂-complete∘∂-sound (f <$> p) (<$> x∈p)    rewrite ∂-complete∘∂-sound p  x∈p  = refl

∂-complete∘∂-sound (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)        (f∈p₁′  ⊛ x∈p₂)  rewrite ∂-complete∘∂-sound p₁ f∈p₁′ = refl
∂-complete∘∂-sound (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂) (∣ˡ    (f∈p₁′  ⊛ x∈p₂)) rewrite ∂-complete∘∂-sound p₁ f∈p₁′ = refl
∂-complete∘∂-sound (_⊛_ {fs = just fs} {xs = just xs} p₁ p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))
  with          Return⋆.sound fs f∈ret⋆
     | Return⋆.complete∘sound fs f∈ret⋆
∂-complete∘∂-sound (_⊛_ {fs = just fs} {xs = just xs} p₁ p₂) (∣ʳ ._ (.(Return⋆.complete f∈fs) ⊛ x∈p₂′)) | (refl , f∈fs) | refl
  rewrite I.complete∘sound p₁ f∈fs | ∂-complete∘∂-sound p₂ x∈p₂′ = refl
∂-complete∘∂-sound (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)        (f∈p₁′  ⊛ x∈p₂)  rewrite ∂-complete∘∂-sound (♭ p₁) f∈p₁′ = refl
∂-complete∘∂-sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣ˡ    (f∈p₁′  ⊛ x∈p₂)) rewrite ∂-complete∘∂-sound (♭ p₁) f∈p₁′ = refl
∂-complete∘∂-sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))
  with          Return⋆.sound fs f∈ret⋆
     | Return⋆.complete∘sound fs f∈ret⋆
∂-complete∘∂-sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣ʳ ._ (.(Return⋆.complete f∈fs) ⊛ x∈p₂′)) | (refl , f∈fs) | refl
  rewrite I.complete∘sound (♭ p₁) f∈fs | ∂-complete∘∂-sound p₂ x∈p₂′ = refl

∂-complete∘∂-sound (_>>=_ {xs = nothing} {f = just _} p₁ p₂)        (x∈p₁′  >>= y∈p₂x)  rewrite ∂-complete∘∂-sound p₁ x∈p₁′ = refl
∂-complete∘∂-sound (_>>=_ {xs = just _}  {f = just _} p₁ p₂) (∣ˡ    (x∈p₁′  >>= y∈p₂x)) rewrite ∂-complete∘∂-sound p₁ x∈p₁′ = refl
∂-complete∘∂-sound (_>>=_ {xs = just xs} {f = just _} p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y))
  with          Return⋆.sound xs y∈ret⋆
     | Return⋆.complete∘sound xs y∈ret⋆
∂-complete∘∂-sound (_>>=_ {xs = just xs} {f = just _} p₁ p₂) (∣ʳ ._ (.(Return⋆.complete y∈xs) >>= z∈p₂′y)) | (refl , y∈xs) | refl
  rewrite I.complete∘sound p₁ y∈xs | ∂-complete∘∂-sound (p₂ _) z∈p₂′y = refl
∂-complete∘∂-sound (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)        (x∈p₁′  >>= y∈p₂x)  rewrite ∂-complete∘∂-sound (♭ p₁) x∈p₁′ = refl
∂-complete∘∂-sound (_>>=_ {xs = just _}  {f = nothing} p₁ p₂) (∣ˡ    (x∈p₁′  >>= y∈p₂x)) rewrite ∂-complete∘∂-sound (♭ p₁) x∈p₁′ = refl
∂-complete∘∂-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y))
  with          Return⋆.sound xs y∈ret⋆
     | Return⋆.complete∘sound xs y∈ret⋆
∂-complete∘∂-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣ʳ ._ (.(Return⋆.complete y∈xs) >>= z∈p₂′y)) | (refl , y∈xs) | refl
  rewrite I.complete∘sound (♭ p₁) y∈xs | ∂-complete∘∂-sound (p₂ _) z∈p₂′y = refl

∂-complete∘∂-sound (nonempty p) x∈p = ∂-complete∘∂-sound p x∈p
∂-complete∘∂-sound (cast _ p)   x∈p = ∂-complete∘∂-sound p x∈p

∂-complete∘∂-sound (return _) ()
∂-complete∘∂-sound fail       ()

complete∘sound : ∀ {Tok R xs x} s
                 (p : Parser Tok R xs) (x∈p : x ∈ parseComplete p s) →
                 complete s (sound s x∈p) ≡ x∈p
complete∘sound []      p x∈p = I.complete∘sound p x∈p
complete∘sound (t ∷ s) p x∈p rewrite ∂-complete∘∂-sound p (sound s x∈p) =
  complete∘sound s (∂ p t) x∈p
