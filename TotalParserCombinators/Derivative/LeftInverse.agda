------------------------------------------------------------------------
-- The derivative operator does not introduce any unneeded ambiguity
------------------------------------------------------------------------

module TotalParserCombinators.Derivative.LeftInverse where

open import Codata.Musical.Notation
open import Data.Maybe hiding (_>>=_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality using (refl)

open import TotalParserCombinators.Derivative.Definition
open import TotalParserCombinators.Derivative.SoundComplete
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

complete∘sound : ∀ {Tok R xs x s t}
                 (p : Parser Tok R xs) (x∈ : x ∈ D t p · s) →
                 complete (sound p x∈) ≡ x∈
complete∘sound token     return            = refl
complete∘sound (p₁ ∣ p₂) (∣-left     x∈p₁) rewrite complete∘sound p₁ x∈p₁ = refl
complete∘sound (p₁ ∣ p₂) (∣-right ._ x∈p₂) rewrite complete∘sound p₂ x∈p₂ = refl
complete∘sound (f <$> p) (<$> x∈p)         rewrite complete∘sound p  x∈p  = refl

complete∘sound (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)             (f∈p₁′  ⊛ x∈p₂)  rewrite complete∘sound p₁ f∈p₁′ = refl
complete∘sound (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂) (∣-left     (f∈p₁′  ⊛ x∈p₂)) rewrite complete∘sound p₁ f∈p₁′ = refl
complete∘sound (_⊛_ {fs = just fs} {xs = just xs} p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))
  with (refl , f∈fs) ←          Return⋆.sound fs f∈ret⋆
     | refl          ← Return⋆.complete∘sound fs f∈ret⋆
  rewrite I.complete∘sound p₁ f∈fs | complete∘sound p₂ x∈p₂′ = refl
complete∘sound (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)             (f∈p₁′  ⊛ x∈p₂)  rewrite complete∘sound (♭ p₁) f∈p₁′ = refl
complete∘sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣-left     (f∈p₁′  ⊛ x∈p₂)) rewrite complete∘sound (♭ p₁) f∈p₁′ = refl
complete∘sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))
  with (refl , f∈fs) ←          Return⋆.sound fs f∈ret⋆
     | refl          ← Return⋆.complete∘sound fs f∈ret⋆
  rewrite I.complete∘sound (♭ p₁) f∈fs | complete∘sound p₂ x∈p₂′ = refl

complete∘sound (_>>=_ {xs = nothing} {f = just _} p₁ p₂)             (x∈p₁′  >>= y∈p₂x)  rewrite complete∘sound p₁ x∈p₁′ = refl
complete∘sound (_>>=_ {xs = just _}  {f = just _} p₁ p₂) (∣-left     (x∈p₁′  >>= y∈p₂x)) rewrite complete∘sound p₁ x∈p₁′ = refl
complete∘sound (_>>=_ {xs = just xs} {f = just _} p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y))
  with (refl , y∈xs) ←          Return⋆.sound xs y∈ret⋆
     | refl          ← Return⋆.complete∘sound xs y∈ret⋆
  rewrite I.complete∘sound p₁ y∈xs | complete∘sound (p₂ _) z∈p₂′y = refl
complete∘sound (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)             (x∈p₁′  >>= y∈p₂x)  rewrite complete∘sound (♭ p₁) x∈p₁′ = refl
complete∘sound (_>>=_ {xs = just _}  {f = nothing} p₁ p₂) (∣-left     (x∈p₁′  >>= y∈p₂x)) rewrite complete∘sound (♭ p₁) x∈p₁′ = refl
complete∘sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y))
  with (refl , y∈xs) ←          Return⋆.sound xs y∈ret⋆
     | refl          ← Return⋆.complete∘sound xs y∈ret⋆
  rewrite I.complete∘sound (♭ p₁) y∈xs | complete∘sound (p₂ _) z∈p₂′y = refl

complete∘sound (nonempty p) x∈p = complete∘sound p x∈p
complete∘sound (cast _ p)   x∈p = complete∘sound p x∈p

complete∘sound (return _) ()
complete∘sound fail       ()
