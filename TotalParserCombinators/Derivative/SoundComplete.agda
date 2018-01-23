------------------------------------------------------------------------
-- Soundness and completeness
------------------------------------------------------------------------

module TotalParserCombinators.Derivative.SoundComplete where

open import Category.Monad
open import Coinduction
open import Data.List
import Data.List.Categorical
open import Data.Maybe
open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

open RawMonad {f = zero} Data.List.Categorical.monad
  using () renaming (_>>=_ to _>>=′_; _⊛_ to _⊛′_)

open import TotalParserCombinators.Derivative.Definition
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- Soundness

sound : ∀ {Tok R xs x s} {t} (p : Parser Tok R xs) →
        x ∈ D t p · s → x ∈ p · t ∷ s
sound token                   return            = token
sound (p₁ ∣ p₂)               (∣-left     x∈p₁) = ∣-left      (sound p₁ x∈p₁)
sound (_∣_ {xs₁ = xs₁} p₁ p₂) (∣-right ._ x∈p₂) = ∣-right xs₁ (sound p₂ x∈p₂)
sound (f <$> p)               (<$> x∈p)         = <$> sound p x∈p
sound (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)             (f∈p₁′  ⊛ x∈p₂)       = [ ○ - ◌ ] sound p₁ f∈p₁′ ⊛ x∈p₂
sound (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂) (∣-left     (f∈p₁′  ⊛ x∈p₂))      = [ ○ - ○ ] sound p₁ f∈p₁′ ⊛ x∈p₂
sound (_⊛_ {fs = just fs} {xs = just _}  p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     with Return⋆.sound fs f∈ret⋆
sound (_⊛_ {fs = just fs} {xs = just _}  p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     | (refl , f∈fs) =
                                                                                    [ ○ - ○ ] I.sound p₁ f∈fs ⊛ sound p₂ x∈p₂′
sound (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)             (f∈p₁′  ⊛ x∈p₂)       = [ ◌ - ◌ ] sound (♭ p₁) f∈p₁′ ⊛ x∈p₂
sound (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂) (∣-left     (f∈p₁′  ⊛ x∈p₂))      = [ ◌ - ○ ] sound (♭ p₁) f∈p₁′ ⊛ x∈p₂
sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     with Return⋆.sound fs f∈ret⋆
sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     | (refl , f∈fs) =
                                                                                    [ ◌ - ○ ] I.sound (♭ p₁) f∈fs ⊛ sound p₂ x∈p₂′
sound (_>>=_ {xs = nothing} {f = just _}  p₁ p₂)             (x∈p₁′  >>= y∈p₂x)   = [ ○ - ◌ ] sound p₁ x∈p₁′ >>= y∈p₂x
sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) with Return⋆.sound xs y∈ret⋆
sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) | (refl , y∈xs) =
                                                                                    [ ○ - ○ ] I.sound p₁ y∈xs >>= sound (p₂ _) z∈p₂′y
sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣-left     (x∈p₁′  >>= y∈p₂x))  = [ ○ - ○ ] sound p₁ x∈p₁′ >>= y∈p₂x
sound (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)             (x∈p₁′  >>= y∈p₂x)   = [ ◌ - ◌ ] sound (♭ p₁) x∈p₁′ >>= y∈p₂x
sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) with Return⋆.sound xs y∈ret⋆
sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) | (refl , y∈xs) =
                                                                                    [ ◌ - ○ ] I.sound (♭ p₁) y∈xs >>= sound (p₂ _) z∈p₂′y
sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣-left     (x∈p₁′  >>= y∈p₂x))  = [ ◌ - ○ ] sound (♭ p₁) x∈p₁′ >>= y∈p₂x
sound (nonempty p) x∈p = nonempty (sound p x∈p)
sound (cast _ p)   x∈p = cast (sound p x∈p)

sound (return _) ()
sound fail       ()

------------------------------------------------------------------------
-- Completeness

mutual

  complete : ∀ {Tok R xs x s t} {p : Parser Tok R xs} →
             x ∈ p · t ∷ s → x ∈ D t p · s
  complete x∈p = complete′ _ x∈p refl

  complete′ : ∀ {Tok R xs x s s′ t} (p : Parser Tok R xs) →
                x ∈ p · s′ → s′ ≡ t ∷ s → x ∈ D t p · s
  complete′ token     token       refl = return

  complete′ (p₁ ∣ p₂) (∣-left    x∈p₁) refl = ∣-left               (complete x∈p₁)
  complete′ (p₁ ∣ p₂) (∣-right _ x∈p₂) refl = ∣-right (D-bag _ p₁) (complete x∈p₂)

  complete′ (f <$> p) (<$> x∈p)   refl = <$> complete x∈p

  complete′ (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)
            (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =         _⊛_ {fs = ○} {xs = ○}  (complete f∈p₁) x∈p₂
  complete′ (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂)
            (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣-left (_⊛_ {fs = ○} {xs = ○}  (complete f∈p₁) x∈p₂)
  complete′ (_⊛_ {fs = just _}  {xs = just xs} p₁ p₂)
            (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣-right (D-bag _ p₁ ⊛′ xs)
                                                   (_⊛_ {fs = ○} {xs = ○}
                                                        (Return⋆.complete (I.complete f∈p₁)) (complete x∈p₂))
  complete′ (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)
            (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =         _⊛_ {fs = ○} {xs = ◌} (complete f∈p₁) x∈p₂
  complete′ (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂)
            (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣-left (_⊛_ {fs = ○} {xs = ◌} (complete f∈p₁) x∈p₂)
  complete′ (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂)
            (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣-right []
                                                   (_⊛_ {fs = ○} {xs = ○}
                                                        (Return⋆.complete (I.complete f∈p₁)) (complete x∈p₂))

  complete′ (_>>=_ {xs = nothing} {f = just _}  p₁ p₂)
            (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =         _>>=_ {xs = ○} {f = ○} (complete x∈p₁) y∈p₂x
  complete′ (_>>=_ {xs = just _}  {f = just _}  p₁ p₂)
            (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣-left (_>>=_ {xs = ○} {f = ○} (complete x∈p₁) y∈p₂x)
  complete′ (_>>=_ {xs = just _}  {f = just f}  p₁ p₂)
            (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣-right (D-bag _ p₁ >>=′ f)
                                                      (_>>=_ {xs = ○} {f = ○}
                                                             (Return⋆.complete (I.complete x∈p₁)) (complete y∈p₂x))

  complete′ (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)
            (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =         _>>=_ {xs = ○} {f = ◌} (complete x∈p₁) y∈p₂x
  complete′ (_>>=_ {xs = just _}  {f = nothing} p₁ p₂)
            (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣-left (_>>=_ {xs = ○} {f = ◌} (complete x∈p₁) y∈p₂x)
  complete′ (_>>=_ {xs = just _}  {f = nothing} p₁ p₂)
            (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣-right []
                                                      (_>>=_ {xs = ○} {f = ○}
                                                             (Return⋆.complete (I.complete x∈p₁)) (complete y∈p₂x))

  complete′ (nonempty p) (nonempty x∈p) refl = complete x∈p

  complete′ (cast _ p) (cast x∈p) refl = complete x∈p

  complete′ (return _) () refl
  complete′ fail       () refl
  complete′ (_⊛_   {fs = nothing} _ _) (_⊛_   {s₁ = []} f∈p₁ _) _ with I.complete f∈p₁
  ... | ()
  complete′ (_>>=_ {xs = nothing} _ _) (_>>=_ {s₁ = []} x∈p₁ _) _ with I.complete x∈p₁
  ... | ()
