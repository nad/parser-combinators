------------------------------------------------------------------------
-- Soundness and completeness
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.SoundComplete where

open import Category.Monad
open import Coinduction
open import Function
open import Data.List as List
open import Data.List.Any as Any
open import Data.Maybe
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡
open RawMonad List.monad
  using () renaming (_>>=_ to _>>=′_; _⊛_ to _⊛′_)

open import TotalParserCombinators.Lib
open import TotalParserCombinators.BreadthFirst.Derivative
import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- Soundness

∂-sound : ∀ {Tok R xs x s} {t} (p : Parser Tok R xs) →
          x ∈ ∂ p t · s → x ∈ p · t ∷ s
∂-sound token                   return       = token
∂-sound (p₁ ∣ p₂)               (∣ˡ    x∈p₁) = ∣ˡ     (∂-sound p₁ x∈p₁)
∂-sound (_∣_ {xs₁ = xs₁} p₁ p₂) (∣ʳ ._ x∈p₂) = ∣ʳ xs₁ (∂-sound p₂ x∈p₂)
∂-sound (f <$> p)               (<$> x∈p)    = <$> ∂-sound p x∈p
∂-sound (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)        (f∈p₁′  ⊛ x∈p₂)       = [ ○ - ◌ ] ∂-sound p₁ f∈p₁′ ⊛ x∈p₂
∂-sound (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂) (∣ˡ    (f∈p₁′  ⊛ x∈p₂))      = [ ○ - ○ ] ∂-sound p₁ f∈p₁′ ⊛ x∈p₂
∂-sound (_⊛_ {fs = just fs} {xs = just _}  p₁ p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))     with Return⋆.sound fs f∈ret⋆
∂-sound (_⊛_ {fs = just fs} {xs = just _}  p₁ p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))     | (refl , f∈fs) =
                                                                                 [ ○ - ○ ] I.sound p₁ f∈fs ⊛ ∂-sound p₂ x∈p₂′
∂-sound (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)        (f∈p₁′  ⊛ x∈p₂)       = [ ◌ - ◌ ] ∂-sound (♭ p₁) f∈p₁′ ⊛ x∈p₂
∂-sound (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂) (∣ˡ    (f∈p₁′  ⊛ x∈p₂))      = [ ◌ - ○ ] ∂-sound (♭ p₁) f∈p₁′ ⊛ x∈p₂
∂-sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))     with Return⋆.sound fs f∈ret⋆
∂-sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣ʳ ._ (f∈ret⋆ ⊛ x∈p₂′))     | (refl , f∈fs) =
                                                                                 [ ◌ - ○ ] I.sound (♭ p₁) f∈fs ⊛ ∂-sound p₂ x∈p₂′
∂-sound (_>>=_ {xs = nothing} {f = just _}  p₁ p₂)        (x∈p₁′  >>= y∈p₂x)   = [ ○ - ◌ ] ∂-sound p₁ x∈p₁′ >>= y∈p₂x
∂-sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y)) with Return⋆.sound xs y∈ret⋆
∂-sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y)) | (refl , y∈xs) =
                                                                                 [ ○ - ○ ] I.sound p₁ y∈xs >>= ∂-sound (p₂ _) z∈p₂′y
∂-sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣ˡ    (x∈p₁′  >>= y∈p₂x))  = [ ○ - ○ ] ∂-sound p₁ x∈p₁′ >>= y∈p₂x
∂-sound (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)        (x∈p₁′  >>= y∈p₂x)   = [ ◌ - ◌ ] ∂-sound (♭ p₁) x∈p₁′ >>= y∈p₂x
∂-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y)) with Return⋆.sound xs y∈ret⋆
∂-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣ʳ ._ (y∈ret⋆ >>= z∈p₂′y)) | (refl , y∈xs) =
                                                                                 [ ◌ - ○ ] I.sound (♭ p₁) y∈xs >>= ∂-sound (p₂ _) z∈p₂′y
∂-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣ˡ    (x∈p₁′  >>= y∈p₂x))  = [ ◌ - ○ ] ∂-sound (♭ p₁) x∈p₁′ >>= y∈p₂x
∂-sound (nonempty p) x∈p = nonempty (∂-sound p x∈p)
∂-sound (cast _ p)   x∈p = cast (∂-sound p x∈p)

∂-sound (return _) ()
∂-sound fail       ()

sound : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
        x ∈ parseComplete p s → x ∈ p · s
sound []      x∈p = I.sound _ x∈p
sound (t ∷ s) x∈p = ∂-sound _ (sound s x∈p)

------------------------------------------------------------------------
-- Completeness

mutual

  ∂-complete : ∀ {Tok R xs x s t} {p : Parser Tok R xs} →
               x ∈ p · t ∷ s → x ∈ ∂ p t · s
  ∂-complete x∈p = ∂-complete′ _ x∈p refl

  ∂-complete′ : ∀ {Tok R xs x s s′ t} (p : Parser Tok R xs) →
                x ∈ p · s′ → s′ ≡ t ∷ s → x ∈ ∂ p t · s
  ∂-complete′ token     token       refl = return

  ∂-complete′ (p₁ ∣ p₂) (∣ˡ   x∈p₁) refl = ∣ˡ                  (∂-complete x∈p₁)
  ∂-complete′ (p₁ ∣ p₂) (∣ʳ _ x∈p₂) refl = ∣ʳ (∂-initial p₁ _) (∂-complete x∈p₂)

  ∂-complete′ (f <$> p) (<$> x∈p)   refl = <$> ∂-complete x∈p

  ∂-complete′ (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     _⊛_ {fs = ○} {xs = ○}  (∂-complete f∈p₁) x∈p₂
  ∂-complete′ (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (_⊛_ {fs = ○} {xs = ○}  (∂-complete f∈p₁) x∈p₂)
  ∂-complete′ (_⊛_ {fs = just _}  {xs = just xs} p₁ p₂)
              (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣ʳ (∂-initial p₁ _ ⊛′ xs)
                                                     (_⊛_ {fs = ○} {xs = ○}
                                                          (Return⋆.complete (I.complete f∈p₁)) (∂-complete x∈p₂))
  ∂-complete′ (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     _⊛_ {fs = ○} {xs = ◌} (∂-complete f∈p₁) x∈p₂
  ∂-complete′ (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (_⊛_ {fs = ○} {xs = ◌} (∂-complete f∈p₁) x∈p₂)
  ∂-complete′ (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂)
              (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣ʳ []
                                                     (_⊛_ {fs = ○} {xs = ○}
                                                          (Return⋆.complete (I.complete f∈p₁)) (∂-complete x∈p₂))

  ∂-complete′ (_>>=_ {xs = nothing} {f = just _}  p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     _>>=_ {xs = ○} {f = ○} (∂-complete x∈p₁) y∈p₂x
  ∂-complete′ (_>>=_ {xs = just _}  {f = just _}  p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (_>>=_ {xs = ○} {f = ○} (∂-complete x∈p₁) y∈p₂x)
  ∂-complete′ (_>>=_ {xs = just _}  {f = just f}  p₁ p₂)
              (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ (∂-initial p₁ _ >>=′ f)
                                                        (_>>=_ {xs = ○} {f = ○}
                                                               (Return⋆.complete (I.complete x∈p₁)) (∂-complete y∈p₂x))

  ∂-complete′ (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     _>>=_ {xs = ○} {f = ◌} (∂-complete x∈p₁) y∈p₂x
  ∂-complete′ (_>>=_ {xs = just _}  {f = nothing} p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (_>>=_ {xs = ○} {f = ◌} (∂-complete x∈p₁) y∈p₂x)
  ∂-complete′ (_>>=_ {xs = just _}  {f = nothing} p₁ p₂)
              (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ []
                                                        (_>>=_ {xs = ○} {f = ○}
                                                               (Return⋆.complete (I.complete x∈p₁)) (∂-complete y∈p₂x))

  ∂-complete′ (nonempty p) (nonempty x∈p) refl = ∂-complete x∈p

  ∂-complete′ (cast _ p) (cast x∈p) refl = ∂-complete x∈p

  ∂-complete′ (return _) () refl
  ∂-complete′ fail       () refl
  ∂-complete′ (_⊛_   {fs = nothing} _ _) (_⊛_   {s₁ = []} f∈p₁ _) _ with I.complete f∈p₁
  ... | ()
  ∂-complete′ (_>>=_ {xs = nothing} _ _) (_>>=_ {s₁ = []} x∈p₁ _) _ with I.complete x∈p₁
  ... | ()

complete : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
           x ∈ p · s → x ∈ parseComplete p s
complete []      x∈p = I.complete x∈p
complete (t ∷ s) x∈p = complete s (∂-complete x∈p)
