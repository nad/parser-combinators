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

D-sound : ∀ {Tok R xs x s} {t} (p : Parser Tok R xs) →
          x ∈ D t p · s → x ∈ p · t ∷ s
D-sound token                   return            = token
D-sound (p₁ ∣ p₂)               (∣-left     x∈p₁) = ∣-left      (D-sound p₁ x∈p₁)
D-sound (_∣_ {xs₁ = xs₁} p₁ p₂) (∣-right ._ x∈p₂) = ∣-right xs₁ (D-sound p₂ x∈p₂)
D-sound (f <$> p)               (<$> x∈p)         = <$> D-sound p x∈p
D-sound (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)             (f∈p₁′  ⊛ x∈p₂)       = [ ○ - ◌ ] D-sound p₁ f∈p₁′ ⊛ x∈p₂
D-sound (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂) (∣-left     (f∈p₁′  ⊛ x∈p₂))      = [ ○ - ○ ] D-sound p₁ f∈p₁′ ⊛ x∈p₂
D-sound (_⊛_ {fs = just fs} {xs = just _}  p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     with Return⋆.sound fs f∈ret⋆
D-sound (_⊛_ {fs = just fs} {xs = just _}  p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     | (refl , f∈fs) =
                                                                                      [ ○ - ○ ] I.sound p₁ f∈fs ⊛ D-sound p₂ x∈p₂′
D-sound (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)             (f∈p₁′  ⊛ x∈p₂)       = [ ◌ - ◌ ] D-sound (♭ p₁) f∈p₁′ ⊛ x∈p₂
D-sound (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂) (∣-left     (f∈p₁′  ⊛ x∈p₂))      = [ ◌ - ○ ] D-sound (♭ p₁) f∈p₁′ ⊛ x∈p₂
D-sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     with Return⋆.sound fs f∈ret⋆
D-sound (_⊛_ {fs = just fs} {xs = nothing} p₁ p₂) (∣-right ._ (f∈ret⋆ ⊛ x∈p₂′))     | (refl , f∈fs) =
                                                                                      [ ◌ - ○ ] I.sound (♭ p₁) f∈fs ⊛ D-sound p₂ x∈p₂′
D-sound (_>>=_ {xs = nothing} {f = just _}  p₁ p₂)             (x∈p₁′  >>= y∈p₂x)   = [ ○ - ◌ ] D-sound p₁ x∈p₁′ >>= y∈p₂x
D-sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) with Return⋆.sound xs y∈ret⋆
D-sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) | (refl , y∈xs) =
                                                                                      [ ○ - ○ ] I.sound p₁ y∈xs >>= D-sound (p₂ _) z∈p₂′y
D-sound (_>>=_ {xs = just xs} {f = just _}  p₁ p₂) (∣-left     (x∈p₁′  >>= y∈p₂x))  = [ ○ - ○ ] D-sound p₁ x∈p₁′ >>= y∈p₂x
D-sound (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)             (x∈p₁′  >>= y∈p₂x)   = [ ◌ - ◌ ] D-sound (♭ p₁) x∈p₁′ >>= y∈p₂x
D-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) with Return⋆.sound xs y∈ret⋆
D-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣-right ._ (y∈ret⋆ >>= z∈p₂′y)) | (refl , y∈xs) =
                                                                                      [ ◌ - ○ ] I.sound (♭ p₁) y∈xs >>=
                                                                                                D-sound (p₂ _) z∈p₂′y
D-sound (_>>=_ {xs = just xs} {f = nothing} p₁ p₂) (∣-left     (x∈p₁′  >>= y∈p₂x))  = [ ◌ - ○ ] D-sound (♭ p₁) x∈p₁′ >>= y∈p₂x
D-sound (nonempty p) x∈p = nonempty (D-sound p x∈p)
D-sound (cast _ p)   x∈p = cast (D-sound p x∈p)

D-sound (return _) ()
D-sound fail       ()

sound : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
        x ∈ parse p s → x ∈ p · s
sound []      x∈p = I.sound _ x∈p
sound (t ∷ s) x∈p = D-sound _ (sound s x∈p)

------------------------------------------------------------------------
-- Completeness

mutual

  D-complete : ∀ {Tok R xs x s t} {p : Parser Tok R xs} →
               x ∈ p · t ∷ s → x ∈ D t p · s
  D-complete x∈p = D-complete′ _ x∈p refl

  D-complete′ : ∀ {Tok R xs x s s′ t} (p : Parser Tok R xs) →
                x ∈ p · s′ → s′ ≡ t ∷ s → x ∈ D t p · s
  D-complete′ token     token       refl = return

  D-complete′ (p₁ ∣ p₂) (∣-left    x∈p₁) refl = ∣-left               (D-complete x∈p₁)
  D-complete′ (p₁ ∣ p₂) (∣-right _ x∈p₂) refl = ∣-right (D-bag _ p₁) (D-complete x∈p₂)

  D-complete′ (f <$> p) (<$> x∈p)   refl = <$> D-complete x∈p

  D-complete′ (_⊛_ {fs = nothing} {xs = just _}  p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     _⊛_ {fs = ○} {xs = ○}  (D-complete f∈p₁) x∈p₂
  D-complete′ (_⊛_ {fs = just _}  {xs = just _}  p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣-left (_⊛_ {fs = ○} {xs = ○}  (D-complete f∈p₁) x∈p₂)
  D-complete′ (_⊛_ {fs = just _}  {xs = just xs} p₁ p₂)
              (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣-right (D-bag _ p₁ ⊛′ xs)
                                                     (_⊛_ {fs = ○} {xs = ○}
                                                          (Return⋆.complete (I.complete f∈p₁)) (D-complete x∈p₂))
  D-complete′ (_⊛_ {fs = nothing} {xs = nothing} p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     _⊛_ {fs = ○} {xs = ◌} (D-complete f∈p₁) x∈p₂
  D-complete′ (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣-left (_⊛_ {fs = ○} {xs = ◌} (D-complete f∈p₁) x∈p₂)
  D-complete′ (_⊛_ {fs = just _}  {xs = nothing} p₁ p₂)
              (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣-right []
                                                     (_⊛_ {fs = ○} {xs = ○}
                                                          (Return⋆.complete (I.complete f∈p₁)) (D-complete x∈p₂))

  D-complete′ (_>>=_ {xs = nothing} {f = just _}  p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     _>>=_ {xs = ○} {f = ○} (D-complete x∈p₁) y∈p₂x
  D-complete′ (_>>=_ {xs = just _}  {f = just _}  p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣-left (_>>=_ {xs = ○} {f = ○} (D-complete x∈p₁) y∈p₂x)
  D-complete′ (_>>=_ {xs = just _}  {f = just f}  p₁ p₂)
              (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣-right (D-bag _ p₁ >>=′ f)
                                                        (_>>=_ {xs = ○} {f = ○}
                                                               (Return⋆.complete (I.complete x∈p₁)) (D-complete y∈p₂x))

  D-complete′ (_>>=_ {xs = nothing} {f = nothing} p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     _>>=_ {xs = ○} {f = ◌} (D-complete x∈p₁) y∈p₂x
  D-complete′ (_>>=_ {xs = just _}  {f = nothing} p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣-left (_>>=_ {xs = ○} {f = ◌} (D-complete x∈p₁) y∈p₂x)
  D-complete′ (_>>=_ {xs = just _}  {f = nothing} p₁ p₂)
              (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣-right []
                                                        (_>>=_ {xs = ○} {f = ○}
                                                               (Return⋆.complete (I.complete x∈p₁)) (D-complete y∈p₂x))

  D-complete′ (nonempty p) (nonempty x∈p) refl = D-complete x∈p

  D-complete′ (cast _ p) (cast x∈p) refl = D-complete x∈p

  D-complete′ (return _) () refl
  D-complete′ fail       () refl
  D-complete′ (_⊛_   {fs = nothing} _ _) (_⊛_   {s₁ = []} f∈p₁ _) _ with I.complete f∈p₁
  ... | ()
  D-complete′ (_>>=_ {xs = nothing} _ _) (_>>=_ {s₁ = []} x∈p₁ _) _ with I.complete x∈p₁
  ... | ()

complete : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
           x ∈ p · s → x ∈ parse p s
complete []      x∈p = I.complete x∈p
complete (t ∷ s) x∈p = complete s (D-complete x∈p)
