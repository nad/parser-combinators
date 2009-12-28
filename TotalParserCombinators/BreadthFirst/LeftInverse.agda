------------------------------------------------------------------------
-- The backend does not introduce any unneeded ambiguity
------------------------------------------------------------------------

-- This module contains a proof showing that
-- TotalParserCombinators.BreadthFirst.complete is a left inverse of
-- TotalParserCombinators.BreadthFirst.sound. This implies that the
-- (finite) type x ∈ parseComplete p s contains at most as many proofs
-- as x ∈ p · s. In other words, the output of parseComplete p s can
-- only contain n copies of x if there are at least n distinct parse
-- trees in x ∈ p · s.

module TotalParserCombinators.BreadthFirst.LeftInverse where

open import Category.Monad
open import Coinduction
open import Data.Function
open import Data.List as List hiding ([_])
open import Data.List.Any as Any
open import Data.List.Any.Properties as AnyProp
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡
open AnyProp.Membership-≡
private
  open RawMonad List.monad using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.Applicative
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
  hiding (sound; complete)

i-complete∘i-sound : ∀ {Tok R xs x}
                     (p : Parser Tok R xs) (x∈p : x ∈ xs) →
                     initial-complete (initial-sound p x∈p) ≡ x∈p
i-complete∘i-sound (return x)              (here refl)       = refl
i-complete∘i-sound (_∣_ {xs₁ = xs₁} p₁ p₂) x∈xs              with ++⁻ xs₁ x∈xs | ++⁺∘++⁻ xs₁ x∈xs
i-complete∘i-sound (_∣_ {xs₁ = xs₁} p₁ p₂) .(++⁺ˡ     x∈xs₁) | inj₁ x∈xs₁ | refl = cong ++⁺ˡ       $ i-complete∘i-sound p₁ x∈xs₁
i-complete∘i-sound (_∣_ {xs₁ = xs₁} p₁ p₂) .(++⁺ʳ xs₁ x∈xs₂) | inj₂ x∈xs₂ | refl = cong (++⁺ʳ xs₁) $ i-complete∘i-sound p₂ x∈xs₂
i-complete∘i-sound (_<$>_ {xs = xs} f p)   x∈xs              with map-∈⁻ xs x∈xs | map-∈⁺∘map-∈⁻ x∈xs
i-complete∘i-sound (_<$>_ {xs = xs} f p)   .(map-∈⁺ y∈xs)    | (y , y∈xs , refl) | refl = cong map-∈⁺ $ i-complete∘i-sound p y∈xs
i-complete∘i-sound (_⊛_ {fs = fs} {x ∷ xs} ⟨ p₁ ⟩ p₂) y∈ys with ⊛′-∈⁻ fs (x ∷ xs) y∈ys | ⊛′-∈⁺∘⊛′-∈⁻ fs (x ∷ xs) y∈ys
i-complete∘i-sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟪ p₂ ⟫) y∈ys                   | (f′ , x′ , ()    , x′∈x∷xs , refl) | _
i-complete∘i-sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟨ p₂ ⟩) .(⊛′-∈⁺ f′∈fs x′∈x∷xs) | (f′ , x′ , f′∈fs , x′∈x∷xs , refl) | refl =
  cong₂ ⊛′-∈⁺ (i-complete∘i-sound p₁ f′∈fs) (i-complete∘i-sound p₂ x′∈x∷xs)
i-complete∘i-sound (_>>=_ {xs = zs}     {f} p₁ p₂) y∈ys                    with >>=-∈⁻ f zs y∈ys | >>=-∈⁺∘>>=-∈⁻ f zs y∈ys
i-complete∘i-sound (_>>=_ {xs = []}     {f} p₁ p₂) ._                      | (x , ()     , y∈fx) | refl
i-complete∘i-sound (_>>=_ {xs = z ∷ zs} {f} p₁ p₂) .(>>=-∈⁺ f x∈z∷zs y∈fx) | (x , x∈z∷zs , y∈fx) | refl =
  cong₂ (>>=-∈⁺ f) (i-complete∘i-sound p₁ x∈z∷zs) (helper (p₂ x) x∈z∷zs y∈fx)
  where
  helper : ∀ {Tok R₁ R₂ x y xs z} {zs : List R₁}
           (p : ∞? (Parser Tok R₂ xs) (z ∷ zs))
           (x∈z∷zs : x ∈ z ∷ zs) (y∈xs : y ∈ xs) →
           initial-complete (initial-sound′ p x∈z∷zs y∈xs) ≡ y∈xs
  helper ⟨ p ⟩ x∈z∷zs y∈xs = i-complete∘i-sound p y∈xs
i-complete∘i-sound (cast refl p) x∈xs = i-complete∘i-sound p x∈xs

i-complete∘i-sound (return _)   (there ())
i-complete∘i-sound fail         ()
i-complete∘i-sound token        ()
i-complete∘i-sound (⟪ _ ⟫ ⊛ _)  ()
i-complete∘i-sound (_ >>=! _)   ()
i-complete∘i-sound (nonempty _) ()

⋁-complete∘⋁-sound : ∀ {Tok R₁ R₂ y s} {i : R₁ → List R₂} →
                     (f : (x : R₁) → Parser Tok R₂ (i x)) (xs : List R₁)
                     (y∈⋁fxs : y ∈ ⋁ f xs · s) →
                     let p = proj₂ $ ⋁-sound f xs y∈⋁fxs in
                     ⋁-complete f (proj₁ p) (proj₂ p) ≡ y∈⋁fxs
⋁-complete∘⋁-sound         f []       ()
⋁-complete∘⋁-sound         f (x ∷ xs) (∣ˡ    y∈fx)   = refl
⋁-complete∘⋁-sound {i = i} f (x ∷ xs) (∣ʳ ._ y∈⋁fxs) =
  cong (∣ʳ (i x)) (⋁-complete∘⋁-sound f xs y∈⋁fxs)

cast∈∘cast∈ : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′}
              (x≡x′ : x ≡ x′) (p≡p′ : p ≡ p′) (s≡s′ : s ≡ s′)
              (x∈p : x ∈ p · s) →
              cast∈ (sym x≡x′) (sym p≡p′) (sym s≡s′)
                    (cast∈ x≡x′ p≡p′ s≡s′ x∈p) ≡ x∈p
cast∈∘cast∈ refl refl refl _ = refl

mutual

  ∂-complete∘∂-sound : ∀ {Tok R xs x s}
                       (p : Parser Tok R xs) {t} (x∈ : x ∈ ∂ p t · s) →
                       ∂-complete (∂-sound p x∈) ≡ x∈
  ∂-complete∘∂-sound token                      return                    = refl
  ∂-complete∘∂-sound (p₁ ∣ p₂)                  (∣ˡ    x∈p₁)              = cong ∣ˡ $ ∂-complete∘∂-sound p₁ x∈p₁
  ∂-complete∘∂-sound (p₁ ∣ p₂)                  (∣ʳ ._ x∈p₂)              = cong (∣ʳ (∂-initial p₁ _)) $ ∂-complete∘∂-sound p₂ x∈p₂
  ∂-complete∘∂-sound (f <$> p)                  (<$> x∈p)                 = cong <$>_ $ ∂-complete∘∂-sound p  x∈p
  ∂-complete∘∂-sound (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)                 (f∈p₁′   ⊛ x∈p₂)   = cong₂ _⊛_ (∂-complete∘∂-sound p₁ f∈p₁′)
                                                                                      (cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)                 (f∈p₁′   ⊛ x∈p₂)   = cong₂ _⊛_
                                                                                  (∂-complete∘∂-sound (♭ p₁) f∈p₁′)
                                                                                  (cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)          (∣ˡ    (f∈p₁′   ⊛ x∈p₂))  = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ ⊛ pr₂))
                                                                                  (∂-complete∘∂-sound p₁ f∈p₁′)
                                                                                  (cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟨ p₁ ⟩ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′))
    with                                    f∈⋁f∷fs′
       | cast∈∘cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs
       |            ⋁-sound return (f ∷ fs) f∈⋁f∷fs′
       | ⋁-complete∘⋁-sound return (f ∷ fs) f∈⋁f∷fs′
    where f∈⋁f∷fs′ = cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs
  ∂-complete∘∂-sound (⟨_⟩ {x} {xs} p₁ ⊛ ⟨ p₂ ⟩)
                     (∣ʳ ._ (.(cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                     (⋁-complete return f′∈f∷fs return)) ⊛ x∈p₂′))
    | ._ | refl | (f′ , f′∈f∷fs , return) | refl = cong₂ (λ pr₁ pr₂ → ∣ʳ (∂-initial p₁ _ ⊛′ (x ∷ xs))
                                                                         (cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                                                                (⋁-complete return pr₁ return) ⊛ pr₂))
                                                         (i-complete∘i-sound p₁ f′∈f∷fs)
                                                         (∂-complete∘∂-sound p₂ x∈p₂′)
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)          (∣ˡ    (f∈p₁′   ⊛ x∈p₂))  = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ ⊛ pr₂))
                                                                                  (∂-complete∘∂-sound (♭ p₁) f∈p₁′)
                                                                                  (cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl x∈p₂)
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′))
    with                                    f∈⋁f∷fs′
       | cast∈∘cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs
       |            ⋁-sound return (f ∷ fs) f∈⋁f∷fs′
       | ⋁-complete∘⋁-sound return (f ∷ fs) f∈⋁f∷fs′
    where f∈⋁f∷fs′ = cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs
  ∂-complete∘∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)
                     (∣ʳ ._ (.(cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                     (⋁-complete return f′∈f∷fs return)) ⊛ x∈p₂′))
    | ._ | refl | (f′ , f′∈f∷fs , return) | refl = cong₂ (λ pr₁ pr₂ → ∣ʳ []
                                                                         (cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                                                                (⋁-complete return pr₁ return) ⊛ pr₂))
                                                         (i-complete∘i-sound (♭ p₁) f′∈f∷fs)
                                                         (∂-complete∘∂-sound p₂ x∈p₂′)
  ∂-complete∘∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ z∈p₂′x)
    with              ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
       | ∂-⋁-complete∘∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
  ∂-complete∘∂-sound (_>>=_ {xs = _ ∷ _} p₁ p₂) (∣ʳ ._ .(∂-⋁-complete p₂ y∈x∷xs z∈p₂′y))
    | (y , y∈x∷xs , z∈p₂′y) | refl =
    cong (λ pr → ∣ʳ (∂-initial p₁ _ >>=′ _) (∂-⋁-complete p₂ pr z∈p₂′y))
         (i-complete∘i-sound p₁ y∈x∷xs)
  ∂-complete∘∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ˡ (x∈p₁′ >>=  y∈p₂x)) = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ >>= pr₂))
                                                                                  (∂-complete∘∂-sound p₁ x∈p₁′)
                                                                                  (cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ _)) refl y∈p₂x)
  ∂-complete∘∂-sound (_>>=_  {xs = []}     p₁ p₂)     (x∈p₁′ >>=  y∈p₂x)  = cong₂ _>>=_
                                                                                  (∂-complete∘∂-sound p₁ x∈p₁′)
                                                                                  (cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ _)) refl y∈p₂x)
  ∂-complete∘∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ z∈p₂′x)
    with              ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
       | ∂-⋁-complete∘∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
  ∂-complete∘∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ .(∂-⋁-complete p₂ y∈x∷xs z∈p₂′y))
    | (y , y∈x∷xs , z∈p₂′y) | refl =
    cong (λ pr → ∣ʳ [] (∂-⋁-complete p₂ pr z∈p₂′y))
         (i-complete∘i-sound (♭ p₁) y∈x∷xs)
  ∂-complete∘∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ˡ (x∈p₁′ >>=! y∈p₂x)) = cong₂ (λ pr₁ pr₂ → ∣ˡ (pr₁ >>=! pr₂))
                                                                                  (∂-complete∘∂-sound (♭ p₁) x∈p₁′)
                                                                                  (cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl y∈p₂x)
  ∂-complete∘∂-sound (_>>=!_ {xs = []}     p₁ p₂)     (x∈p₁′ >>=! y∈p₂x)  = cong₂ _>>=!_
                                                                                  (∂-complete∘∂-sound (♭ p₁) x∈p₁′)
                                                                                  (cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl y∈p₂x)
  ∂-complete∘∂-sound (nonempty p)                 x∈p                     = ∂-complete∘∂-sound p x∈p
  ∂-complete∘∂-sound (cast _ p)                   x∈p                     = ∂-complete∘∂-sound p x∈p

  ∂-complete∘∂-sound (return _) ()
  ∂-complete∘∂-sound fail       ()

  ∂-⋁-complete∘∂-⋁-sound : ∀ {Tok R₁ R₂ t z s y} {ys : List R₁} {f : R₁ → List R₂}
                           xs (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys))
                           (z∈p′ : z ∈ ∂-⋁ xs p t · s) →
                           let p′ = proj₂ $ ∂-⋁-sound xs p z∈p′ in
                           ∂-⋁-complete p (proj₁ p′) (proj₂ p′) ≡ z∈p′
  ∂-⋁-complete∘∂-⋁-sound []       p ()
  ∂-⋁-complete∘∂-⋁-sound (x ∷ xs) p (∣ˡ    z∈p₂′x)  = cong ∣ˡ $ ∂!-complete∘∂!-sound (p x) z∈p₂′x
  ∂-⋁-complete∘∂-⋁-sound (x ∷ xs) p (∣ʳ ._ z∈p₂′xs) = cong (∣ʳ (∂!-initial (p x) _)) $
                                                           ∂-⋁-complete∘∂-⋁-sound xs p z∈p₂′xs

  ∂!-complete∘∂!-sound : ∀ {Tok R₁ R₂ z t s xs y} {ys : List R₁}
                         (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) →
                         (z∈p′ : z ∈ ∂! p t · s) →
                         ∂!-complete p (∂!-sound p z∈p′) ≡ z∈p′
  ∂!-complete∘∂!-sound ⟨ p ⟩ z∈p′ = ∂-complete∘∂-sound p z∈p′

complete∘sound : ∀ {Tok R xs x} s
                 (p : Parser Tok R xs) (x∈p : x ∈ parseComplete p s) →
                 complete s (sound s x∈p) ≡ x∈p
complete∘sound []      p x∈p = i-complete∘i-sound p x∈p
complete∘sound (t ∷ s) p x∈p rewrite ∂-complete∘∂-sound p (sound s x∈p) =
  complete∘sound s (∂ p t) x∈p
