------------------------------------------------------------------------
-- The backend does not remove any ambiguity
------------------------------------------------------------------------

-- This module contains a proof showing that
-- TotalParserCombinators.BreadthFirst.complete is a right inverse of
-- TotalParserCombinators.BreadthFirst.sound. This implies that the
-- (finite) type x ∈ parseComplete p s contains at least as many
-- proofs as x ∈ p · s. In other words, if the output of
-- parseComplete p s contains n copies of x, then there are at most n
-- distinct parse trees in x ∈ p · s.

module TotalParserCombinators.BreadthFirst.RightInverse where

open import Coinduction
open import Data.Function
open import Data.List
open import Data.List.Any as Any
open import Data.List.Any.Properties as AnyProp
open import Data.Product
open import Data.Sum
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡
open AnyProp.Membership-≡

open import TotalParserCombinators.Applicative
open import TotalParserCombinators.BreadthFirst
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics
  hiding (sound; complete)

i-sound∘i-complete′ : ∀ {Tok R xs x s} {p : Parser Tok R xs}
                      (x∈p : x ∈ p · s) (s≡[] : s ≡ []) →
                      initial-sound p (initial-complete′ x∈p s≡[]) ≅ x∈p
i-sound∘i-complete′ return                            refl = refl
i-sound∘i-complete′ (∣ˡ {xs₁ = xs₁} {xs₂ = xs₂} x∈p₁) refl rewrite ++⁻∘++⁺ xs₁ {ys = xs₂} (inj₁ (initial-complete x∈p₁)) =
                                                           H.cong ((_ → _ ∈ _ · _) ∶ ∣ˡ)     (i-sound∘i-complete′ x∈p₁ refl)
i-sound∘i-complete′ (∣ʳ xs₁ x∈p₂)                     refl rewrite ++⁻∘++⁺ xs₁ (inj₂ (initial-complete x∈p₂)) =
                                                           H.cong ((_ → _ ∈ _ · _) ∶ ∣ʳ xs₁) (i-sound∘i-complete′ x∈p₂ refl)
i-sound∘i-complete′ (<$>_ {f = f} x∈p)                refl rewrite map-∈⁻∘map-∈⁺ f (initial-complete x∈p) =
                                                           H.cong ((_ → _ ∈ _ · _) ∶ <$>_) (i-sound∘i-complete′ x∈p refl)
i-sound∘i-complete′ (_⊛_ {s₁ = []} {fs = fs} {xs = x ∷ xs} {p₁ = ⟨ p₁ ⟩} f∈p₁ x∈p₂) refl
  with initial-complete f∈p₁ | initial-complete x∈p₂
  | ⊛′-∈⁻ fs (x ∷ xs) (⊛′-∈⁺ (initial-complete f∈p₁) (initial-complete x∈p₂))
  | ⊛′-∈⁻∘⊛′-∈⁺ (initial-complete f∈p₁) (initial-complete x∈p₂)
  | i-sound∘i-complete′ f∈p₁ refl | i-sound∘i-complete′ x∈p₂ refl
i-sound∘i-complete′ (_⊛_ {s₁ = []} {fs = []}     {xs = _ ∷ _}  {p₁ = ⟨ _  ⟩} {p₂ = ⟪ _  ⟫} _ _) refl | () | _ | _ | _ | _ | _
i-sound∘i-complete′ (_⊛_ {s₁ = []} {fs = f ∷ fs} {xs = x ∷ xs} {p₁ = ⟨ p₁ ⟩} {p₂ = ⟨ p₂ ⟩}
                         .(initial-sound p₁ ∈f∷fs) .(initial-sound p₂ ∈x∷xs)) refl
  | ∈f∷fs | ∈x∷xs | ._ | refl | refl | refl = refl
i-sound∘i-complete′ (_>>=_ {x = x} {y = y} {s₁ = []} {xs = _ ∷ _} {f} {p₁ = p₁} {p₂ = p₂} x∈p₁ y∈p₂x) refl
  rewrite >>=-∈⁻∘>>=-∈⁺ f (initial-complete x∈p₁) (initial-complete y∈p₂x)
     with initial-sound p₁ (initial-complete x∈p₁)
        | i-sound∘i-complete′ x∈p₁ refl
        | initial-sound′ (p₂ x) (initial-complete x∈p₁) (initial-complete y∈p₂x)
        | helper (p₂ x) (initial-complete x∈p₁) y∈p₂x
     where
     helper : ∀ {Tok R₁ R₂ x y ys} {xs : List R₁}
              (p : ∞? (Parser Tok R₂ ys) xs) →
              (x∈xs : x ∈ xs) (y∈p : y ∈ ♭? p · []) →
              initial-sound′ p x∈xs (initial-complete y∈p) ≅ y∈p
     helper ⟪ p ⟫ () _
     helper ⟨ p ⟩ _  y∈p = i-sound∘i-complete′ y∈p refl
... | ._ | refl | ._ | refl = refl
i-sound∘i-complete′ (cast {eq = refl} x∈p)                     refl with initial-complete x∈p | i-sound∘i-complete′ x∈p refl
i-sound∘i-complete′ (cast {eq = refl} .(initial-sound _ x∈xs)) refl | x∈xs | refl = refl

i-sound∘i-complete′ (_⊛_    {s₁ = []} {xs = []} _    x∈p₂)  refl with initial-complete x∈p₂
... | ()
i-sound∘i-complete′ (_>>=_  {s₁ = []} {xs = []} x∈p₁ y∈p₂x) refl with initial-complete x∈p₁
... | ()
i-sound∘i-complete′ (_>>=!_ {s₁ = []}           x∈p₁ y∈p₂x) refl with initial-complete y∈p₂x
... | ()

i-sound∘i-complete′ token                     ()
i-sound∘i-complete′ (_⊛_    {s₁ = _ ∷ _} _ _) ()
i-sound∘i-complete′ (_>>=_  {s₁ = _ ∷ _} _ _) ()
i-sound∘i-complete′ (_>>=!_ {s₁ = _ ∷ _} _ _) ()
i-sound∘i-complete′ (nonempty _)              ()

i-sound∘i-complete : ∀ {Tok R xs x} {p : Parser Tok R xs}
                     (x∈p : x ∈ p · []) →
                     initial-sound p (initial-complete x∈p) ≡ x∈p
i-sound∘i-complete x∈p = H.≅-to-≡ (i-sound∘i-complete′ x∈p refl)

⋁-sound∘⋁-complete :
  ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
  (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
  (x∈xs : x ∈ xs) (y∈fx : y ∈ f x · s) →
  ⋁-sound f xs (⋁-complete f x∈xs y∈fx) ≡ (x , x∈xs , y∈fx)
⋁-sound∘⋁-complete f (here  refl) y∈fx = refl
⋁-sound∘⋁-complete f (there x∈xs) y∈fx
  rewrite ⋁-sound∘⋁-complete f x∈xs y∈fx = refl

cast∈∘cast∈ : ∀ {Tok R xs} {p p′ : Parser Tok R xs} {x x′ s s′}
              (x≡x′ : x ≡ x′) (p≡p′ : p ≡ p′) (s≡s′ : s ≡ s′)
              (x∈p : x′ ∈ p′ · s′) →
              cast∈ x≡x′ p≡p′ s≡s′
                    (cast∈ (sym x≡x′) (sym p≡p′) (sym s≡s′) x∈p) ≡ x∈p
cast∈∘cast∈ refl refl refl _ = refl

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
          | cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫) (_⊛_ {s₁ = t ∷ _} f∈p₁ x∈p₂) refl
    rewrite ∂-sound∘∂-complete f∈p₁
          | cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩) (_⊛_ {s₁ = t ∷ _} f∈p₁ x∈p₂) refl
    rewrite ∂-sound∘∂-complete f∈p₁
          | cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ {Tok = Tok} {t = t} (_⊛_ {fs = f ∷ fs} {xs = x ∷ xs} ⟨ p₁ ⟩ ⟨ p₂ ⟩) (_⊛_ {s₁ = []} f∈p₁ x∈p₂) refl
    with lhs | lemma
    where
    f∈f∷fs = initial-complete f∈p₁
    c      = ⋁-complete {Tok = Tok} return f∈f∷fs return
    lhs    = ⋁-sound return (f ∷ fs) $
               cast∈ refl (♭?♯? (∂-initial p₂ t)) refl $
                 cast∈ refl (sym (♭?♯? (∂-initial p₂ t))) refl c
    lemma : lhs ≡ (_ , f∈f∷fs , return)
    lemma rewrite cast∈∘cast∈ refl (♭?♯? (∂-initial p₂ t)) refl c =
          ⋁-sound∘⋁-complete return f∈f∷fs return
  ... | .(_ , initial-complete f∈p₁ , return) | refl
    rewrite i-sound∘i-complete f∈p₁ | ∂-sound∘∂-complete x∈p₂ = refl

  ∂-sound∘∂-complete′ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩) (_⊛_ {s₁ = t ∷ _} f∈p₁ x∈p₂) refl
    rewrite ∂-sound∘∂-complete f∈p₁
          | cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) t)) refl x∈p₂ =
    refl

  ∂-sound∘∂-complete′ {Tok = Tok} {t = t} (_⊛_ {fs = f ∷ fs} ⟪ p₁ ⟫ ⟨ p₂ ⟩) (_⊛_ {s₁ = []} f∈p₁ x∈p₂) refl
    with lhs | lemma
    where
    f∈f∷fs = initial-complete f∈p₁
    c      = ⋁-complete {Tok = Tok} return f∈f∷fs return
    lhs    = ⋁-sound return (f ∷ fs) $
               cast∈ refl (♭?♯? (∂-initial p₂ t)) refl $
                 cast∈ refl (sym (♭?♯? (∂-initial p₂ t))) refl c
    lemma : lhs ≡ (_ , f∈f∷fs , return)
    lemma rewrite cast∈∘cast∈ refl (♭?♯? (∂-initial p₂ t)) refl c =
          ⋁-sound∘⋁-complete return f∈f∷fs return
  ... | .(_ , initial-complete f∈p₁ , return) | refl
    rewrite i-sound∘i-complete f∈p₁ | ∂-sound∘∂-complete x∈p₂ = refl

  ∂-sound∘∂-complete′ (_>>=_ {xs = x ∷ xs} {f} p₁ p₂) (_>>=_ {s₁ = []} x∈p₁ y∈p₂x) refl
    rewrite ∂-⋁-sound∘∂-⋁-complete p₂ (initial-complete x∈p₁) y∈p₂x
          | i-sound∘i-complete x∈p₁ =
    refl
  ∂-sound∘∂-complete′ (_>>=_ {xs = x ∷ xs} p₁ p₂) (_>>=_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ t)) refl y∈p₂x =
    refl
  ∂-sound∘∂-complete′ (_>>=_ {R₁} {xs = []} p₁ p₂) (_>>=_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | cast∈∘cast∈ refl (♭?♯? (∂-initial p₁ t)) refl y∈p₂x =
    refl

  ∂-sound∘∂-complete′ (_>>=!_ {xs = x ∷ xs} p₁ p₂) (_>>=!_ {s₁ = []} x∈p₁ y∈p₂x) refl
    rewrite ∂-⋁-sound∘∂-⋁-complete p₂ (initial-complete x∈p₁) y∈p₂x
          | i-sound∘i-complete x∈p₁ =
    refl
  ∂-sound∘∂-complete′ (_>>=!_ {xs = x ∷ xs} p₁ p₂) (_>>=!_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) t)) refl y∈p₂x =
    refl
  ∂-sound∘∂-complete′ (_>>=!_ {R₁} {xs = []} p₁ p₂) (_>>=!_ {s₁ = t ∷ _} x∈p₁ y∈p₂x) refl
    rewrite ∂-sound∘∂-complete x∈p₁
          | cast∈∘cast∈ refl (♭?♯? (∂-initial (♭ p₁) t)) refl y∈p₂x =
    refl

  ∂-sound∘∂-complete′ (nonempty p) (nonempty x∈p) refl rewrite ∂-sound∘∂-complete x∈p = refl

  ∂-sound∘∂-complete′ (cast _ p) (cast x∈p) refl rewrite ∂-sound∘∂-complete x∈p = refl

  ∂-sound∘∂-complete′ (return _) () refl
  ∂-sound∘∂-complete′ fail       () refl
  ∂-sound∘∂-complete′ (_ ⊛ ⟪ _ ⟫)            (_⊛_    {s₁ = []} f∈p₁ _) _ with initial-complete f∈p₁
  ... | ()
  ∂-sound∘∂-complete′ (_>>=_  {xs = []} _ _) (_>>=_  {s₁ = []} x∈p₁ _) _ with initial-complete x∈p₁
  ... | ()
  ∂-sound∘∂-complete′ (_>>=!_ {xs = []} _ _) (_>>=!_ {s₁ = []} x∈p₁ _) _ with initial-complete x∈p₁
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
sound∘complete []      x∈p = i-sound∘i-complete x∈p
sound∘complete (t ∷ s) x∈p
  rewrite sound∘complete s (∂-complete x∈p) = ∂-sound∘∂-complete x∈p
