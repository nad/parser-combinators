------------------------------------------------------------------------
-- Correctness
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Correct where

open import Category.Monad
open import Coinduction
open import Function
open import Data.List as List
open import Data.List.Any as Any
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡
open RawMonad List.monad using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.Applicative
open import TotalParserCombinators.Lib
open import TotalParserCombinators.BreadthFirst.Derivative
open import TotalParserCombinators.Coinduction
import TotalParserCombinators.InitialSet as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- Soundness

mutual

  ∂-sound : ∀ {Tok R xs x s} {t} (p : Parser Tok R xs) →
            x ∈ ∂ p t · s → x ∈ p · t ∷ s
  ∂-sound token                      return                    = token
  ∂-sound (p₁ ∣ p₂)                  (∣ˡ    x∈p₁)              = ∣ˡ     (∂-sound p₁ x∈p₁)
  ∂-sound (_∣_ {xs₁ = xs₁} p₁ p₂)    (∣ʳ ._ x∈p₂)              = ∣ʳ xs₁ (∂-sound p₂ x∈p₂)
  ∂-sound (f <$> p)                  (<$> x∈p)                 = <$> ∂-sound p x∈p
  ∂-sound (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)                 (f∈p₁′   ⊛ x∈p₂)   = ∂-sound p₁ f∈p₁′ ⊛
                                                                 cast∈ refl (♭?♯? (∂-initial p₁ _)) refl x∈p₂
  ∂-sound (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)                 (f∈p₁′   ⊛ x∈p₂)   = ∂-sound (♭ p₁) f∈p₁′ ⊛
                                                                 cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl x∈p₂
  ∂-sound (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)          (∣ˡ    (f∈p₁′   ⊛ x∈p₂))  = ∂-sound p₁ f∈p₁′ ⊛
                                                                 cast∈ refl (♭?♯? (∂-initial p₁ _)) refl x∈p₂
  ∂-sound (⟨ p₁ ⟩ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) with ⋁.sound return (f ∷ fs)
                                                                            (cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs)
  ∂-sound (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)          (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) | (f′ , f′∈f∷fs , return) =
                                                                 I.sound p₁ f′∈f∷fs ⊛ ∂-sound p₂ x∈p₂′
  ∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)          (∣ˡ    (f∈p₁′   ⊛ x∈p₂))  = ∂-sound (♭ p₁) f∈p₁′ ⊛
                                                                 cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl x∈p₂
  ∂-sound (⟪ p₁ ⟫ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) with ⋁.sound return (f ∷ fs)
                                                                            (cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs)
  ∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)          (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) | (f′ , f′∈f∷fs , return) =
                                                                 I.sound (♭ p₁) f′∈f∷fs ⊛ ∂-sound p₂ x∈p₂′
  ∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ z∈p₂′x)          with ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
  ∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ z∈p₂′x)          | (y , y∈x∷xs , z∈p₂′y) =
                                                                 _>>=_ {p₂ = p₂} (I.sound p₁ y∈x∷xs) z∈p₂′y
  ∂-sound (_>>=_  {xs = x ∷ xs} p₁ p₂) (∣ˡ (x∈p₁′ >>=  y∈p₂x)) = _>>=_ {p₂ = p₂} (∂-sound p₁ x∈p₁′)
                                                                                 (cast∈ refl (♭?♯? (∂-initial p₁ _)) refl y∈p₂x)
  ∂-sound (_>>=_  {xs = []}     p₁ p₂)     (x∈p₁′ >>=  y∈p₂x)  = ∂-sound p₁ x∈p₁′ >>=
                                                                 cast∈ refl (♭?♯? (∂-initial p₁ _)) refl y∈p₂x
  ∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ z∈p₂′x)          with ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
  ∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ʳ ._ z∈p₂′x)          | (y , y∈x∷xs , z∈p₂′y) =
                                                                 _>>=!_ {p₂ = p₂} (I.sound (♭ p₁) y∈x∷xs) z∈p₂′y
  ∂-sound (_>>=!_ {xs = x ∷ xs} p₁ p₂) (∣ˡ (x∈p₁′ >>=! y∈p₂x)) = _>>=!_ {p₂ = p₂} (∂-sound (♭ p₁) x∈p₁′)
                                                                                  (cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl y∈p₂x)
  ∂-sound (_>>=!_ {xs = []}     p₁ p₂)     (x∈p₁′ >>=! y∈p₂x)  = ∂-sound (♭ p₁) x∈p₁′ >>=!
                                                                 cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl y∈p₂x
  ∂-sound (nonempty p)                x∈p                      = nonempty (∂-sound p x∈p)
  ∂-sound (cast _ p)                  x∈p                      = cast (∂-sound p x∈p)

  ∂-sound (return _) ()
  ∂-sound fail       ()

  ∂-⋁-sound : ∀ {Tok R₁ R₂ t z s y} {ys : List R₁} {f : R₁ → List R₂}
              xs (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys)) →
              z ∈ ∂-⋁ xs p t · s →
              ∃ λ x → (x ∈ xs) × (z ∈ ♭? (p x) · t ∷ s)
  ∂-⋁-sound []       p ()
  ∂-⋁-sound (x ∷ xs) p (∣ˡ    z∈p₂′x)  = (x , here refl , ∂!-sound (p x) z∈p₂′x)
  ∂-⋁-sound (x ∷ xs) p (∣ʳ ._ z∈p₂′xs) =
    Prod.map id (Prod.map there (λ z∈ → z∈))
      (∂-⋁-sound xs p z∈p₂′xs)

  ∂!-sound : ∀ {Tok R₁ R₂ z t s xs y} {ys : List R₁}
             (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) →
             z ∈ ∂! p t · s → z ∈ ♭? p · t ∷ s
  ∂!-sound ⟨ p ⟩ z∈p′ = ∂-sound p z∈p′

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

  ∂-complete′ (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     ∂-complete f∈p₁ ⊛
                                                      cast∈ refl (sym (♭?♯? (∂-initial p₁ _))) refl x∈p₂
  ∂-complete′ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     ∂-complete f∈p₁ ⊛
                                                      cast∈ refl (sym (♭?♯? (∂-initial (♭ p₁) _))) refl x∈p₂
  ∂-complete′ (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (∂-complete f∈p₁ ⊛
                                                      cast∈ refl (sym (♭?♯? (∂-initial p₁ _))) refl x∈p₂)
  ∂-complete′ (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟨ p₂ ⟩)
              (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣ʳ (∂-initial p₁ _ ⊛′ (x ∷ xs))
                                                     (cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                                        (⋁.complete return (I.complete f∈p₁) return) ⊛
                                                      ∂-complete x∈p₂)
  ∂-complete′ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)
              (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (∂-complete f∈p₁ ⊛
                                                      cast∈ refl (sym (♭?♯? (∂-initial (♭ p₁) _))) refl x∈p₂)
  ∂-complete′ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)
              (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣ʳ []
                                                     (cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                                        (⋁.complete return (I.complete f∈p₁) return) ⊛
                                                      ∂-complete x∈p₂)

  ∂-complete′ (_>>=_ {xs = x ∷ xs} {f} p₁ p₂)
              (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ (∂-initial p₁ _ >>=′ f)
                                                        (∂-⋁-complete p₂ (I.complete x∈p₁) y∈p₂x)
  ∂-complete′ (_>>=_ {xs = x ∷ xs}     p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (∂-complete x∈p₁ >>=
                                                         cast∈ refl (sym (♭?♯? (∂-initial p₁ _))) refl
                                                           y∈p₂x)
  ∂-complete′ (_>>=_ {R₁} {xs = []}    p₁ p₂)
              (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     ∂-complete x∈p₁ >>=
                                                         cast∈ refl (sym (♭?♯? (∂-initial p₁ _))) refl
                                                           y∈p₂x

  ∂-complete′ (_>>=!_ {xs = x ∷ xs} p₁ p₂)
              (_>>=!_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ []
                                                         (∂-⋁-complete p₂ (I.complete x∈p₁) y∈p₂x)
  ∂-complete′ (_>>=!_ {xs = x ∷ xs}     p₁ p₂)
              (_>>=!_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (∂-complete x∈p₁ >>=!
                                                          cast∈ refl (sym (♭?♯? (∂-initial (♭ p₁) _))) refl
                                                            y∈p₂x)
  ∂-complete′ (_>>=!_ {R₁} {xs = []}    p₁ p₂)
              (_>>=!_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     ∂-complete x∈p₁ >>=!
                                                          cast∈ refl (sym (♭?♯? (∂-initial (♭ p₁) _))) refl
                                                            y∈p₂x

  ∂-complete′ (nonempty p) (nonempty x∈p) refl = ∂-complete x∈p

  ∂-complete′ (cast _ p) (cast x∈p) refl = ∂-complete x∈p

  ∂-complete′ (return _) () refl
  ∂-complete′ fail       () refl
  ∂-complete′ (_ ⊛ ⟪ _ ⟫)            (_⊛_    {s₁ = []} f∈p₁ _) _ with I.complete f∈p₁
  ... | ()
  ∂-complete′ (_>>=_  {xs = []} _ _) (_>>=_  {s₁ = []} x∈p₁ _) _ with I.complete x∈p₁
  ... | ()
  ∂-complete′ (_>>=!_ {xs = []} _ _) (_>>=!_ {s₁ = []} x∈p₁ _) _ with I.complete x∈p₁
  ... | ()

  ∂-⋁-complete : ∀ {Tok R₁ R₂ x t z s xs y} {ys : List R₁}
                   {f : R₁ → List R₂}
                 (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys)) →
                 x ∈ xs → z ∈ ♭? (p x) · t ∷ s → z ∈ ∂-⋁ xs p t · s
  ∂-⋁-complete p (here refl)  y∈px = ∣ˡ (∂!-complete (p _) y∈px)
  ∂-⋁-complete p (there x∈xs) y∈px =
    ∣ʳ (∂!-initial (p _) _) (∂-⋁-complete p x∈xs y∈px)

  ∂!-complete : ∀ {Tok R₁ R₂ z t s xs y} {ys : List R₁}
                (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) →
                z ∈ ♭? p · t ∷ s → z ∈ ∂! p t · s
  ∂!-complete ⟨ p ⟩ z∈p = ∂-complete z∈p

complete : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
           x ∈ p · s → x ∈ parseComplete p s
complete []      x∈p = I.complete x∈p
complete (t ∷ s) x∈p = complete s (∂-complete x∈p)
