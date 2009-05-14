------------------------------------------------------------------------
-- A breadth-first backend
------------------------------------------------------------------------

-- Similar to Brzozowski's "Derivatives of Regular Expressions".

-- TODO: Examine if the use of simplification really is an
-- optimisation.

module StructurallyRecursiveDescentParsing.Backend.BreadthFirst where

open import Category.Monad
open import Coinduction
open import Data.Bool
open import Data.Function hiding (_∶_)
open import Data.List as List
open RawMonad List.monad using () renaming (_>>=_ to _>>=′_; return to return′)
open import Data.Product1 as Prod1 renaming (∃₀₁ to ∃; Σ₀₁ to Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality1 as Eq1

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (sound; complete)
open import StructurallyRecursiveDescentParsing.Backend.Simplification
  as Simplification

------------------------------------------------------------------------
-- Parsing

private

  -- Map then choice: y ∈ ⋁ f xs · s  iff  ∃ x ∈ xs. y ∈ f x · s.

  ⋁-initial : ∀ {R₁ R₂} → (R₁ → List R₂) → List R₁ → List R₂
  ⋁-initial e []       = _
  ⋁-initial e (x ∷ xs) = _

  ⋁ : ∀ {Tok R₁ R₂} {f : R₁ → List R₂} →
      ((x : R₁) → Parser Tok R₂ (f x)) → (xs : List R₁) →
      Parser Tok R₂ (⋁-initial f xs)
  ⋁ f []       = fail
  ⋁ f (x ∷ xs) = f x ∣ ⋁ f xs

  -- "Derivative": x ∈ ∂ t p · s  iff  x ∈ p · t ∷ s.

  ∂-initial : ∀ {Tok R xs} → Tok → Parser Tok R xs → List R
  ∂-initial _ (return _)                  = _
  ∂-initial _ fail                        = _
  ∂-initial _ token                       = _
  ∂-initial _ (_ ∣ _)                     = _
  ∂-initial _ (_∶_⊛_ (_ ∷ _) {[]}    _ _) = _
  ∂-initial _ (_∶_⊛_ (_ ∷ _) {_ ∷ _} _ _) = _
  ∂-initial _ (_∶_⊛_ []      {[]}    _ _) = _
  ∂-initial _ (_∶_⊛_ []      {_ ∷ _} _ _) = _
  ∂-initial _ (_>>=_ {xs = x ∷ xs}   _ _) = _
  ∂-initial _ (_>>=_ {xs = []}       _ _) = _
  ∂-initial _ (cast _ _)                  = _

  ∂-⋁-initial : ∀ {Tok R₁ R₂} {f : R₁ → List R₂} →
                Tok → List R₁ → ((x : R₁) → Parser Tok R₂ (f x)) →
                List R₂
  ∂-⋁-initial _ []       _ = []
  ∂-⋁-initial t (x ∷ xs) p = ∂-initial t (p x) ++ ∂-⋁-initial t xs p

  -- Is ∂ t p nullable?

  ∂-∅? : ∀ {Tok R xs} → Tok → Parser Tok R xs → Bool
  ∂-∅? t p = null (∂-initial t p)

  -- Note that this function would not work with the simplified
  -- parsers. The reason is that the analogue of p₁ !>>= p₂ is
  -- sometimes changed to the analogue of p₁′ ?>>= p₂′, where p₂′ is
  -- still dependently typed, and _?>>=_ does not accept dependently
  -- typed arguments.

  mutual

    -- Note: No simplification is currently performed under ♯₁_.

    ∂ : ∀ {Tok R xs}
        (t : Tok) (p : Parser Tok R xs) → Parser Tok R (∂-initial t p)
    ∂ t (return x)                     = fail
    ∂ t fail                           = fail
    ∂ t token                          = return t
    ∂ t (p₁ ∣ p₂)                      = ∂ t p₁ ∣ ∂ t p₂
    ∂ t (_∶_⊛_ (_ ∷ _) {[]}     p₁ p₂) = (_ ∷ _)        ∶ ∂ t p₁ ⊛ ♯? (∂-∅? t p₁) (♭₁ p₂)
    ∂ t (_∶_⊛_ (_ ∷ _) {f ∷ fs} p₁ p₂) = (_ ∷ _)        ∶ ∂ t p₁ ⊛ ♯? (∂-∅? t p₁)     p₂
                                       ∣ ∂-initial t p₂ ∶ ♯? (∂-∅? t p₂) (⋁ return (f ∷ fs)) ⊛ ∂ t p₂
    ∂ t (_∶_⊛_ []      {[]}     p₁ p₂) = []             ∶ ♯₁ ∂ t (♭₁ p₁) ⊛ ♯? (∂-∅? t (♭₁ p₁)) (♭₁ p₂)
    ∂ t (_∶_⊛_ []      {f ∷ fs} p₁ p₂) = []             ∶ ♯₁ ∂ t (♭₁ p₁) ⊛ ♯? (∂-∅? t (♭₁ p₁))     p₂
                                       ∣ ∂-initial t p₂ ∶ ♯? (∂-∅? t p₂) (⋁ return (f ∷ fs)) ⊛ ∂ t p₂
    ∂ t (_>>=_ {xs = x ∷ xs}    p₁ p₂) = ∂ t p₁ >>= (λ x → ♯? (∂-∅? t p₁)     (p₂ x))
                                       ∣ ∂-⋁ t (x ∷ xs) p₂
    ∂ t (_>>=_ {xs = []}        p₁ p₂) = ∂ t p₁ >>=  λ x → ♯? (∂-∅? t p₁) (♭₁ (p₂ x))
    ∂ t (cast _ p)                     = ∂ t p

    -- ⋁ is inlined here, because otherwise the termination checker
    -- would not accept the code.

    ∂-⋁ : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
          (t : Tok) (xs : List R₁) (p : (x : R₁) → Parser Tok R₂ (f x)) →
          Parser Tok R₂ (∂-⋁-initial t xs p)
    ∂-⋁ t []       p = fail
    ∂-⋁ t (x ∷ xs) p = ∂ t (p x) ∣ ∂-⋁ t xs p

-- Parsing: x ∈ parseComplete p s  iff  x ∈ p · s.

parseComplete : ∀ {Tok R xs} → Parser Tok R xs → List Tok → List R
parseComplete {xs = xs} p []      = xs
parseComplete           p (t ∷ s) = parseComplete (simplify (∂ t p)) s

------------------------------------------------------------------------
-- Soundness

private

  ⋁-sound : ∀ {Tok R₁ R₂ y s} {i : R₁ → List R₂} →
            (f : (x : R₁) → Parser Tok R₂ (i x)) (xs : List R₁) →
            y ∈ ⋁ f xs · s → ∃ λ x → Σ (x ∈ xs) λ _ → y ∈ f x · s
  ⋁-sound f []       ()
  ⋁-sound f (x ∷ xs) (∣ˡ    y∈fx)   = (x , here , y∈fx)
  ⋁-sound f (x ∷ xs) (∣ʳ ._ y∈⋁fxs) =
    Prod1.map₀₁ id (Prod1.map₀₁ there (λ y∈ → y∈)) (⋁-sound f xs y∈⋁fxs)

  mutual

    ∂-sound : ∀ {Tok R xs x s} {t} (p : Parser Tok R xs) →
              x ∈ ∂ t p · s → x ∈ p · t ∷ s
    ∂-sound token                           return                 = token
    ∂-sound (p₁ ∣ p₂)                       (∣ˡ    x∈p₁)           = ∣ˡ     (∂-sound p₁ x∈p₁)
    ∂-sound (_∣_ {xs₁ = xs₁} p₁ p₂)         (∣ʳ ._ x∈p₂)           = ∣ʳ xs₁ (∂-sound p₂ x∈p₂)
    ∂-sound (_∶_⊛_ (_ ∷ _)  {[]}     p₁ p₂)        (f∈p₁′ ⊛ x∈p₂)  = ∂-sound     p₁  f∈p₁′ ⊛ cast∈ refl (♭?♯? (∂-∅? _     p₁))  refl x∈p₂
    ∂-sound (_∶_⊛_ []       {[]}     p₁ p₂)        (f∈p₁′ ⊛ x∈p₂)  = ∂-sound (♭₁ p₁) f∈p₁′ ⊛ cast∈ refl (♭?♯? (∂-∅? _ (♭₁ p₁))) refl x∈p₂
    ∂-sound (_∶_⊛_ (_ ∷ _)  {f ∷ fs} p₁ p₂) (∣ˡ    (f∈p₁′ ⊛ x∈p₂)) = ∂-sound     p₁  f∈p₁′ ⊛ cast∈ refl (♭?♯? (∂-∅? _     p₁))  refl x∈p₂
    ∂-sound (_∶_⊛_ []       {f ∷ fs} p₁ p₂) (∣ˡ    (f∈p₁′ ⊛ x∈p₂)) = ∂-sound (♭₁ p₁) f∈p₁′ ⊛ cast∈ refl (♭?♯? (∂-∅? _ (♭₁ p₁))) refl x∈p₂
    ∂-sound (_∶_⊛_ (x ∷ xs) {f ∷ fs} p₁ p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) with ⋁-sound return (f ∷ fs)
                                                                             (cast∈ refl (♭?♯? (∂-∅? _ p₂)) refl f∈⋁f∷fs)
    ∂-sound (_∶_⊛_ (x ∷ xs) {f ∷ fs} p₁ p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) | (f′ , f′∈fs , return) =
                                                                        initial-sound p₁ f′∈fs ⊛ ∂-sound p₂ x∈p₂′
    ∂-sound (_∶_⊛_ []       {f ∷ fs} p₁ p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) with ⋁-sound return (f ∷ fs)
                                                                             (cast∈ refl (♭?♯? (∂-∅? _ p₂)) refl f∈⋁f∷fs)
    ∂-sound (_∶_⊛_ []       {f ∷ fs} p₁ p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) | (f′ , f′∈fs , return) =
                                                                        initial-sound (♭₁ p₁) f′∈fs ⊛ ∂-sound p₂ x∈p₂′
    ∂-sound (_>>=_ {xs = x ∷ xs} p₁ p₂)     (∣ʳ ._ z∈p₂′x)            with ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
    ∂-sound (_>>=_ {xs = x ∷ xs} p₁ p₂)     (∣ʳ ._ z∈p₂′x)            | (y , y∈x∷xs , z∈p₂′y) =
                                                                        _>>=_ {p₂ = p₂} (initial-sound p₁ y∈x∷xs) z∈p₂′y
    ∂-sound (_>>=_ {xs = x ∷ xs} p₁ p₂)     (∣ˡ (x∈p₁′ >>= y∈p₂x))    = _>>=_ {p₂ = p₂} (∂-sound p₁ x∈p₁′)
                                                                                        (cast∈ refl (♭?♯? (∂-∅? _ p₁))
                                                                                               refl y∈p₂x)
    ∂-sound (_>>=_ {xs = []}     p₁ p₂)     (x∈p₁′ >>= y∈p₂x)         = ∂-sound p₁ x∈p₁′ >>=
                                                                        cast∈ refl (♭?♯? (∂-∅? _ p₁)) refl y∈p₂x
    ∂-sound (cast _ p)                      x∈p                       = cast (∂-sound p x∈p)

    ∂-sound (return _) ()
    ∂-sound fail       ()

    ∂-⋁-sound : ∀ {Tok R₁ R₂ t y s} {f : R₁ → List R₂} xs
                  (p : (x : R₁) → Parser Tok R₂ (f x)) →
                y ∈ ∂-⋁ t xs p · s →
                ∃ λ x → Σ (x ∈ xs) λ _ → y ∈ p x · t ∷ s
    ∂-⋁-sound []       p ()
    ∂-⋁-sound (x ∷ xs) p (∣ˡ    y∈p₂′x)  = (x , here , ∂-sound (p x) y∈p₂′x)
    ∂-⋁-sound (x ∷ xs) p (∣ʳ ._ y∈p₂′xs) =
      Prod1.map₀₁ id (Prod1.map₀₁ there (λ y∈ → y∈))
        (∂-⋁-sound xs p y∈p₂′xs)

sound : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
        x ∈ parseComplete p s → x ∈ p · s
sound []      x∈p = initial-sound _ x∈p
sound (t ∷ s) x∈p =
  ∂-sound _ (proj₁₁₂ Simplification.correct (sound s x∈p))

------------------------------------------------------------------------
-- Completeness

private

  ⋁-complete : ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
               (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
               x ∈ xs → y ∈ f x · s → y ∈ ⋁ f xs · s
  ⋁-complete         f here         y∈fx = ∣ˡ y∈fx
  ⋁-complete {i = i} f (there x∈xs) y∈fx = ∣ʳ (i _) (⋁-complete f x∈xs y∈fx)

  mutual

    ∂-complete : ∀ {Tok R xs x s t} {p : Parser Tok R xs} →
                 x ∈ p · t ∷ s → x ∈ ∂ t p · s
    ∂-complete x∈p = ∂-complete′ _ x∈p refl
      where
      ∂-complete′ : ∀ {Tok R xs x s s′ t} (p : Parser Tok R xs) →
                    x ∈ p · s′ → s′ ≡ t ∷ s → x ∈ ∂ t p · s
      ∂-complete′ token     token       refl = return

      ∂-complete′ (p₁ ∣ p₂) (∣ˡ   x∈p₁) refl = ∣ˡ                  (∂-complete x∈p₁)
      ∂-complete′ (p₁ ∣ p₂) (∣ʳ _ x∈p₂) refl = ∣ʳ (∂-initial _ p₁) (∂-complete x∈p₂)

      ∂-complete′ (_∶_⊛_ (_ ∷ _)  {[]}    p₁ p₂)
                  (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     ∂-complete f∈p₁ ⊛ cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _     p₁)))  refl x∈p₂
      ∂-complete′ (_∶_⊛_ (_ ∷ _)  {_ ∷ _} p₁ p₂)
                  (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (∂-complete f∈p₁ ⊛ cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _     p₁)))  refl x∈p₂)
      ∂-complete′ (_∶_⊛_ []       {[]}    p₁ p₂)
                  (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl =     ∂-complete f∈p₁ ⊛ cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _ (♭₁ p₁)))) refl x∈p₂
      ∂-complete′ (_∶_⊛_ []       {_ ∷ _} p₁ p₂)
                  (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (∂-complete f∈p₁ ⊛ cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _ (♭₁ p₁)))) refl x∈p₂)
      ∂-complete′ (_∶_⊛_ (x ∷ xs) {_ ∷ _} p₁ p₂)
                  (_⊛_ {s₁ = []} f∈p₁ x∈p₂)    refl = ∣ʳ (∂-initial _ p₁ ⊛′ (x ∷ xs))
                                                         (cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _ p₂))) refl
                                                            (⋁-complete return (initial-complete f∈p₁) return)
                                                          ⊛ ∂-complete x∈p₂)
      ∂-complete′ (_∶_⊛_ []       {_ ∷ _} p₁ p₂)
                  (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣ʳ []
                                                         (cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _ p₂))) refl
                                                            (⋁-complete return (initial-complete f∈p₁) return)
                                                          ⊛ ∂-complete x∈p₂)

      ∂-complete′ (_>>=_ {xs = x ∷ xs} {f} p₁ p₂)
                  (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ (∂-initial _ p₁ >>=′ f)
                                                            (∂-⋁-complete p₂ (initial-complete x∈p₁) y∈p₂x)
      ∂-complete′ (_>>=_ {xs = _ ∷ _}      p₁ p₂)
                  (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (∂-complete x∈p₁ >>=
                                                             cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _ p₁))) refl
                                                               y∈p₂x)
      ∂-complete′ (_>>=_ {xs = []}         p₁ p₂)
                  (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     ∂-complete x∈p₁ >>=
                                                             cast∈ refl (Eq1.sym (♭?♯? (∂-∅? _ p₁))) refl
                                                               y∈p₂x

      ∂-complete′ (cast _ p) (cast x∈p) refl = ∂-complete x∈p

      ∂-complete′ (return _) () refl
      ∂-complete′ fail       () refl
      ∂-complete′ (_∶_⊛_ _    {[]} _ _) (_⊛_   {s₁ = []} f∈p₁ _) _ with initial-complete f∈p₁
      ... | ()
      ∂-complete′ (_>>=_ {xs = []} _ _) (_>>=_ {s₁ = []} x∈p₁ _) _ with initial-complete x∈p₁
      ... | ()

    ∂-⋁-complete : ∀ {Tok R₁ R₂ t x y xs s} {f : R₁ → List R₂}
                   (p : (x : R₁) → Parser Tok R₂ (f x)) →
                   x ∈ xs → y ∈ p x · t ∷ s → y ∈ ∂-⋁ t xs p · s
    ∂-⋁-complete p here         y∈px = ∣ˡ (∂-complete y∈px)
    ∂-⋁-complete p (there x∈xs) y∈px =
      ∣ʳ (∂-initial _ (p _)) (∂-⋁-complete p x∈xs y∈px)

complete : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
           x ∈ p · s → x ∈ parseComplete p s
complete []      x∈p = initial-complete x∈p
complete (t ∷ s) x∈p =
  complete s (proj₁₁₁ Simplification.correct (∂-complete x∈p))
