------------------------------------------------------------------------
-- A breadth-first backend
------------------------------------------------------------------------

-- Similar to Brzozowski's "Derivatives of Regular Expressions".

-- TODO: Examine if the use of simplification really is an
-- optimisation.

module StructurallyRecursiveDescentParsing.Backend.BreadthFirst where

open import Coinduction
open import Data.Bool
open import Data.Function
open import Data.List
open import Data.Product1 as Prod1 renaming (∃₀₁ to ∃)
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

  ⋁-nullable : ∀ {R₁} → (R₁ → Bool) → List R₁ → Bool
  ⋁-nullable e []       = _
  ⋁-nullable e (x ∷ xs) = _

  ⋁ : ∀ {Tok R₁ R₂} {e : R₁ → Bool} →
      ((x : R₁) → Parser Tok (e x) R₂) → (xs : List R₁) →
      Parser Tok (⋁-nullable e xs) R₂
  ⋁ f []       = fail
  ⋁ f (x ∷ xs) = f x ∣ ⋁ f xs

  -- "Derivative": x ∈ ∂ t p · s  iff  x ∈ p · t ∷ s.

  ∂-nullable : ∀ {Tok e R} → Tok → Parser Tok e R → Bool
  ∂-nullable _ (return _)          = _
  ∂-nullable _ fail                = _
  ∂-nullable _ token               = _
  ∂-nullable _ (_ ∣ _)             = _
  ∂-nullable _ (_>>=_ {true}  _ _) = _
  ∂-nullable _ (_>>=_ {false} _ _) = _
  ∂-nullable _ (cast _ _)          = _

  -- Note that this function would not work with the simplified
  -- parsers. The reason is that the analogue of p₁ !>>= p₂ is
  -- sometimes changed to the analogue of p₁′ ?>>= p₂′, where p₂′ is
  -- still dependently typed, and _?>>=_ does not accept dependently
  -- typed arguments.

  ∂ : ∀ {Tok e R}
      (t : Tok) (p : Parser Tok e R) → Parser Tok (∂-nullable t p) R
  ∂ t (return x)            = fail
  ∂ t fail                  = fail
  ∂ t token                 = return t
  ∂ t (p₁ ∣ p₂)             = ∂ t p₁ ∣ ∂ t p₂
  ∂ t (_>>=_ {true}  p₁ p₂) = ∂ t p₁ >>= (λ x → ♯? (∂-nullable t p₁) (p₂ x))
                            ∣ ⋁ (λ x → ∂ t (p₂ x)) (initial p₁)
  ∂ t (_>>=_ {false} p₁ p₂) = ∂ t p₁ >>= (λ x → ♭¿ (∂-nullable t p₁) (p₂ x))
  ∂ t (cast _ p)            = ∂ t p

-- Parsing: x ∈ parseComplete p s  iff  x ∈ p · s.

parseComplete : ∀ {Tok e R} → Parser Tok e R → List Tok → List R
parseComplete p []      = initial p
parseComplete p (t ∷ s) = parseComplete (simplify (∂ t p)) s

------------------------------------------------------------------------
-- Soundness

private

  ⋁-sound : ∀ {Tok R₁ R₂ y s} {e : R₁ → Bool} →
            (f : (x : R₁) → Parser Tok (e x) R₂) (xs : List R₁) →
            y ∈ ⋁ f xs · s → ∃ λ x → Σ₀₁ (x ∈ xs) λ _ → y ∈ f x · s
  ⋁-sound f []       ()
  ⋁-sound f (x ∷ xs) (∣ˡ    y∈fx)   = (x , here , y∈fx)
  ⋁-sound f (x ∷ xs) (∣ʳ ._ y∈⋁fxs) =
    Prod1.map₀₁ id (Prod1.map₀₁ there (λ y∈ → y∈)) (⋁-sound f xs y∈⋁fxs)

  ∂-sound : ∀ {Tok e R x s} {t} (p : Parser Tok e R) →
            x ∈ ∂ t p · s → x ∈ p · t ∷ s
  ∂-sound token                 return                 = token
  ∂-sound (p₁ ∣ p₂)             (∣ˡ    x∈p₁)           = ∣ˡ    (∂-sound p₁ x∈p₁)
  ∂-sound (_∣_ {e₁} p₁ p₂)      (∣ʳ ._ x∈p₂)           = ∣ʳ e₁ (∂-sound p₂ x∈p₂)
  ∂-sound (_>>=_ {true}  p₁ p₂) (∣ˡ (x∈p₁′ >>= y∈p₂x)) = ∂-sound p₁ x∈p₁′ >>=
                                                         cast∈ refl (♭?♯? (∂-nullable _ p₁)) refl y∈p₂x
  ∂-sound (_>>=_ {true}  p₁ p₂) (∣ʳ ._ z∈p₂′x)         with ⋁-sound (λ x → ∂ _ (p₂ x)) (initial p₁) z∈p₂′x
  ∂-sound (_>>=_ {true}  p₁ p₂) (∣ʳ ._ z∈p₂′x)         | (y , y∈init-p₁ , z∈p₂′y) =
                                                         initial-sound p₁ y∈init-p₁ >>=
                                                         ∂-sound (p₂ y) z∈p₂′y
  ∂-sound (_>>=_ {false} p₁ p₂) (x∈p₁′ >>= y∈p₂x)      = ∂-sound p₁ x∈p₁′ >>=
                                                         cast∈ refl (♭?♭¿ (∂-nullable _ p₁)) refl y∈p₂x
  ∂-sound (cast _ p)            x∈p                    = cast (∂-sound p x∈p)

  ∂-sound (return _) ()
  ∂-sound fail       ()

sound : ∀ {Tok e R x} {p : Parser Tok e R} (s : List Tok) →
        x ∈ parseComplete p s → x ∈ p · s
sound []      x∈p = initial-sound _ x∈p
sound (t ∷ s) x∈p =
  ∂-sound _ (proj₁₁₂ Simplification.correct (sound s x∈p))

------------------------------------------------------------------------
-- Completeness

private

  ⋁-complete : ∀ {Tok R₁ R₂ x y s} {e : R₁ → Bool} →
               (f : (x : R₁) → Parser Tok (e x) R₂) {xs : List R₁} →
               x ∈ xs → y ∈ f x · s → y ∈ ⋁ f xs · s
  ⋁-complete         f here         y∈fx = ∣ˡ y∈fx
  ⋁-complete {e = e} f (there x∈xs) y∈fx = ∣ʳ (e _) (⋁-complete f x∈xs y∈fx)

  ∂-complete : ∀ {Tok e R x s t} {p : Parser Tok e R} →
               x ∈ p · t ∷ s → x ∈ ∂ t p · s
  ∂-complete x∈p = ∂-complete′ _ x∈p refl
    where
    ∂-complete′ : ∀ {Tok e R x s s′ t} (p : Parser Tok e R) →
                  x ∈ p · s′ → s′ ≡ t ∷ s → x ∈ ∂ t p · s
    ∂-complete′ token     token       refl = return
    ∂-complete′ (p₁ ∣ p₂) (∣ˡ   x∈p₁) refl = ∣ˡ                   (∂-complete x∈p₁)
    ∂-complete′ (p₁ ∣ p₂) (∣ʳ _ x∈p₂) refl = ∣ʳ (∂-nullable _ p₁) (∂-complete x∈p₂)
    ∂-complete′ (_>>=_ {true}  p₁ p₂)
                (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ (∂-nullable _ p₁ ∧ _)
                                                          (⋁-complete (λ x → ∂ _ (p₂ x))
                                                                      (initial-complete x∈p₁)
                                                                      (∂-complete y∈p₂x))
    ∂-complete′ (_>>=_ {true}  p₁ p₂)
                (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (∂-complete x∈p₁ >>=
                                                           cast∈ refl (Eq1.sym (♭?♯? (∂-nullable _ p₁))) refl
                                                                 y∈p₂x)
    ∂-complete′ (_>>=_ {false} p₁ p₂)
                (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∂-complete x∈p₁ >>=
                                                       cast∈ refl (Eq1.sym (♭?♭¿ (∂-nullable _ p₁))) refl
                                                             y∈p₂x
    ∂-complete′ (cast _ p) (cast x∈p)           refl = ∂-complete x∈p

    ∂-complete′ (return _) () refl
    ∂-complete′ fail       () refl
    ∂-complete′ (_>>=_ {false} _ _) (_>>=_ {s₁ = []} x∈p₁ _) _ with doesNot x∈p₁
    ... | ()

complete : ∀ {Tok e R x} {p : Parser Tok e R} (s : List Tok) →
           x ∈ p · s → x ∈ parseComplete p s
complete []      x∈p = initial-complete x∈p
complete (t ∷ s) x∈p =
  complete s (proj₁₁₁ Simplification.correct (∂-complete x∈p))
