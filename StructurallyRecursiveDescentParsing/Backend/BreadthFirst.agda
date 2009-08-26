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
open import Data.List.Any
open Membership-≡
open RawMonad List.monad
  using () renaming (_>>=_ to _>>=′_; return to return′)
open import Data.Product1 as Prod1 renaming (∃₀₁ to ∃; Σ₀₁ to Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality1 as Eq1

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (sound; complete)
open import StructurallyRecursiveDescentParsing.Backend.Simplification
  as Simplification using (simplify)

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

  -- Functions calculating the index of the derivative.

  ∂-initial : ∀ {Tok R xs} → Tok → Parser Tok R xs → List R
  ∂-initial _ (return _)               = _
  ∂-initial _ fail                     = _
  ∂-initial _ token                    = _
  ∂-initial _ (_ ∣ _)                  = _
  ∂-initial _ (_ <$> _)                = _
  ∂-initial _ (_ ⊛ delayed _)          = _
  ∂-initial _ (_ ⊛ forced  _)          = _
  ∂-initial _ (_>>=_ {xs = []}    _ _) = _
  ∂-initial _ (_>>=_ {xs = _ ∷ _} _ _) = _
  ∂-initial _ (cast _ _)               = _

  ∂-⋁-initial : ∀ {Tok R₁ R₂ y} {ys : List R₁} {f : R₁ → List R₂} →
                Tok → List R₁ →
                ((x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys)) →
                List R₂
  ∂-⋁-initial _ []      _ = _
  ∂-⋁-initial _ (_ ∷ _) _ = _

  ∂?-initial : ∀ {Tok R R′ xs} {ys : List R′} →
               Tok → ∞? (Parser Tok R xs) ys → List R
  ∂?-initial _ (delayed _) = _
  ∂?-initial _ (forced  _) = _

  ∂!-initial : ∀ {Tok R₁ R₂ xs y} {ys : List R₁} →
               Tok → ∞? (Parser Tok R₂ xs) (y ∷ ys) → List R₂
  ∂!-initial _ (forced _) = _

  -- "Derivative": x ∈ ∂ t p · s  iff  x ∈ p · t ∷ s.

  -- Note that these functions would not work with the simplified
  -- parsers. The reason is that the analogue of p₁ !>>= p₂ is
  -- sometimes changed to the analogue of p₁′ ?>>= p₂′, where p₂′ is
  -- still dependently typed, and _?>>=_ does not accept dependently
  -- typed arguments.

  mutual

    -- Note that simplification is currently not performed
    -- (co)recursively under ♯₁_.

    ∂ : ∀ {Tok R xs}
        (t : Tok) (p : Parser Tok R xs) → Parser Tok R (∂-initial t p)
    ∂ t (return x)                  = fail
    ∂ t fail                        = fail
    ∂ t token                       = return t
    ∂ t (p₁ ∣ p₂)                   = ∂ t p₁ ∣ ∂ t p₂
    ∂ t (f <$> p)                   = f <$> ∂ t p
    ∂ t (p₁ ⊛ delayed     p₂)       = ∂? t p₁ ⊛ forced (♭₁  p₂)
    ∂ t (p₁ ⊛ forced {fs} p₂)       = ∂? t p₁ ⊛ forced      p₂
                                    ∣ forced (⋁ return fs) ⊛ forced (∂ t p₂)
    ∂ t (_>>=_ {xs = []}     p₁ p₂) = ∂ t p₁ >>= (λ x → forced (♭? (p₂ x)))
    ∂ t (_>>=_ {xs = x ∷ xs} p₁ p₂) = ∂ t p₁ >>= (λ x → forced (♭? (p₂ x)))
                                    ∣ ∂-⋁ t (x ∷ xs) p₂
    ∂ t (cast _ p)                  = ∂ t p

    -- ⋁ is inlined here, because otherwise the termination checker
    -- would not accept the code.

    ∂-⋁ : ∀ {Tok R₁ R₂ y} {ys : List R₁} {f : R₁ → List R₂}
          (t : Tok) (xs : List R₁)
          (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys)) →
          Parser Tok R₂ (∂-⋁-initial t xs p)
    ∂-⋁ t []       p = fail
    ∂-⋁ t (x ∷ xs) p = ∂! t (p x) ∣ ∂-⋁ t xs p

    ∂? : ∀ {Tok R R′ xs} {ys : List R′}
         (t : Tok) (p : ∞? (Parser Tok R xs) ys) →
         ∞? (Parser Tok R (∂?-initial t p)) ys
    ∂? t (delayed p) = delayed (♯₁ ∂ t (♭₁ p))
    ∂? t (forced  p) = forced     (∂ t     p)

    ∂! : ∀ {Tok R₁ R₂ xs y} {ys : List R₁}
         (t : Tok) (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) →
         Parser Tok R₂ (∂!-initial t p)
    ∂! t (forced p) = ∂ t p

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
  ⋁-sound f (x ∷ xs) (∣ˡ    y∈fx)   = (x , here refl , y∈fx)
  ⋁-sound f (x ∷ xs) (∣ʳ ._ y∈⋁fxs) =
    Prod1.map₀₁ id (Prod1.map₀₁ there (λ y∈ → y∈)) (⋁-sound f xs y∈⋁fxs)

  mutual

    ∂-sound : ∀ {Tok R xs x s} {t} (p : Parser Tok R xs) →
              x ∈ ∂ t p · s → x ∈ p · t ∷ s
    ∂-sound token                           return                 = token
    ∂-sound (p₁ ∣ p₂)                       (∣ˡ    x∈p₁)           = ∣ˡ     (∂-sound p₁ x∈p₁)
    ∂-sound (_∣_ {xs₁ = xs₁} p₁ p₂)         (∣ʳ ._ x∈p₂)           = ∣ʳ xs₁ (∂-sound p₂ x∈p₂)
    ∂-sound (f <$> p)                       (.f <$> x∈p)           = f <$> ∂-sound p x∈p
    ∂-sound (p₁ ⊛ delayed     p₂)           (f∈p₁′ ⊛ x∈p₂)         = ∂?-sound p₁ f∈p₁′ ⊛ x∈p₂
    ∂-sound (p₁ ⊛ forced      p₂)    (∣ˡ    (f∈p₁′ ⊛ x∈p₂))        = ∂?-sound p₁ f∈p₁′ ⊛ x∈p₂
    ∂-sound (p₁ ⊛ forced {fs} p₂)    (∣ʳ ._ (f∈⋁fs ⊛ x∈p₂′))       with ⋁-sound return fs f∈⋁fs
    ∂-sound (p₁ ⊛ forced      p₂)    (∣ʳ ._ (f∈⋁fs ⊛ x∈p₂′))       | (f′ , f′∈fs , return) =
                                                                     initial-sound (♭? p₁) f′∈fs ⊛ ∂-sound p₂ x∈p₂′
    ∂-sound (_>>=_ {xs = x ∷ xs} p₁ p₂)     (∣ʳ ._ z∈p₂′x)         with ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
    ∂-sound (_>>=_ {xs = x ∷ xs} p₁ p₂)     (∣ʳ ._ z∈p₂′x)         | (y , y∈x∷xs , z∈p₂′y) =
                                                                     _>>=_ {p₂ = p₂} (initial-sound p₁ y∈x∷xs) z∈p₂′y
    ∂-sound (_>>=_ {xs = x ∷ xs} p₁ p₂)     (∣ˡ (x∈p₁′ >>= y∈p₂x)) = _>>=_ {p₂ = p₂} (∂-sound p₁ x∈p₁′)
                                                                                     (cast∈ refl (♭?♯? (x ∷ xs))
                                                                                            refl y∈p₂x)
    ∂-sound (_>>=_ {R₁} {xs = []} p₁ p₂)    (x∈p₁′ >>= y∈p₂x)      = ∂-sound p₁ x∈p₁′ >>=
                                                                     cast∈ refl (♭?♯? {B = R₁} []) refl y∈p₂x
    ∂-sound (cast _ p)                      x∈p                    = cast (∂-sound p x∈p)

    ∂-sound (return _) ()
    ∂-sound fail       ()

    ∂-⋁-sound : ∀ {Tok R₁ R₂ t z s y} {ys : List R₁} {f : R₁ → List R₂}
                xs (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys)) →
                z ∈ ∂-⋁ t xs p · s →
                ∃ λ x → Σ (x ∈ xs) λ _ → z ∈ ♭? (p x) · t ∷ s
    ∂-⋁-sound []       p ()
    ∂-⋁-sound (x ∷ xs) p (∣ˡ    z∈p₂′x)  = ( x , here refl
                                           , ∂!-sound (p x) z∈p₂′x
                                           )
    ∂-⋁-sound (x ∷ xs) p (∣ʳ ._ z∈p₂′xs) =
      Prod1.map₀₁ id (Prod1.map₀₁ there (λ z∈ → z∈))
        (∂-⋁-sound xs p z∈p₂′xs)

    ∂?-sound : ∀ {Tok R R′ xs} {ys : List R′} {x s} {t : Tok}
               (p : ∞? (Parser Tok R xs) ys) →
               x ∈ ♭? (∂? t p) · s → x ∈ ♭? p · t ∷ s
    ∂?-sound (delayed p) x∈p′ = ∂-sound (♭₁ p) x∈p′
    ∂?-sound (forced  p) x∈p′ = ∂-sound     p  x∈p′

    ∂!-sound : ∀ {Tok R₁ R₂ z t s xs y} {ys : List R₁}
               (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) →
               z ∈ ∂! t p · s → z ∈ ♭? p · t ∷ s
    ∂!-sound (forced p) z∈p′ = ∂-sound p z∈p′

sound : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
        x ∈ parseComplete p s → x ∈ p · s
sound []      x∈p = initial-sound _ x∈p
sound (t ∷ s) x∈p =
  ∂-sound _ (Simplification.sound (sound s x∈p))

------------------------------------------------------------------------
-- Completeness

private

  ⋁-complete : ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
               (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
               x ∈ xs → y ∈ f x · s → y ∈ ⋁ f xs · s
  ⋁-complete         f (here refl)  y∈fx = ∣ˡ y∈fx
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

      ∂-complete′ (f <$> p) (.f <$> x∈p) refl = f <$> ∂-complete x∈p

      ∂-complete′ (p₁ ⊛ delayed p₂)
                  (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∂?-complete p₁ f∈p₁ ⊛ x∈p₂
      ∂-complete′ (_⊛_ {xs = xs} p₁ (forced p₂))
                  (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (∂?-complete p₁ f∈p₁ ⊛ x∈p₂)
      ∂-complete′ (_⊛_ {xs = xs} p₁ (forced p₂))
                  (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣ʳ (∂?-initial _ p₁ ⊛′ xs)
                                                         (⋁-complete return (initial-complete f∈p₁) return ⊛
                                                          ∂-complete x∈p₂)

      ∂-complete′ (_>>=_ {xs = x ∷ xs} {f} p₁ p₂)
                  (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ (∂-initial _ p₁ >>=′ f)
                                                            (∂-⋁-complete p₂ (initial-complete x∈p₁) y∈p₂x)
      ∂-complete′ (_>>=_ {xs = x ∷ xs}     p₁ p₂)
                  (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (∂-complete x∈p₁ >>=
                                                             cast∈ refl (Eq1.sym (♭?♯? (x ∷ xs))) refl
                                                               y∈p₂x)
      ∂-complete′ (_>>=_ {R₁} {xs = []}    p₁ p₂)
                  (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     ∂-complete x∈p₁ >>=
                                                             cast∈ refl (Eq1.sym (♭?♯? {B = R₁} [])) refl
                                                               y∈p₂x

      ∂-complete′ (cast _ p) (cast x∈p) refl = ∂-complete x∈p

      ∂-complete′ (return _) () refl
      ∂-complete′ fail       () refl
      ∂-complete′ (_ ⊛ delayed _)       (_⊛_   {s₁ = []} f∈p₁ _) _ with initial-complete f∈p₁
      ... | ()
      ∂-complete′ (_>>=_ {xs = []} _ _) (_>>=_ {s₁ = []} x∈p₁ _) _ with initial-complete x∈p₁
      ... | ()

    ∂-⋁-complete : ∀ {Tok R₁ R₂ x t z s xs y} {ys : List R₁}
                     {f : R₁ → List R₂}
                   (p : (x : R₁) → ∞? (Parser Tok R₂ (f x)) (y ∷ ys)) →
                   x ∈ xs → z ∈ ♭? (p x) · t ∷ s → z ∈ ∂-⋁ t xs p · s
    ∂-⋁-complete p (here refl)  y∈px = ∣ˡ (∂!-complete (p _) y∈px)
    ∂-⋁-complete p (there x∈xs) y∈px =
      ∣ʳ (∂!-initial _ (p _)) (∂-⋁-complete p x∈xs y∈px)

    ∂?-complete : ∀ {Tok R R′ xs} {ys : List R′} {x s} {t : Tok}
                  (p : ∞? (Parser Tok R xs) ys) →
                  x ∈ ♭? p · t ∷ s → x ∈ ♭? (∂? t p) · s
    ∂?-complete (delayed p) x∈p = ∂-complete x∈p
    ∂?-complete (forced  p) x∈p = ∂-complete x∈p

    ∂!-complete : ∀ {Tok R₁ R₂ z t s xs y} {ys : List R₁}
                  (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) →
                  z ∈ ♭? p · t ∷ s → z ∈ ∂! t p · s
    ∂!-complete (forced p) z∈p = ∂-complete z∈p

complete : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
           x ∈ p · s → x ∈ parseComplete p s
complete []      x∈p = initial-complete x∈p
complete (t ∷ s) x∈p =
  complete s (Simplification.complete (∂-complete x∈p))
