------------------------------------------------------------------------
-- A breadth-first backend
------------------------------------------------------------------------

-- Similar to Brzozowski's "Derivatives of Regular Expressions".

-- TODO: Examine if the use of simplification really is an
-- optimisation.

module TotalParserCombinators.Backend.BreadthFirst where

open import Category.Monad
open import Coinduction
open import Data.Bool
open import Data.Function hiding (_∶_)
open import Data.List as List
open import Data.List.Any
open Membership-≡
open RawMonad List.monad
  using () renaming (_>>=_ to _>>=′_; return to return′)
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Parser.Semantics
  hiding (sound; complete)
open import TotalParserCombinators.Backend.Simplification
  as Simplification using (simplify)

------------------------------------------------------------------------
-- Parsing

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

mutual

  ∂-initial : ∀ {Tok R xs} → Parser Tok R xs → Tok → List R
  ∂-initial (return _)      _ = _
  ∂-initial fail            _ = _
  ∂-initial token           _ = _
  ∂-initial (_ ∣ _)         _ = _
  ∂-initial (_ <$> _)       _ = _
  ∂-initial (⟨ _ ⟩ ⊛ ⟪ _ ⟫) _ = _
  ∂-initial (⟪ _ ⟫ ⊛ ⟪ _ ⟫) _ = _
  ∂-initial (⟨ _ ⟩ ⊛ ⟨ _ ⟩) _ = _
  ∂-initial (⟪ _ ⟫ ⊛ ⟨ _ ⟩) _ = _
  ∂-initial (_ >>=  ⟪ _ ⟫)  _ = _
  ∂-initial (_ >>=  ⟨ _ ⟩)  _ = _
  ∂-initial (_ >>=! ⟪ _ ⟫)  _ = _
  ∂-initial (_ >>=! ⟨ _ ⟩)  _ = _
  ∂-initial (nonempty _)    _ = _
  ∂-initial (cast _ _)      _ = _

  ∂-⋁-initial : ∀ {Tok R₁ R₂} {f : R₁ → List R₂} →
                List R₁ → ((x : R₁) → Parser Tok R₂ (f x)) → Tok →
                List R₂
  ∂-⋁-initial []      _ _ = _
  ∂-⋁-initial (_ ∷ _) _ _ = _

-- "Derivative": x ∈ ∂ p t · s  iff  x ∈ p · t ∷ s.

-- Note that these functions would not work with the simplified
-- parsers. The reason is that the analogue of p₁ !>>= p₂ is
-- sometimes changed to the analogue of p₁′ ?>>= p₂′, where p₂′ is
-- still dependently typed, and _?>>=_ does not accept dependently
-- typed arguments.

mutual

  -- Note that simplification is currently not performed
  -- (co)recursively under ♯_.

  ∂ : ∀ {Tok R xs}
      (p : Parser Tok R xs) (t : Tok) → Parser Tok R (∂-initial p t)
  ∂ (return x)                 t = fail
  ∂ fail                       t = fail
  ∂ token                      t = return t
  ∂ (p₁ ∣ p₂)                  t = ∂ p₁ t ∣ ∂ p₂ t
  ∂ (f <$> p)                  t = f <$> ∂ p t
  ∂ (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)          t = ⟨   ∂    p₁  t ⟩ ⊛ ♯? (♭ p₂)
  ∂ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)          t = ⟪ ♯ ∂ (♭ p₁) t ⟫ ⊛ ♯? (♭ p₂)
  ∂ (⟨ p₁ ⟩ ⊛ ⟨_⟩ {f} {fs} p₂) t = ⟨   ∂    p₁  t ⟩ ⊛ ♯?    p₂
                                 ∣ ♯? (⋁ return (f ∷ fs)) ⊛ ⟨ ∂ p₂ t ⟩
  ∂ (⟪ p₁ ⟫ ⊛ ⟨_⟩ {f} {fs} p₂) t = ⟪ ♯ ∂ (♭ p₁) t ⟫ ⊛ ♯?     p₂
                                 ∣ ♯? (⋁ return (f ∷ fs)) ⊛ ⟨ ∂ p₂ t ⟩
  ∂ (p₁ >>=  ⟪ p₂ ⟫)           t = ∂ p₁ t >>= ♯? (♭ p₂)
  ∂ (p₁ >>=  ⟨_⟩ {x} {xs} p₂)  t = ∂ p₁ t >>= ♯?    p₂
                                 ∣ ∂-⋁ (x ∷ xs) p₂ t
  ∂ (p₁ >>=! ⟪ p₂ ⟫)           t = (♯ ∂ (♭ p₁) t) >>=! ♯? (♭ p₂)
  ∂ (p₁ >>=! ⟨_⟩ {x} {xs} p₂)  t = (♯ ∂ (♭ p₁) t) >>=! ♯?    p₂
                                 ∣ ∂-⋁ (x ∷ xs) p₂ t
  ∂ (nonempty p)               t = ∂ p t
  ∂ (cast _ p)                 t = ∂ p t

  -- ⋁ is inlined here, because otherwise the termination checker
  -- would not accept the code.

  ∂-⋁ : ∀ {Tok R₁ R₂} {f : R₁ → List R₂}
        (xs : List R₁) (p : (x : R₁) → Parser Tok R₂ (f x)) (t : Tok) →
        Parser Tok R₂ (∂-⋁-initial xs p t)
  ∂-⋁ []       p t = fail
  ∂-⋁ (x ∷ xs) p t = ∂ (p x) t ∣ ∂-⋁ xs p t

-- Parsing: x ∈ parseComplete p s  iff  x ∈ p · s.

parseComplete : ∀ {Tok R xs} → Parser Tok R xs → List Tok → List R
parseComplete {xs = xs} p []      = xs
parseComplete           p (t ∷ s) = parseComplete (simplify (∂ p t)) s

------------------------------------------------------------------------
-- Soundness

⋁-sound : ∀ {Tok R₁ R₂ y s} {i : R₁ → List R₂} →
          (f : (x : R₁) → Parser Tok R₂ (i x)) (xs : List R₁) →
          y ∈ ⋁ f xs · s → ∃ λ x → (x ∈ xs) × (y ∈ f x · s)
⋁-sound f []       ()
⋁-sound f (x ∷ xs) (∣ˡ    y∈fx)   = (x , here refl , y∈fx)
⋁-sound f (x ∷ xs) (∣ʳ ._ y∈⋁fxs) =
  Prod.map id (Prod.map there (λ y∈ → y∈)) (⋁-sound f xs y∈⋁fxs)

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
  ∂-sound (⟨ p₁ ⟩ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) with ⋁-sound return (f ∷ fs)
                                                                            (cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs)
  ∂-sound (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)          (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) | (f′ , f′∈f∷fs , return) =
                                                                 initial-sound p₁ f′∈f∷fs ⊛ ∂-sound p₂ x∈p₂′
  ∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)          (∣ˡ    (f∈p₁′   ⊛ x∈p₂))  = ∂-sound (♭ p₁) f∈p₁′ ⊛
                                                                 cast∈ refl (♭?♯? (∂-initial (♭ p₁) _)) refl x∈p₂
  ∂-sound (⟪ p₁ ⟫ ⊛ ⟨_⟩ {f} {fs} p₂) (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) with ⋁-sound return (f ∷ fs)
                                                                            (cast∈ refl (♭?♯? (∂-initial p₂ _)) refl f∈⋁f∷fs)
  ∂-sound (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)          (∣ʳ ._ (f∈⋁f∷fs ⊛ x∈p₂′)) | (f′ , f′∈f∷fs , return) =
                                                                 initial-sound (♭ p₁) f′∈f∷fs ⊛ ∂-sound p₂ x∈p₂′
  ∂-sound (p₁ >>= ⟨_⟩ {x} {xs} p₂)   (∣ʳ ._ z∈p₂′x)            with ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
  ∂-sound (p₁ >>= ⟨_⟩ {x} {xs} p₂)   (∣ʳ ._ z∈p₂′x)            | (y , y∈x∷xs , z∈p₂′y) =
                                                                 _>>=_ {p₂ = ⟨ p₂ ⟩} (initial-sound p₁ y∈x∷xs) z∈p₂′y
  ∂-sound (p₁ >>= ⟨ p₂ ⟩)            (∣ˡ (x∈p₁′ >>=  y∈p₂x))   = _>>=_ {p₂ = ⟨ p₂ ⟩}
                                                                       (∂-sound p₁ x∈p₁′)
                                                                       (cast∈ refl (cong (λ f → f _) (♭?♯? (∂-initial p₁ _) {p₂})) refl
                                                                              y∈p₂x)
  ∂-sound (p₁ >>= ⟪ p₂ ⟫)                (x∈p₁′ >>=  y∈p₂x)    = ∂-sound p₁ x∈p₁′ >>=
                                                                 cast∈ refl (cong (λ f → f _) (♭?♯? (∂-initial p₁ _) {♭ p₂})) refl y∈p₂x

  ∂-sound (p₁ >>=! ⟨_⟩ {x} {xs} p₂)  (∣ʳ ._ z∈p₂′x)            with ∂-⋁-sound (x ∷ xs) p₂ z∈p₂′x
  ∂-sound (p₁ >>=! ⟨_⟩ {x} {xs} p₂)  (∣ʳ ._ z∈p₂′x)            | (y , y∈x∷xs , z∈p₂′y) =
                                                                 _>>=!_ {p₂ = ⟨ _ ⟩} (initial-sound (♭ p₁) y∈x∷xs) z∈p₂′y
  ∂-sound (p₁ >>=! ⟨ p₂ ⟩)   (∣ˡ (_>>=!_ {x = x} x∈p₁′ y∈p₂x)) = _>>=!_ {p₂ = ⟨ _ ⟩}
                                                                        (∂-sound (♭ p₁) x∈p₁′)
                                                                        (cast∈ refl (cong (λ f → f x) (♭?♯? (∂-initial (♭ p₁) _) {p₂}))
                                                                               refl y∈p₂x)
  ∂-sound (p₁ >>=! ⟪ p₂ ⟫)       (_>>=!_ {x = x} x∈p₁′ y∈p₂x)  = ∂-sound (♭ p₁) x∈p₁′ >>=!
                                                                 cast∈ refl (cong (λ f → f x) (♭?♯? (∂-initial (♭ p₁) _) {♭ p₂})) refl
                                                                       y∈p₂x
  ∂-sound (nonempty p)                x∈p                      = nonempty (∂-sound p x∈p)
  ∂-sound (cast _ p)                  x∈p                      = cast (∂-sound p x∈p)

  ∂-sound (return _) ()
  ∂-sound fail       ()

  ∂-⋁-sound : ∀ {Tok R₁ R₂ t z s} {f : R₁ → List R₂}
              xs (p : (x : R₁) → Parser Tok R₂ (f x)) →
              z ∈ ∂-⋁ xs p t · s →
              ∃ λ x → (x ∈ xs) × (z ∈ p x · t ∷ s)
  ∂-⋁-sound []       p ()
  ∂-⋁-sound (x ∷ xs) p (∣ˡ    z∈p₂′x)  = (x , here refl , ∂-sound (p x) z∈p₂′x)
  ∂-⋁-sound (x ∷ xs) p (∣ʳ ._ z∈p₂′xs) =
    Prod.map id (Prod.map there (λ z∈ → z∈))
      (∂-⋁-sound xs p z∈p₂′xs)

sound : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
        x ∈ parseComplete p s → x ∈ p · s
sound []      x∈p = initial-sound _ x∈p
sound (t ∷ s) x∈p =
  ∂-sound _ (Simplification.sound (sound s x∈p))

------------------------------------------------------------------------
-- Completeness

⋁-complete : ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
             (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
             x ∈ xs → y ∈ f x · s → y ∈ ⋁ f xs · s
⋁-complete         f (here refl)  y∈fx = ∣ˡ y∈fx
⋁-complete {i = i} f (there x∈xs) y∈fx = ∣ʳ (i _) (⋁-complete f x∈xs y∈fx)

mutual

  ∂-complete : ∀ {Tok R xs x s t} {p : Parser Tok R xs} →
               x ∈ p · t ∷ s → x ∈ ∂ p t · s
  ∂-complete x∈p = ∂-complete′ _ x∈p refl
    where
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
                                                          (⋁-complete return (initial-complete f∈p₁) return) ⊛
                                                        ∂-complete x∈p₂)
    ∂-complete′ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)
                (_⊛_ {s₁ = _ ∷ _} f∈p₁ x∈p₂) refl = ∣ˡ (∂-complete f∈p₁ ⊛
                                                        cast∈ refl (sym (♭?♯? (∂-initial (♭ p₁) _))) refl x∈p₂)
    ∂-complete′ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)
                (_⊛_ {s₁ = []}    f∈p₁ x∈p₂) refl = ∣ʳ []
                                                       (cast∈ refl (sym (♭?♯? (∂-initial p₂ _))) refl
                                                          (⋁-complete return (initial-complete f∈p₁) return) ⊛
                                                        ∂-complete x∈p₂)

    ∂-complete′ (_>>=_ {f = f} p₁ ⟨ p₂ ⟩)
                (_>>=_ {s₁ = []}    x∈p₁ y∈p₂x) refl = ∣ʳ (∂-initial p₁ _ >>=′ f)
                                                          (∂-⋁-complete p₂ (initial-complete x∈p₁) y∈p₂x)
    ∂-complete′ (p₁ >>= ⟨ p₂ ⟩)
                (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl = ∣ˡ (∂-complete x∈p₁ >>=
                                                           cast∈ refl (cong (λ f → f _) (sym (♭?♯? (∂-initial p₁ _) {p₂}))) refl
                                                             y∈p₂x)
    ∂-complete′ (_>>=_ {R₁} p₁ ⟪ p₂ ⟫)
                (_>>=_ {s₁ = _ ∷ _} x∈p₁ y∈p₂x) refl =     ∂-complete x∈p₁ >>=
                                                           cast∈ refl (cong (λ f → f _) (sym (♭?♯? (∂-initial p₁ _) {♭ p₂}))) refl
                                                             y∈p₂x

    ∂-complete′ (p₁ >>=! ⟨ p₂ ⟩)
                (_>>=!_ {s₁ = []}    x∈p₁ y∈p₂x) refl    = ∣ʳ [] (∂-⋁-complete p₂ (initial-complete x∈p₁) y∈p₂x)
    ∂-complete′ (p₁ >>=! ⟨ p₂ ⟩)
                (_>>=!_ {x = x} {s₁ = _ ∷ _} x∈p₁ y∈p₂x)
                refl                                     = ∣ˡ (∂-complete x∈p₁ >>=!
                                                               cast∈ refl (cong (λ f → f x) (sym (♭?♯? (∂-initial (♭ p₁) _) {p₂}))) refl
                                                                 y∈p₂x)
    ∂-complete′ (_>>=!_ {R₁} p₁ ⟪ p₂ ⟫)
                (_>>=!_ {x = x} {s₁ = _ ∷ _} x∈p₁ y∈p₂x)
                refl                                     =    ∂-complete x∈p₁ >>=!
                                                              cast∈ refl (cong (λ f → f x) (sym (♭?♯? (∂-initial (♭ p₁) _) {♭ p₂}))) refl
                                                                y∈p₂x

    ∂-complete′ (nonempty p) (nonempty x∈p) refl = ∂-complete x∈p

    ∂-complete′ (cast _ p) (cast x∈p) refl = ∂-complete x∈p

    ∂-complete′ (return _) () refl
    ∂-complete′ fail       () refl
    ∂-complete′ (_  ⊛   ⟪ _ ⟫) (_⊛_    {s₁ = []} f∈p₁ _) _ with initial-complete f∈p₁
    ... | ()
    ∂-complete′ (_ >>=  ⟪ _ ⟫) (_>>=_  {s₁ = []} x∈p₁ _) _ with initial-complete x∈p₁
    ... | ()
    ∂-complete′ (_ >>=! ⟪ _ ⟫) (_>>=!_ {s₁ = []} x∈p₁ _) _ with initial-complete x∈p₁
    ... | ()

  ∂-⋁-complete : ∀ {Tok R₁ R₂ x t z s xs} {f : R₁ → List R₂}
                 (p : (x : R₁) → Parser Tok R₂ (f x)) →
                 x ∈ xs → z ∈ p x · t ∷ s → z ∈ ∂-⋁ xs p t · s
  ∂-⋁-complete p (here refl)  y∈px = ∣ˡ (∂-complete y∈px)
  ∂-⋁-complete p (there x∈xs) y∈px =
    ∣ʳ (∂-initial (p _) _) (∂-⋁-complete p x∈xs y∈px)

complete : ∀ {Tok R xs x} {p : Parser Tok R xs} (s : List Tok) →
           x ∈ p · s → x ∈ parseComplete p s
complete []      x∈p = initial-complete x∈p
complete (t ∷ s) x∈p =
  complete s (Simplification.complete (∂-complete x∈p))

------------------------------------------------------------------------
-- Some results about ∂

-- ∂ is monotone.

∂-mono : ∀ {Tok R xs₁ xs₂ t}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ⊑ p₂ → ∂ p₁ t ⊑ ∂ p₂ t
∂-mono p₁⊑p₂ = ∂-complete ∘ p₁⊑p₂ ∘ ∂-sound _

-- ∂ preserves equality.

∂-cong : ∀ {Tok R xs₁ xs₂ t}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈ p₂ → ∂ p₁ t ≈ ∂ p₂ t
∂-cong = Prod.map ∂-mono ∂-mono
