------------------------------------------------------------------------
-- Brzozowski-style derivatives of parsers
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Derivative where

open import Coinduction
open import Data.List

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

-- Functions calculating the index of the derivative.

mutual

  ∂-initial : ∀ {Tok R xs} → Parser Tok R xs → Tok → List R
  ∂-initial (return _)                _ = _
  ∂-initial fail                      _ = _
  ∂-initial token                     _ = _
  ∂-initial (_ ∣ _)                   _ = _
  ∂-initial (_ <$> _)                 _ = _
  ∂-initial (⟨ _ ⟩ ⊛ ⟪ _ ⟫)           _ = _
  ∂-initial (⟪ _ ⟫ ⊛ ⟪ _ ⟫)           _ = _
  ∂-initial (⟨ _ ⟩ ⊛ ⟨ _ ⟩)           _ = _
  ∂-initial (⟪ _ ⟫ ⊛ ⟨ _ ⟩)           _ = _
  ∂-initial (_>>=_  {xs = []   } _ _) _ = _
  ∂-initial (_>>=_  {xs = _ ∷ _} _ _) _ = _
  ∂-initial (_>>=!_ {xs = []   } _ _) _ = _
  ∂-initial (_>>=!_ {xs = _ ∷ _} _ _) _ = _
  ∂-initial (nonempty _)              _ = _
  ∂-initial (cast _ _)                _ = _

  ∂!-initial : ∀ {Tok R₁ R₂ xs y} {ys : List R₁} →
               ∞? (Parser Tok R₂ xs) (y ∷ ys) → Tok → List R₂
  ∂!-initial ⟨ _ ⟩ _ = _

-- "Derivative": x ∈ ∂ p t · s  iff  x ∈ p · t ∷ s.

mutual

  ∂ : ∀ {Tok R xs}
      (p : Parser Tok R xs) (t : Tok) → Parser Tok R (∂-initial p t)
  ∂ (return x)                   t = fail
  ∂ fail                         t = fail
  ∂ token                        t = return t
  ∂ (p₁ ∣ p₂)                    t = ∂ p₁ t ∣ ∂ p₂ t
  ∂ (f <$> p)                    t = f <$> ∂ p t
  ∂ (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)            t = ⟨   ∂    p₁  t ⟩ ⊛ ♯? (♭ p₂)
  ∂ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)            t = ⟪ ♯ ∂ (♭ p₁) t ⟫ ⊛ ♯? (♭ p₂)
  ∂ (⟨ p₁ ⟩ ⊛ ⟨_⟩ {f} {fs} p₂)   t = ⟨   ∂    p₁  t ⟩ ⊛ ♯?    p₂
                                   ∣ ♯? (return⋆ (f ∷ fs)) ⊛ ⟨ ∂ p₂ t ⟩
  ∂ (⟪ p₁ ⟫ ⊛ ⟨_⟩ {f} {fs} p₂)   t = ⟪ ♯ ∂ (♭ p₁) t ⟫ ⊛ ♯?     p₂
                                   ∣ ♯? (return⋆ (f ∷ fs)) ⊛ ⟨ ∂ p₂ t ⟩
  ∂ (_>>=_ {xs = []}      p₁ p₂) t = ∂ p₁ t >>= (λ x → ♯? (♭? (p₂ x)))
  ∂ (_>>=_ {xs = x ∷ xs}  p₁ p₂) t = ∂ p₁ t >>= (λ x → ♯? (♭? (p₂ x)))
                                   ∣ return⋆ (x ∷ xs) >>= λ x → ⟨ ∂! (p₂ x) t ⟩
  ∂ (_>>=!_ {xs = []}     p₁ p₂) t = (♯ ∂ (♭ p₁) t) >>=! (λ x → ♯? (♭? (p₂ x)))
  ∂ (_>>=!_ {xs = x ∷ xs} p₁ p₂) t = (♯ ∂ (♭ p₁) t) >>=! (λ x → ♯? (♭? (p₂ x)))
                                   ∣ return⋆ (x ∷ xs) >>= λ x → ⟨ ∂! (p₂ x) t ⟩
  ∂ (nonempty p)                 t = ∂ p t
  ∂ (cast _ p)                   t = ∂ p t

  ∂! : ∀ {Tok R₁ R₂ xs y} {ys : List R₁}
       (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) (t : Tok) →
       Parser Tok R₂ (∂!-initial p t)
  ∂! ⟨ p ⟩ t = ∂ p t

-- Parsing: x ∈ parseComplete p s  iff  x ∈ p · s.

parseComplete : ∀ {Tok R xs} → Parser Tok R xs → List Tok → List R
parseComplete {xs = xs} p []      = xs
parseComplete           p (t ∷ s) = parseComplete (∂ p t) s
