------------------------------------------------------------------------
-- Brzozowski-style derivatives of parsers
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Derivative where

open import Category.Monad
open import Coinduction
open import Data.List as List

open RawMonadPlus List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _>>=_  to _>>=′_
           )

open import TotalParserCombinators.Applicative using (_⊛′_)
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

-- Functions calculating the index of the derivative. Note that these
-- functions are highly constrained by the definition of ∂; most of
-- the right-hand sides could be replaced by _.

mutual

  ∂-initial : ∀ {Tok R xs} → Parser Tok R xs → Tok → List R
  ∂-initial (return x)        t = fail′
  ∂-initial fail              t = fail′
  ∂-initial token             t = return′ t
  ∂-initial (p₁ ∣ p₂)         t = ∂-initial p₁ t ∣′ ∂-initial p₂ t
  ∂-initial (nonempty p)      t = ∂-initial p t
  ∂-initial (cast eq p)       t = ∂-initial p t
  ∂-initial (f <$> p)         t = map f (∂-initial p t)
  ∂-initial (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫) t = ∂-initial p₁ t     ⊛′ initial-set (♭ p₂)
  ∂-initial (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫) t = fail′
  ∂-initial (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩) t = ∂-initial p₁ t     ⊛′ initial-set    p₂  ∣′
                                  initial-set    p₁  ⊛′ ∂-initial p₂ t
  ∂-initial (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩) t = initial-set (♭ p₁) ⊛′ ∂-initial p₂ t
  ∂-initial (p₁ >>= p₂)       t with initial-set p₁
  ... | []     =  ∂-initial p₁ t >>=′ (λ x → initial-set (♭? (p₂ x)))
  ... | x ∷ xs = (∂-initial p₁ t >>=′ (λ x → initial-set (♭? (p₂ x)))) ∣′
                 ((x ∷ xs) >>=′ λ x → ∂!-initial (p₂ x) t)
  ∂-initial (p₁ >>=! p₂)      t with initial-set (♭ p₁)
  ... | []     = []
  ... | x ∷ xs = (x ∷ xs) >>=′ λ x → ∂!-initial (p₂ x) t

  ∂!-initial : ∀ {Tok R₁ R₂ xs y} {ys : List R₁} →
               ∞? (Parser Tok R₂ xs) (y ∷ ys) → Tok → List R₂
  ∂!-initial ⟨ p ⟩ t = ∂-initial p t

-- "Derivative": x ∈ ∂ p t · s  iff  x ∈ p · t ∷ s.

mutual

  ∂ : ∀ {Tok R xs}
      (p : Parser Tok R xs) (t : Tok) → Parser Tok R (∂-initial p t)
  ∂ (return x)        t = fail
  ∂ fail              t = fail
  ∂ token             t = return t
  ∂ (p₁ ∣ p₂)         t = ∂ p₁ t ∣ ∂ p₂ t
  ∂ (nonempty p)      t = ∂ p t
  ∂ (cast eq p)       t = ∂ p t
  ∂ (f <$> p)         t = f <$> ∂ p t
  ∂ (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫) t = ⟨   ∂    p₁  t ⟩ ⊛ ♯? (♭ p₂)
  ∂ (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫) t = ⟪ ♯ ∂ (♭ p₁) t ⟫ ⊛ ♯? (♭ p₂)
  ∂ (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩) t = ⟨   ∂    p₁  t ⟩ ⊛ ♯?    p₂
                        ∣ ♯? (return⋆ (initial-set    p₁ )) ⊛ ⟨ ∂ p₂ t ⟩
  ∂ (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩) t = ⟪ ♯ ∂ (♭ p₁) t ⟫ ⊛ ♯?     p₂
                        ∣ ♯? (return⋆ (initial-set (♭ p₁))) ⊛ ⟨ ∂ p₂ t ⟩
  ∂ (p₁ >>= p₂)       t with initial-set p₁
  ∂ (p₁ >>= p₂)       t | []     = ∂ p₁ t >>= (λ x → ♯? (♭? (p₂ x)))
  ∂ (p₁ >>= p₂)       t | x ∷ xs = ∂ p₁ t >>= (λ x → ♯? (♭? (p₂ x)))
                                 ∣ return⋆ (x ∷ xs) >>= λ x → ⟨ ∂! (p₂ x) t ⟩
  ∂ (p₁ >>=! p₂)      t with initial-set (♭ p₁)
  ∂ (p₁ >>=! p₂)      t | []     = (♯ ∂ (♭ p₁) t) >>=! (λ x → ♯? (♭? (p₂ x)))
  ∂ (p₁ >>=! p₂)      t | x ∷ xs = (♯ ∂ (♭ p₁) t) >>=! (λ x → ♯? (♭? (p₂ x)))
                                 ∣ return⋆ (x ∷ xs) >>= λ x → ⟨ ∂! (p₂ x) t ⟩

  ∂! : ∀ {Tok R₁ R₂ xs y} {ys : List R₁}
       (p : ∞? (Parser Tok R₂ xs) (y ∷ ys)) (t : Tok) →
       Parser Tok R₂ (∂!-initial p t)
  ∂! ⟨ p ⟩ t = ∂ p t

-- Parsing: x ∈ parseComplete p s  iff  x ∈ p · s.

parseComplete : ∀ {Tok R xs} → Parser Tok R xs → List Tok → List R
parseComplete {xs = xs} p []      = xs
parseComplete           p (t ∷ s) = parseComplete (∂ p t) s
