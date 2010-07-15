------------------------------------------------------------------------
-- Brzozowski-style derivatives of parsers
------------------------------------------------------------------------

module TotalParserCombinators.BreadthFirst.Derivative where

open import Category.Monad
open import Coinduction
open import Data.List as List using (List; map); open List.List
open import Data.Maybe using (Maybe); open Data.Maybe.Maybe

open RawMonadPlus List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _⊛_    to _⊛′_
           ; _>>=_  to _>>=′_
           )

open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser

-- A function which calculates the index of the derivative.

∂-initial : ∀ {Tok R xs} → Parser Tok R xs → Tok → List R
∂-initial (return x)   t = fail′
∂-initial fail         t = fail′
∂-initial token        t = return′ t
∂-initial (p₁ ∣ p₂)    t = ∂-initial p₁ t ∣′ ∂-initial p₂ t
∂-initial (nonempty p) t = ∂-initial p t
∂-initial (cast eq p)  t = ∂-initial p t
∂-initial (f <$> p)    t = map f (∂-initial p t)
∂-initial (p₁ ⊛ p₂)    t with delayed? p₁ | delayed? p₂
... | just xs | nothing = ∂-initial p₁ t ⊛′ xs
... | just xs | just fs = ∂-initial p₁ t ⊛′ xs ∣′ fs ⊛′ ∂-initial p₂ t
... | nothing | nothing = fail′
... | nothing | just fs =                         fs ⊛′ ∂-initial p₂ t
∂-initial (p₁ >>= p₂)  t with delayed? p₁ | delayed?′ p₂
... | just f  | nothing =  ∂-initial p₁ t >>=′ f
... | just f  | just xs = (∂-initial p₁ t >>=′ f) ∣′
                          (xs >>=′ λ x → ∂-initial (p₂ x) t)
... | nothing | nothing = fail′
... | nothing | just xs =  xs >>=′ λ x → ∂-initial (p₂ x) t

-- "Derivative": x ∈ ∂ p t · s  iff  x ∈ p · t ∷ s.

∂ : ∀ {Tok R xs}
    (p : Parser Tok R xs) (t : Tok) → Parser Tok R (∂-initial p t)
∂ (return x)   t = fail
∂ fail         t = fail
∂ token        t = return t
∂ (p₁ ∣ p₂)    t = ∂ p₁ t ∣ ∂ p₂ t
∂ (nonempty p) t = ∂ p t
∂ (cast eq p)  t = ∂ p t
∂ (f <$> p)    t = f <$> ∂ p t
∂ (p₁ ⊛ p₂)    t with delayed? p₁ | delayed? p₂
... | just xs | nothing =   ∂    p₁  t ⊛ ♭ p₂
... | just xs | just fs =   ∂    p₁  t ⊛   p₂ ∣ return⋆ fs ⊛ ∂ p₂ t
... | nothing | nothing = ♯ ∂ (♭ p₁) t ⊛ ♭ p₂
... | nothing | just fs = ♯ ∂ (♭ p₁) t ⊛   p₂ ∣ return⋆ fs ⊛ ∂ p₂ t
∂ (p₁ >>= p₂)  t with delayed? p₁ | delayed?′ p₂
... | just f  | nothing = ∂ p₁ t >>= (λ x → ♭ (p₂ x))
... | just f  | just xs = ∂ p₁ t >>= (λ x →    p₂ x)
                        ∣ return⋆ xs >>= λ x → ∂ (p₂ x) t
... | nothing | nothing = ♯ ∂ (♭ p₁) t >>= (λ x → ♭ (p₂ x))
... | nothing | just xs = ♯ ∂ (♭ p₁) t >>= (λ x →    p₂ x)
                        ∣ return⋆ xs >>= λ x → ∂ (p₂ x) t

-- Parsing: x ∈ parseComplete p s  iff  x ∈ p · s.

parseComplete : ∀ {Tok R xs} → Parser Tok R xs → List Tok → List R
parseComplete {xs = xs} p []      = xs
parseComplete           p (t ∷ s) = parseComplete (∂ p t) s
