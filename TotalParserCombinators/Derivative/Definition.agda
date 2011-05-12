------------------------------------------------------------------------
-- Brzozowski-style derivatives of parsers
------------------------------------------------------------------------

module TotalParserCombinators.Derivative.Definition where

open import Category.Monad
open import Coinduction
open import Data.List as List using (List; map)
import Data.Maybe; open Data.Maybe.Maybe
open import Level

open RawMonadPlus {f = zero} List.monadPlus
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

D-bag : ∀ {Tok R xs} → Tok → Parser Tok R xs → List R
D-bag t (return x)   = fail′
D-bag t fail         = fail′
D-bag t token        = return′ t
D-bag t (p₁ ∣ p₂)    = D-bag t p₁ ∣′ D-bag t p₂
D-bag t (nonempty p) = D-bag t p
D-bag t (cast eq p)  = D-bag t p
D-bag t (f <$> p)    = map f (D-bag t p)
D-bag t (p₁ ⊛ p₂)    with forced? p₁ | forced? p₂
... | just xs | nothing = D-bag t p₁ ⊛′ xs
... | just xs | just fs = D-bag t p₁ ⊛′ xs ∣′ fs ⊛′ D-bag t p₂
... | nothing | nothing = fail′
... | nothing | just fs =                     fs ⊛′ D-bag t p₂
D-bag t (p₁ >>= p₂)  with forced? p₁ | forced?′ p₂
... | just f  | nothing =  D-bag t p₁ >>=′ f
... | just f  | just xs = (D-bag t p₁ >>=′ f) ∣′ (xs >>=′ λ x → D-bag t (p₂ x))
... | nothing | nothing = fail′
... | nothing | just xs =                         xs >>=′ λ x → D-bag t (p₂ x)

-- "Derivative": x ∈ D t p · s  iff  x ∈ p · t ∷ s.

D : ∀ {Tok R xs}
    (t : Tok) (p : Parser Tok R xs) → Parser Tok R (D-bag t p)
D t (return x)   = fail
D t fail         = fail
D t token        = return t
D t (p₁ ∣ p₂)    = D t p₁ ∣ D t p₂
D t (nonempty p) = D t p
D t (cast eq p)  = D t p
D t (f <$> p)    = f <$> D t p
D t (p₁ ⊛ p₂)    with forced? p₁ | forced? p₂
... | just xs | nothing =   D t    p₁  ⊛ ♭ p₂
... | just xs | just fs =   D t    p₁  ⊛   p₂ ∣ return⋆ fs ⊛ D t p₂
... | nothing | nothing = ♯ D t (♭ p₁) ⊛ ♭ p₂
... | nothing | just fs = ♯ D t (♭ p₁) ⊛   p₂ ∣ return⋆ fs ⊛ D t p₂
D t (p₁ >>= p₂)  with forced? p₁ | forced?′ p₂
... | just f  | nothing = D t p₁ >>= (λ x → ♭ (p₂ x))
... | just f  | just xs = D t p₁ >>= (λ x →    p₂ x)
                        ∣ return⋆ xs >>= λ x → D t (p₂ x)
... | nothing | nothing = ♯ D t (♭ p₁) >>= (λ x → ♭ (p₂ x))
... | nothing | just xs = ♯ D t (♭ p₁) >>= (λ x →    p₂ x)
                        ∣ return⋆ xs >>= λ x → D t (p₂ x)
