------------------------------------------------------------------------
-- Forcing of parsers (can be used for inspection/debugging purposes)
------------------------------------------------------------------------

{-# OPTIONS --termination-depth=2 #-}

module TotalParserCombinators.Force where

open import Coinduction
import Data.List.Properties as ListProp
open import Data.Maybe
open import Data.Nat
open import Function
import Relation.Binary.PropositionalEquality as P

open import TotalParserCombinators.Congruence
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Parser

-- force n p returns p, but with the first n layers of delay
-- constructors removed.

force : ∀ {Tok R xs} → ℕ → Parser Tok R xs → Parser Tok R xs
force zero    p                = p
force n       (return x)       = return x
force n       fail             = fail
force n       token            = token
force n       (p₁ ∣ p₂)        = force n p₁ ∣ force n p₂
force n       (f <$> p)        = f <$> force n p
force n       (nonempty p)     = nonempty (force n p)
force n       (cast xs₁≈xs₂ p) = cast xs₁≈xs₂ (force n p)
force (suc n) (p₁ ⊛ p₂)        with forced? p₁ | forced? p₂
... | just xs | nothing = force (suc n)   p₁  ⊛ force      n (♭ p₂)
... | just xs | just fs = force (suc n)   p₁  ⊛ force (suc n)   p₂
... | nothing | nothing = force      n (♭ p₁) ⊛ force      n (♭ p₂)
... | nothing | just fs =
  P.subst (Parser _ _) (ListProp.Applicative.right-zero fs) $
                          force      n (♭ p₁) ⊛ force (suc n)   p₂
force (suc n) (p₁ >>= p₂)      with forced? p₁ | forced?′ p₂
... | just f  | nothing = force (suc n)   p₁  >>= λ x → force      n (♭ (p₂ x))
... | just f  | just xs = force (suc n)   p₁  >>= λ x → force (suc n)   (p₂ x)
... | nothing | nothing = force      n (♭ p₁) >>= λ x → force      n (♭ (p₂ x))
... | nothing | just xs =
  P.subst (Parser _ _) (ListProp.Monad.right-zero xs) $
                          force n (♭ p₁) >>= λ x → force (suc n) (p₂ x)

-- force preserves the semantics of its argument.

correct : ∀ {Tok R xs} (n : ℕ) (p : Parser Tok R xs) → force n p ≅P p
correct zero    p                = p ∎
correct (suc n) (return x)       = return x ∎
correct (suc n) fail             = fail ∎
correct (suc n) token            = token ∎
correct (suc n) (p₁ ∣ p₂)        = correct (suc n) p₁ ∣ correct (suc n) p₂
correct (suc n) (f <$> p)        = (λ _ → P.refl) <$> correct (suc n) p
correct (suc n) (nonempty p)     = nonempty (correct (suc n) p)
correct (suc n) (cast xs₁≈xs₂ p) = cast (correct (suc n) p)
correct (suc n) (p₁ ⊛ p₂)        with forced? p₁ | forced? p₂
... | just xs | nothing = [ ○ - ○ - ○ - ◌ ] correct (suc n)   p₁  ⊛ correct      n (♭ p₂)
... | just xs | just fs = [ ○ - ○ - ○ - ○ ] correct (suc n)   p₁  ⊛ correct (suc n)   p₂
... | nothing | nothing = [ ○ - ◌ - ○ - ◌ ] correct      n (♭ p₁) ⊛ correct      n (♭ p₂)
... | nothing | just fs =
  P.subst (Parser _ _) lemma forced  ≅⟨ Subst.correct lemma ⟩
  forced                             ≅⟨ [ ○ - ◌ - ○ - ○ ] correct n (♭ p₁) ⊛ correct (suc n) p₂ ⟩
  p₁ ⊛ p₂                            ∎
  where
  lemma  = ListProp.Applicative.right-zero fs
  forced = force n (♭ p₁) ⊛ force (suc n) p₂
correct (suc n) (p₁ >>= p₂)      with forced? p₁ | forced?′ p₂
... | just f  | nothing = [ ○ - ○ - ○ - ◌ ] correct (suc n)   p₁  >>= λ x → correct      n (♭ (p₂ x))
... | just f  | just xs = [ ○ - ○ - ○ - ○ ] correct (suc n)   p₁  >>= λ x → correct (suc n)   (p₂ x)
... | nothing | nothing = [ ○ - ◌ - ○ - ◌ ] correct      n (♭ p₁) >>= λ x → correct      n (♭ (p₂ x))
... | nothing | just xs =
  P.subst (Parser _ _) lemma forced  ≅⟨ Subst.correct lemma ⟩
  forced                             ≅⟨ [ ○ - ◌ - ○ - ○ ] correct n (♭ p₁) >>= (λ x → correct (suc n) (p₂ x)) ⟩
  p₁ >>= p₂                          ∎
  where
  forced = force n (♭ p₁) >>= λ x → force (suc n) (p₂ x)
  lemma  = ListProp.Monad.right-zero xs
