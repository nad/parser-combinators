-- This code is based on "Parallel Parsing Processes" by Koen
-- Claessen.

-- This module is a variant of Parallel in which Parser uses mixed
-- induction/coinduction.

module Parallel2 {Tok : Set} where

open import Coinduction
open import Data.Bool
import Data.Bool.Properties as Bool
open import Algebra
open import Data.Product
open import Data.Function
import Data.List as List
open List using (List; []; _∷_)
open import Data.Vec using ([]; _∷_)
open import Data.Fin using (#_)
open import Category.Monad.State
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

------------------------------------------------------------------------
-- Boring lemma

private

  lem₁ : ∀ b₁ b₂ → b₁ ∨ b₂ ∧ b₁ ≡ b₁
  lem₁ b₁ b₂ = begin
    b₁ ∨ b₂ ∧ b₁  ≡⟨ cong (_∨_ b₁) (B.∧-comm b₂ b₁) ⟩
    b₁ ∨ b₁ ∧ b₂  ≡⟨ proj₁ B.absorptive b₁ b₂ ⟩
    b₁            ∎
    where module B = BooleanAlgebra Bool.booleanAlgebra

------------------------------------------------------------------------
-- Parser monad

P : Set → Set
P = StateT (List Tok) List

------------------------------------------------------------------------
-- Basic parsers (no CPS)

-- Note that the recursive argument of symbolBind is coinductive,
-- while that of returnPlus is inductive. An infinite choice is not
-- acceptable, but an infinite tree of potential parsers is fine.

data Parser (R : Set) : Bool → Set where
  symbolBind : {e : Tok → Bool} →
               (f : (x : Tok) → ∞ (Parser R (e x))) → Parser R false
  fail       : Parser R false
  returnPlus : ∀ {e} (x : R) (p : Parser R e) → Parser R true

parse : ∀ {R e} → Parser R e → P R
parse (symbolBind f)   []       = []
parse (symbolBind f)   (x ∷ xs) = parse (♭ (f x)) xs
parse fail             _        = []
parse (returnPlus x p) xs       = (x , xs) ∷ parse p xs

cast : ∀ {R e₁ e₂} → e₁ ≡ e₂ → Parser R e₁ → Parser R e₂
cast refl = id

return : ∀ {R} → R → Parser R true
return x = returnPlus x fail

module DirectImplementations where

  -- The definition of _∣_ is fine, but is the definition of _>>=_
  -- acceptable?

  infixl 1 _>>=_
  infixl 0 _∣_

  _∣_ : ∀ {R e₁ e₂} → Parser R e₁ → Parser R e₂ → Parser R (e₁ ∨ e₂)
  symbolBind f₁    ∣ symbolBind f₂    = symbolBind (λ x → ♯ (♭ (f₁ x) ∣ ♭ (f₂ x)))

  fail             ∣ p₂               = p₂
  symbolBind f₁    ∣ fail             = symbolBind f₁
  returnPlus x₁ p₁ ∣ fail             = returnPlus x₁ p₁

  returnPlus x₁ p₁ ∣ p₂               = returnPlus x₁ (p₁ ∣ p₂)
  symbolBind f₁    ∣ returnPlus x₂ p₂ = returnPlus x₂ (symbolBind f₁ ∣ p₂)

  _>>=_ : ∀ {R₁ R₂ e₁ e₂} →
          Parser R₁ e₁ → (R₁ → Parser R₂ e₂) → Parser R₂ (e₁ ∧ e₂)
  symbolBind f₁        >>= f₂ = symbolBind (λ x → ♯ (♭ (f₁ x) >>= f₂))
  fail                 >>= f₂ = fail
  returnPlus {e} x₁ p₁ >>= f₂ = cast (lem₁ _ e) (f₂ x₁ ∣ p₁ >>= f₂)

  -- Implementing _!>>=_ seems tricky.

  -- _!>>=_ : ∀ {R₁ R₂} {e₂ : R₁ → Bool} →
  --          Parser R₁ false → ((x : R₁) → Parser R₂ (e₂ x)) →
  --          Parser R₂ false
  -- symbolBind f !>>= p₂ = symbolBind (λ x → ♯ {!♭ (f x) !>>= p₂!})
  -- fail         !>>= p₂ = fail

module IndirectImplementations where

  -- Can _>>=_ be implemented by using the productivity trick?

  infixl 1 _>>=_
  infixl 0 _∣_

  data PProg : Set → Bool → Set1 where
    symbolBind : ∀ {R} {e : Tok → Bool} →
                 (f : (x : Tok) → ∞₁ (PProg R (e x))) → PProg R false
    fail       : ∀ {R} → PProg R false
    returnPlus : ∀ {R e} (x : R) (p : PProg R e) → PProg R true
    _∣_        : ∀ {R e₁ e₂}
                 (p₁ : PProg R e₁) (p₂ : PProg R e₂) → PProg R (e₁ ∨ e₂)
    _>>=_      : ∀ {R₁ R₂ e₁ e₂}
                 (p₁ : PProg R₁ e₁) (f₂ : R₁ → PProg R₂ e₂) →
                 PProg R₂ (e₁ ∧ e₂)

  data PWHNF (R : Set) : Bool → Set1 where
    symbolBind : {e : Tok → Bool} →
                 (f : (x : Tok) → PProg R (e x)) → PWHNF R false
    fail       : PWHNF R false
    returnPlus : ∀ {e} (x : R) (p : PWHNF R e) → PWHNF R true

  -- _∣_ is a program, so implementing whnf seems challenging.

  whnf : ∀ {R e} → PProg R e → PWHNF R e
  whnf (symbolBind f)   = symbolBind (λ x → ♭₁ (f x))
  whnf fail             = fail
  whnf (returnPlus x p) = returnPlus x (whnf p)

  whnf (p₁ ∣ p₂) with whnf p₁
  ... | fail              = whnf p₂
  ... | returnPlus x₁ p₁′ = returnPlus x₁ {!(p₁′ ∣ p₂)!} -- (p₁′ ∣ p₂)
  ... | symbolBind f₁     with whnf p₂
  ...   | symbolBind f₂     = symbolBind (λ x → f₁ x ∣ f₂ x)
  ...   | fail              = symbolBind f₁
  ...   | returnPlus x₂ p₂′ = returnPlus x₂ {!!} -- (symbolBind f₁ ∣ p₂′)

  whnf (p₁ >>= f₂) with whnf p₁
  ... | symbolBind f₁     = symbolBind (λ x → f₁ x >>= f₂)
  ... | fail              = fail
  ... | returnPlus x₁ p₁′ = {!f₂ x₁ ∣ p₁′ >>= f₂!}

  mutual

    value : ∀ {R e} → PWHNF R e → Parser R e
    value (symbolBind f)   = symbolBind (λ x → ♯ ⟦ f x ⟧)
    value fail             = fail
    value (returnPlus x p) = returnPlus x (value p)

    ⟦_⟧ : ∀ {R e} → PProg R e → Parser R e
    ⟦ p ⟧ = value (whnf p)
