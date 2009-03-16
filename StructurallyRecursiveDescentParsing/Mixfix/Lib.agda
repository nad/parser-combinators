------------------------------------------------------------------------
-- Small library used by StructurallyRecursiveDescentParsing.Mixfix
------------------------------------------------------------------------

open import Relation.Binary

module StructurallyRecursiveDescentParsing.Mixfix.Lib
         (Token : DecSetoid)
         where

open DecSetoid Token using (_≟_) renaming (carrier to Tok)

open import Coinduction
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary

open import StructurallyRecursiveDescentParsing.Type

-- Agda's termination checker only accepts corecursive definitions if
-- they are /syntactically/ guarded by constructors. The following
-- small language of "parser programs" reifies a selection of parser
-- combinators as /constructors/. These constructors are then used in
-- StructurallyRecursiveDescentParsing.Mixfix in order to ensure that
-- Agda accepts the grammar defined there.

infix  55 _+
infixl 50 _⊛_ _<$>_
infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_

data ParserProg : Bool → Set → Set1 where
  return    : ∀ {R} (x : R) → ParserProg true R
  fail      : ∀ {R} → ParserProg false R
  token     : ParserProg false Tok
  _∣_       : ∀ {e₁ e₂ R}
              (p₁ : ParserProg  e₁       R)
              (p₂ : ParserProg       e₂  R) →
                    ParserProg (e₁ ∨ e₂) R
  _?>>=_    : ∀ {e₂ R₁ R₂}
              (p₁ :      ParserProg true R₁)
              (p₂ : R₁ → ParserProg e₂   R₂) →
                         ParserProg e₂   R₂
  _!>>=_    : ∀ {R₁ R₂} {e₂ : R₁ → Bool}
              (p₁ :                ParserProg false  R₁)
              (p₂ : (x : R₁) → ∞₁ (ParserProg (e₂ x) R₂)) →
                                   ParserProg false  R₂
  _⊛_       : ∀ {e₁ e₂ R₁ R₂}
              (p₁ : ParserProg  e₁      (R₁ → R₂))
              (p₂ : ParserProg       e₂  R₁) →
                    ParserProg (e₁ ∧ e₂) R₂
  _<$>_     : ∀ {e R₁ R₂} (f : R₁ → R₂)
              (p : ParserProg e R₁) →
                   ParserProg e R₂
  _+        : ∀ {R} (p : ParserProg false R) →
                         ParserProg false (List R)
  _between_ : ∀ {e R n}
              (p : ∞₁ (ParserProg e R)) (toks : Vec Tok (suc n)) →
              ParserProg false (Vec R n)

-- Parses a given token (or, really, a given equivalence class of
-- tokens).

theToken : Tok → Parser Tok false Tok
theToken tok = token !>>= λ tok′ → ♯₁ ok tok′
  where
  okIndex : Tok → Bool
  okIndex tok′ with tok ≟ tok′
  ... | yes _ = true
  ... | no  _ = false

  ok : (tok′ : Tok) → Parser Tok (okIndex tok′) Tok
  ok tok′ with tok ≟ tok′
  ... | yes _ = return tok′
  ... | no  _ = fail

-- Interprets the parser programs as parsers.

⟦_⟧ : ∀ {e R} → ParserProg e R → Parser Tok e R
⟦ return x                 ⟧ = return x
⟦ fail                     ⟧ = fail
⟦ token                    ⟧ = token
⟦ p₁ ∣ p₂                  ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ p₁ ?>>= p₂               ⟧ = ⟦ p₁ ⟧ ?>>= λ x →    ⟦     p₂ x  ⟧
⟦ p₁ !>>= p₂               ⟧ = ⟦ p₁ ⟧ !>>= λ x → ♯₁ ⟦ ♭₁ (p₂ x) ⟧
⟦ _⊛_ {true} {true}  p₁ p₂ ⟧ = ⟦ p₁ ⟧ ?>>= λ f →
                               ⟦ p₂ ⟧ ?>>= λ x →    return (f x)
⟦ _⊛_ {true} {false} p₁ p₂ ⟧ = ⟦ p₁ ⟧ ?>>= λ f →
                               ⟦ p₂ ⟧ !>>= λ x → ♯₁ return (f x)
⟦ _⊛_ {false}        p₁ p₂ ⟧ = ⟦ p₁ ⟧ !>>= λ f → ♯₁ ⟦ f <$> p₂ ⟧
⟦ _<$>_ {true}  f p        ⟧ = ⟦ p  ⟧ ?>>= λ x →    return (f x)
⟦ _<$>_ {false} f p        ⟧ = ⟦ p  ⟧ !>>= λ x → ♯₁ return (f x)
⟦ p +                      ⟧ = ⟦ p  ⟧ !>>= λ x → ♯₁
                               ⟦ _∷_ x <$> (p + ∣ return []) ⟧
⟦ p between (t ∷ [])       ⟧ = theToken t !>>= λ _ → ♯₁ return []
⟦ p between (t ∷ t′ ∷ ts)  ⟧ = theToken t !>>= λ _ → ♯₁
                               ⟦ _∷_ <$> ♭₁ p ⊛ (p between (t′ ∷ ts)) ⟧
