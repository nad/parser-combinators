------------------------------------------------------------------------
-- Small library used by StructurallyRecursiveDescentParsing.Mixfix
------------------------------------------------------------------------

open import Relation.Binary

module StructurallyRecursiveDescentParsing.Mixfix.Lib
         (Token : DecSetoid)
         where

open DecSetoid Token using (_≟_; refl) renaming (carrier to Tok)

open import Coinduction
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷ʳ_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

open import StructurallyRecursiveDescentParsing.Coinduction
import StructurallyRecursiveDescentParsing.Parser as Parser
import StructurallyRecursiveDescentParsing.Simplified as Simplified
open Simplified hiding (⟦_⟧)
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (cast∈)

------------------------------------------------------------------------
-- Programs

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
infixr  5 _∥_

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
                         ParserProg false (List⁺ R)
  _between_ : ∀ {e R n}
              (p : ∞₁ (ParserProg e R)) (toks : Vec Tok (suc n)) →
              ParserProg false (Vec R n)
  _∥_       : ∀ {e₁ e₂ I i} {R : I → Set}
              (p₁ : ParserProg  e₁       (R i))
              (p₂ : ParserProg       e₂  (∃ R)) →
                    ParserProg (e₁ ∨ e₂) (∃ R)

-- Parses a given token (or, really, a given equivalence class of
-- tokens).

theToken : Tok → Parser Tok false Tok
theToken tok = token !>>= λ tok′ → ♯₁ ok tok′
  module TheToken where
  okIndex : Tok → Bool
  okIndex tok′ with tok ≟ tok′
  ... | yes _ = true
  ... | no  _ = false

  ok : (tok′ : Tok) → Parser Tok (okIndex tok′) Tok
  ok tok′ with tok ≟ tok′
  ... | yes _ = return tok′
  ... | no  _ = fail

-- Interprets the parser programs as parsers.

private
  infix 10 ♯′_

  ♯′_ : ∀ {A} → A → ∞₁ A
  ♯′ x = ♯₁ x

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
                               ⟦ p₂ ⟧ !>>= λ x → ♯′ return (f x)
⟦ _⊛_ {false}        p₁ p₂ ⟧ = ⟦ p₁ ⟧ !>>= λ f → ♯₁ ⟦ f <$> p₂ ⟧
⟦ _<$>_  {true}  f p       ⟧ = ⟦ p  ⟧ ?>>= λ x →    return (f x)
⟦ _<$>_  {false} f p       ⟧ = ⟦ p  ⟧ !>>= λ x → ♯′ return (f x)
⟦ p +                      ⟧ = ⟦ p  ⟧ !>>= λ x → ♯₁
                               ⟦ _∷_ x <$> p + ∣ return [ x ] ⟧
⟦ p between (t ∷ [])       ⟧ = theToken t !>>= λ _ → ♯′ return []
⟦ p between (t ∷ t′ ∷ ts)  ⟧ = theToken t !>>= λ _ → ♯₁
                                ⟦ _∷_ <$> ♭₁ p ⊛ (p between (t′ ∷ ts)) ⟧
⟦ _∥_ {true}  p₁ p₂        ⟧ = (⟦ p₁ ⟧ ?>>= λ x →    return (, x)) ∣ ⟦ p₂ ⟧
⟦ _∥_ {false} p₁ p₂        ⟧ = (⟦ p₁ ⟧ !>>= λ x → ♯′ return (, x)) ∣ ⟦ p₂ ⟧

⟦_⟧′ : ∀ {e R} → ParserProg e R → Parser.Parser Tok e R
⟦ p ⟧′ = Simplified.⟦_⟧ ⟦ p ⟧

------------------------------------------------------------------------
-- Semantics of the programs

-- This definition may seem unnecessary: why not simply define
--
--   x ⊕ s′ ∈⟦ p ⟧· s  =  x ⊕ s′ ∈ ⟦ p ⟧′ · s?
--
-- The reason is that it is hard for Agda to infer the value of p from
-- ⟦ p ⟧′ (note that ⟦_⟧′ is a function which evaluates). By using the
-- definition below this problem is avoided.

infix 4 _⊕_∈⟦_⟧·_

data _⊕_∈⟦_⟧·_ : ∀ {R e} →
                 R → List Tok → ParserProg e R → List Tok → Set1 where
  return     : ∀ {R} {x : R} {s} → x ⊕ s ∈⟦ return x ⟧· s
  token      : ∀ {x s} → x ⊕ s ∈⟦ token ⟧· x ∷ s
  ∣ˡ         : ∀ {R x e₁ e₂ s s₁}
                 {p₁ : ParserProg e₁ R} {p₂ : ParserProg e₂ R}
               (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
  ∣ʳ         : ∀ {R x e₂ s s₁} e₁
                 {p₁ : ParserProg e₁ R} {p₂ : ParserProg e₂ R}
               (x∈p₂ : x ⊕ s₁ ∈⟦ p₂ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
  _?>>=_     : ∀ {R₁ R₂ x y e₂ s s₁ s₂}
                 {p₁ : ParserProg true R₁} {p₂ : R₁ → ParserProg e₂ R₂}
               (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) (y∈p₂x : y ⊕ s₂ ∈⟦ p₂ x ⟧· s₁) →
               y ⊕ s₂ ∈⟦ p₁ ?>>= p₂ ⟧· s
  _!>>=_     : ∀ {R₁ R₂ x y} {e₂ : R₁ → Bool} {s s₁ s₂}
                 {p₁ : ParserProg false R₁}
                 {p₂ : (x : R₁) → ∞₁ (ParserProg (e₂ x) R₂)}
               (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) (y∈p₂x : y ⊕ s₂ ∈⟦ ♭₁ (p₂ x) ⟧· s₁) →
               y ⊕ s₂ ∈⟦ p₁ !>>= p₂ ⟧· s
  _⊛_        : ∀ {e₁ e₂ s s₁ s₂ R₁ R₂ f x}
                 {p₁ : ParserProg e₁ (R₁ → R₂)} {p₂ : ParserProg e₂ R₁}
               (f∈p₁ : f ⊕ s₁ ∈⟦ p₁ ⟧· s) (x∈p₂ : x ⊕ s₂ ∈⟦ p₂ ⟧· s₁) →
               f x ⊕ s₂ ∈⟦ p₁ ⊛ p₂ ⟧· s
  _<$>_      : ∀ {e s s′ R₁ R₂ x} (f : R₁ → R₂) {p : ParserProg e R₁}
               (x∈p : x ⊕ s′ ∈⟦ p ⟧· s) → f x ⊕ s′ ∈⟦ f <$> p ⟧· s
  +-[]       : ∀ {R x s s₁} {p : ParserProg false R}
               (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) → [ x ] ⊕ s₁ ∈⟦ p + ⟧· s
  +-∷        : ∀ {R x s s₁ s₂ xs} {p : ParserProg false R}
               (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) (xs∈p : xs ⊕ s₂ ∈⟦ p + ⟧· s₁) →
               x ∷ xs ⊕ s₂ ∈⟦ p + ⟧· s
  between-[] : ∀ {e R t s} {p : ∞₁ (ParserProg e R)} →
               [] ⊕ s ∈⟦ p between (t ∷ []) ⟧· t ∷ s
  between-∷  : ∀ {e R n t x xs s s₁ s₂}
                 {p : ∞₁ (ParserProg e R)} {ts : Vec Tok (suc n)} →
               (x∈p : x ⊕ s₁ ∈⟦ ♭₁ p ⟧· s)
               (xs∈⋯ : xs ⊕ s₂ ∈⟦ p between ts ⟧· s₁) →
               x ∷ xs ⊕ s₂ ∈⟦ p between (t ∷ ts) ⟧· t ∷ s
  ∥ˡ         : ∀ {e₁ e₂ I i} {R : I → Set} {x s s′}
                 {p₁ : ParserProg e₁ (R i)} {p₂ : ParserProg e₂ (∃ R)}
               (x∈p₁ : x ⊕ s′ ∈⟦ p₁ ⟧· s) → (, x) ⊕ s′ ∈⟦ p₁ ∥ p₂ ⟧· s
  ∥ʳ         : ∀ e₁ {e₂ I i} {R : I → Set} {x s s′}
                 {p₁ : ParserProg e₁ (R i)} {p₂ : ParserProg e₂ (∃ R)}
               (x∈p₂ : x ⊕ s′ ∈⟦ p₂ ⟧· s) → x ⊕ s′ ∈⟦ p₁ ∥ p₂ ⟧· s

-- The semantics is correct.

private

  <$>-lemma : ∀ {e s s′ R₁ R₂ x} (p : ParserProg e R₁) {f : R₁ → R₂} →
              x ⊕ s′ ∈ ⟦ p ⟧′ · s → f x ⊕ s′ ∈ ⟦ f <$> p ⟧′ · s
  <$>-lemma {true}  _ x∈p·s = cast (x∈p·s >>= return)
  <$>-lemma {false} _ x∈p·s =       x∈p·s >>= return

  ⊛-lemma : ∀ {e₁ e₂ s s₁ s₂ R₁ R₂ f x}
              {p₁ : ParserProg e₁ (R₁ → R₂)} {p₂ : ParserProg e₂ R₁} →
            f ⊕ s₁ ∈ ⟦ p₁ ⟧′ · s → x ⊕ s₂ ∈ ⟦ p₂ ⟧′ · s₁ →
            f x ⊕ s₂ ∈ ⟦ p₁ ⊛ p₂ ⟧′ · s
  ⊛-lemma {true}  {true}  {p₂ = p₂} f∈p₁ x∈p₂ = cast (f∈p₁ >>= <$>-lemma p₂ x∈p₂)
  ⊛-lemma {true}  {false} {p₂ = p₂} f∈p₁ x∈p₂ = cast (f∈p₁ >>= <$>-lemma p₂ x∈p₂)
  ⊛-lemma {false} {_}     {p₂ = p₂} f∈p₁ x∈p₂ =       f∈p₁ >>= <$>-lemma p₂ x∈p₂

  theToken-lemma : ∀ {t s} →
                   t ⊕ s ∈ Simplified.⟦_⟧ (theToken t) · t ∷ s
  theToken-lemma {t} {s} = token >>= ok-lemma
    where
    ok-lemma : t ⊕ s ∈ Simplified.⟦_⟧ (TheToken.ok t t) · s
    ok-lemma with t ≟ t
    ... | yes t≈t = return
    ... | no  t≉t with t≉t refl
    ...   | ()

correct : ∀ {R e x s s′} {p : ParserProg e R} →
          x ⊕ s′ ∈⟦ p ⟧· s → x ⊕ s′ ∈ ⟦ p ⟧′ · s
correct return                 = return
correct token                  = token
correct (∣ˡ x∈p₁)              = ∣ˡ (correct x∈p₁)
correct (∣ʳ e₁ x∈p₂)           = ∣ʳ e₁ (correct x∈p₂)
correct (x∈p₁ ?>>= y∈p₂x)      = cast (correct x∈p₁ >>= correct y∈p₂x)
correct (x∈p₁ !>>= y∈p₂x)      =       correct x∈p₁ >>= correct y∈p₂x
correct (f∈p₁ ⊛ x∈p₂)          = ⊛-lemma (correct f∈p₁) (correct x∈p₂)
correct (f <$> x∈p)            = <$>-lemma _ (correct x∈p)
correct (+-[] x∈p)             = correct x∈p >>= ∣ʳ false return
correct (+-∷ {p = p} x∈p xs∈p) = correct x∈p >>=
                                 ∣ˡ (<$>-lemma (p +) (correct xs∈p))
correct between-[]             = theToken-lemma >>= return
correct (between-∷ {p = p} {_ ∷ _} x∈p xs∈⋯) =
  theToken-lemma >>= ⊛-lemma (<$>-lemma _ (correct x∈p)) (correct xs∈⋯)
correct (∥ˡ {true}  {p₁ = p₁} x∈p₁) = ∣ˡ (<$>-lemma p₁ (correct x∈p₁))
correct (∥ˡ {false} {p₁ = p₁} x∈p₁) = ∣ˡ (<$>-lemma p₁ (correct x∈p₁))
correct (∥ʳ true  x∈p₂)             = ∣ʳ true  (correct x∈p₂)
correct (∥ʳ false x∈p₂)             = ∣ʳ false (correct x∈p₂)

-- Some lemmas.

+-∷ʳ : ∀ {R x s s₁ s₂ xs} {p : ParserProg false R} →
       xs ⊕ s₁ ∈⟦ p + ⟧· s → x ⊕ s₂ ∈⟦ p ⟧· s₁ →
       xs ∷ʳ x ⊕ s₂ ∈⟦ p + ⟧· s
+-∷ʳ (+-[] x∈p)     y∈p = +-∷ x∈p (+-[] y∈p)
+-∷ʳ (+-∷ x∈p xs∈p) y∈p = +-∷ x∈p (+-∷ʳ xs∈p y∈p)

cast∈ : ∀ {e R x₁ x₂ s s′} {p : ParserProg e R} →
        x₁ ≡ x₂ → x₁ ⊕ s′ ∈⟦ p ⟧· s → x₂ ⊕ s′ ∈⟦ p ⟧· s
cast∈ PropEq.refl x∈p = x∈p
