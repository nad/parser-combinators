------------------------------------------------------------------------
-- Small library used by StructurallyRecursiveDescentParsing.Mixfix
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Mixfix.Lib where

open import Coinduction
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷ʳ_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product
import Data.String as String
open import Relation.Binary
open DecSetoid String.decSetoid using (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import StructurallyRecursiveDescentParsing.Coinduction
import StructurallyRecursiveDescentParsing.Parser as Parser
import StructurallyRecursiveDescentParsing.Simplified as Simplified
open Simplified hiding (⟦_⟧)
open import StructurallyRecursiveDescentParsing.Simplified.Semantics
  hiding (cast∈; sound; complete)
open import StructurallyRecursiveDescentParsing.Mixfix.Expr
  using (NamePart)

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
infixl  5 _∣_
infixr  5 _∥_

data ParserProg : Set → Set1 where
  fail      : ∀ {R} → ParserProg R
  _∣_       : ∀ {R}
              (p₁ : ParserProg R)
              (p₂ : ParserProg R) →
                    ParserProg R
  _⊛_       : ∀ {R₁ R₂}
              (p₁ : ParserProg (R₁ → R₂))
              (p₂ : ParserProg R₁) →
                    ParserProg R₂
  _<$>_     : ∀ {R₁ R₂} (f : R₁ → R₂)
              (p : ParserProg R₁) →
                   ParserProg R₂
  _+        : ∀ {R} (p : ParserProg R) →
                         ParserProg (List⁺ R)
  _between_ : ∀ {R n}
              (p : ∞₁ (ParserProg R)) (toks : Vec NamePart (suc n)) →
              ParserProg (Vec R n)
  _∥_       : ∀ {I i} {R : I → Set}
              (p₁ : ParserProg (R i))
              (p₂ : ParserProg (∃ R)) →
                    ParserProg (∃ R)

-- Parses a given token (or, really, a given equivalence class of
-- tokens).

theToken : NamePart → Parser NamePart false NamePart
theToken tok = token !>>= λ tok′ → ♯₁ ok tok′
  module TheToken where
  okIndex : NamePart → Bool
  okIndex tok′ with tok ≟ tok′
  ... | yes _ = true
  ... | no  _ = false

  ok : (tok′ : NamePart) → Parser NamePart (okIndex tok′) NamePart
  ok tok′ with tok ≟ tok′
  ... | yes _ = return tok′
  ... | no  _ = fail

-- Interprets the parser programs as parsers.

private
  infix 10 ♯′_

  ♯′_ : ∀ {A} → A → ∞₁ A
  ♯′ x = ♯₁ x

⟦_⟧ : ∀ {R} → ParserProg R → Parser NamePart false R
⟦ fail                    ⟧ = fail
⟦ p₁ ∣ p₂                 ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ p₁ ⊛ p₂                 ⟧ = ⟦ p₁ ⟧ !>>= λ f → ♯₁ ⟦ f <$> p₂ ⟧
⟦ f <$> p                 ⟧ = ⟦ p  ⟧ !>>= λ x → ♯′ return (f x)
⟦ p +                     ⟧ = ⟦ p  ⟧ !>>= λ x → ♯₁
                              (⟦ _∷_ x <$> p + ⟧ ∣ return [ x ])
⟦ p between (t ∷ [])      ⟧ = theToken t !>>= λ _ → ♯′ return []
⟦ p between (t ∷ t′ ∷ ts) ⟧ = theToken t !>>= λ _ → ♯₁
                              ⟦ _∷_ <$> ♭₁ p ⊛ (p between (t′ ∷ ts)) ⟧
⟦ p₁ ∥ p₂                 ⟧ = (⟦ p₁ ⟧ !>>= λ x → ♯′ return (, x)) ∣ ⟦ p₂ ⟧

------------------------------------------------------------------------
-- Semantics of the programs

-- This definition may seem unnecessary: why not simply define
--
--   x ⊕ s′ ∈⟦ p ⟧· s  =  x ⊕ s′ ∈ ⟦ p ⟧ · s?
--
-- The reason is that it is hard for Agda to infer the value of p from
-- ⟦ p ⟧ (note that ⟦_⟧ is a function which evaluates). By using the
-- definition below this problem is avoided.

infix 4 _⊕_∈⟦_⟧·_

data _⊕_∈⟦_⟧·_ : ∀ {R} →
                 R → List NamePart → ParserProg R → List NamePart → Set1 where
  ∣ˡ         : ∀ {R x s s₁}
                 {p₁ : ParserProg R} {p₂ : ParserProg R}
               (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
  ∣ʳ         : ∀ {R x s s₁}
                 {p₁ : ParserProg R} {p₂ : ParserProg R}
               (x∈p₂ : x ⊕ s₁ ∈⟦ p₂ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
  _⊛_        : ∀ {s s₁ s₂ R₁ R₂ f x}
                 {p₁ : ParserProg (R₁ → R₂)} {p₂ : ParserProg R₁}
               (f∈p₁ : f ⊕ s₁ ∈⟦ p₁ ⟧· s) (x∈p₂ : x ⊕ s₂ ∈⟦ p₂ ⟧· s₁) →
               f x ⊕ s₂ ∈⟦ p₁ ⊛ p₂ ⟧· s
  _<$>_      : ∀ {s s′ R₁ R₂ x} (f : R₁ → R₂) {p : ParserProg R₁}
               (x∈p : x ⊕ s′ ∈⟦ p ⟧· s) → f x ⊕ s′ ∈⟦ f <$> p ⟧· s
  +-[]       : ∀ {R x s s₁} {p : ParserProg R}
               (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) → [ x ] ⊕ s₁ ∈⟦ p + ⟧· s
  +-∷        : ∀ {R x s s₁ s₂ xs} {p : ParserProg R}
               (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) (xs∈p : xs ⊕ s₂ ∈⟦ p + ⟧· s₁) →
               x ∷ xs ⊕ s₂ ∈⟦ p + ⟧· s
  between-[] : ∀ {R t s} {p : ∞₁ (ParserProg R)} →
               [] ⊕ s ∈⟦ p between (t ∷ []) ⟧· t ∷ s
  between-∷  : ∀ {R n t x xs s s₁ s₂}
                 {p : ∞₁ (ParserProg R)} {ts : Vec NamePart (suc n)}
               (x∈p : x ⊕ s₁ ∈⟦ ♭₁ p ⟧· s)
               (xs∈⋯ : xs ⊕ s₂ ∈⟦ p between ts ⟧· s₁) →
               x ∷ xs ⊕ s₂ ∈⟦ p between (t ∷ ts) ⟧· t ∷ s
  ∥ˡ         : ∀ {I i} {R : I → Set} {x s s′}
                 {p₁ : ParserProg (R i)}
                 {p₂ : ParserProg (∃ R)}
               (x∈p₁ : x ⊕ s′ ∈⟦ p₁ ⟧· s) → (, x) ⊕ s′ ∈⟦ p₁ ∥ p₂ ⟧· s
  ∥ʳ         : ∀ {I i} {R : I → Set} {x s s′}
                 {p₁ : ParserProg (R i)}
                 {p₂ : ParserProg (∃ R)}
               (x∈p₂ : x ⊕ s′ ∈⟦ p₂ ⟧· s) → x ⊕ s′ ∈⟦ p₁ ∥ p₂ ⟧· s

-- The semantics is correct.

private

  ⊛-complete : ∀ {s s₁ s₂ R₁ R₂ f x}
                 {p₁ : ParserProg (R₁ → R₂)} {p₂ : ParserProg R₁} →
               f ⊕ s₁ ∈ ⟦ p₁ ⟧ · s → x ⊕ s₂ ∈ ⟦ p₂ ⟧ · s₁ →
               f x ⊕ s₂ ∈ ⟦ p₁ ⊛ p₂ ⟧ · s
  ⊛-complete f∈p₁ x∈p₂ = f∈p₁ !>>= (x∈p₂ !>>= return)

  theToken-sound : ∀ {t t′ s₁ s} →
                   t′ ⊕ s₁ ∈ theToken t · s →
                   t ≡ t′ × s ≡ t′ ∷ s₁
  theToken-sound {t} (_!>>=_ {x = t″} token t′∈) with t ≟ t″
  theToken-sound (token !>>= return) | yes t≈t″ = (t≈t″ , refl)
  theToken-sound (token !>>= ())     | no  t≉t″

  theToken-complete : ∀ {t s} → t ⊕ s ∈ theToken t · t ∷ s
  theToken-complete {t} {s} = token !>>= ok-lemma
    where
    ok-lemma : t ⊕ s ∈ TheToken.ok t t · s
    ok-lemma with t ≟ t
    ... | yes refl = return
    ... | no  t≢t  with t≢t refl
    ...   | ()

sound : ∀ {R x s s′} {p : ParserProg R} →
        x ⊕ s′ ∈⟦ p ⟧· s → x ⊕ s′ ∈ ⟦ p ⟧ · s
sound (∣ˡ x∈p₁)      = ∣ˡ       (sound x∈p₁)
sound (∣ʳ x∈p₂)      = ∣ʳ false (sound x∈p₂)
sound (f∈p₁ ⊛ x∈p₂)  = ⊛-complete (sound f∈p₁) (sound x∈p₂)
sound (f <$> x∈p)    = sound x∈p !>>= return
sound (+-[] x∈p)     = sound x∈p !>>= ∣ʳ false return
sound (+-∷ x∈p xs∈p) = sound x∈p !>>= ∣ˡ (sound xs∈p !>>= return)
sound (∥ˡ x∈p₁)      = ∣ˡ (sound x∈p₁ !>>= return)
sound (∥ʳ x∈p₂)      = ∣ʳ false (sound x∈p₂)
sound between-[]     = theToken-complete !>>= return
sound (between-∷ {ts = _ ∷ _} x∈p xs∈⋯) =
  theToken-complete !>>=
  ⊛-complete (sound x∈p !>>= return) (sound xs∈⋯)

complete : ∀ {R x s s′} (p : ParserProg R) →
           x ⊕ s′ ∈ ⟦ p ⟧ · s → x ⊕ s′ ∈⟦ p ⟧· s
complete fail      ()

complete (p₁ ∣ p₂) (∣ˡ        x∈p₁) = ∣ˡ (complete p₁ x∈p₁)
complete (p₁ ∣ p₂) (∣ʳ .false x∈p₂) = ∣ʳ (complete p₂ x∈p₂)

complete (p₁ ⊛ p₂) (f∈p₁ !>>= (y∈p₂ !>>= return)) =
  complete p₁ f∈p₁ ⊛ complete p₂ y∈p₂

complete (f <$> p) (x∈p !>>= return) = f <$> complete p x∈p

complete (p +) (x∈p !>>= ∣ˡ (xs∈p+ !>>= return)) = +-∷  (complete p x∈p) (complete (p +) xs∈p+)
complete (p +) (x∈p !>>= ∣ʳ .false return)       = +-[] (complete p x∈p)

complete (p between (t ∷ [])) (t∈ !>>= return) with theToken-sound t∈
... | (refl , refl) = between-[]
complete (p between (t ∷ t′ ∷ ts))
         (t∈ !>>= (x∈p !>>= return !>>= (xs∈ !>>= return))) with theToken-sound t∈
... | (refl , refl) =
  between-∷ (complete (♭₁ p) x∈p) (complete (p between (t′ ∷ ts)) xs∈)

complete (p₁ ∥ p₂) (∣ˡ (x∈p₁ !>>= return)) = ∥ˡ (complete p₁ x∈p₁)
complete (p₁ ∥ p₂) (∣ʳ .false x∈p₂)        = ∥ʳ (complete p₂ x∈p₂)

-- Some lemmas.

+-∷ʳ : ∀ {R x s s₁ s₂ xs} {p : ParserProg R} →
       xs ⊕ s₁ ∈⟦ p + ⟧· s → x ⊕ s₂ ∈⟦ p ⟧· s₁ →
       xs ∷ʳ x ⊕ s₂ ∈⟦ p + ⟧· s
+-∷ʳ (+-[] x∈p)     y∈p = +-∷ x∈p (+-[] y∈p)
+-∷ʳ (+-∷ x∈p xs∈p) y∈p = +-∷ x∈p (+-∷ʳ xs∈p y∈p)

cast∈ : ∀ {R x₁ x₂ s s′} {p : ParserProg R} →
        x₁ ≡ x₂ → x₁ ⊕ s′ ∈⟦ p ⟧· s → x₂ ⊕ s′ ∈⟦ p ⟧· s
cast∈ refl x∈p = x∈p
