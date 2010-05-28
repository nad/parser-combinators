------------------------------------------------------------------------
-- Small parser combinator library used by Mixfix.Cyclic.Grammar
------------------------------------------------------------------------

module Mixfix.Cyclic.Lib where

open import Algebra
open import Coinduction
open import Function using (const)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List as List using (List; []; _∷_; _++_)
private module LM {A : Set} = Monoid (List.monoid A)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product
import Data.String as String
open import Relation.Binary
open DecSetoid String.decSetoid using (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

open import TotalParserCombinators.Coinduction hiding (maybe)
open import TotalParserCombinators.Parser
import TotalParserCombinators.Lib as Lib
open import TotalParserCombinators.Semantics as Sem
open import TotalParserCombinators.Semantics.Continuation as ContSem
  hiding (sound; complete)
open import Mixfix.Operator using (NamePart)

private
  open module Tok = Lib.Token NamePart _≟_ using (tok)

------------------------------------------------------------------------
-- Programs

-- Agda's termination checker only accepts corecursive definitions if
-- they are /syntactically/ guarded by constructors. The following
-- small language of "parser programs" reifies a selection of parser
-- combinators as /constructors/. These constructors are then used in
-- Mixfix.Cyclic.Grammar in order to ensure that Agda accepts the
-- grammars defined there.

infix  55 _+
infixl 50 _⊛_ _⊛∞_ _<$>_
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
  _⊛∞_      : ∀ {R₁ R₂}
              (p₁ : ∞ (ParserProg (R₁ → R₂)))
              (p₂ : ∞ (ParserProg R₁)) →
                       ParserProg R₂
  _<$>_     : ∀ {R₁ R₂} (f : R₁ → R₂)
              (p : ParserProg R₁) →
                   ParserProg R₂
  _+        : ∀ {R} (p : ParserProg R) →
                         ParserProg (List⁺ R)
  _between_ : ∀ {R n}
              (p : ∞ (ParserProg R)) (toks : Vec NamePart (1 + n)) →
              ParserProg (Vec R n)
  _∥_       : ∀ {I i} {R : I → Set}
              (p₁ : ParserProg (R i))
              (p₂ : ParserProg (∃ R)) →
                    ParserProg (∃ R)

-- Interprets the parser programs as parsers.

⟦_⟧ : ∀ {R} → ParserProg R → Parser NamePart R []
⟦ fail               ⟧ = fail
⟦ p₁ ∣ p₂            ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ p₁ ⊛  p₂           ⟧ = ⟪ ♯ ⟦   p₁ ⟧ ⟫ ⊛ ⟪ ♯ ⟦   p₂ ⟧ ⟫
⟦ p₁ ⊛∞ p₂           ⟧ = ⟪ ♯ ⟦ ♭ p₁ ⟧ ⟫ ⊛ ⟪ ♯ ⟦ ♭ p₂ ⟧ ⟫
⟦ f <$> p            ⟧ = f <$> ⟦ p ⟧
⟦ p +                ⟧ = ⟨ (λ x → maybe (_∷_ x) [ x ]) <$> ⟦ p ⟧ ⟩ ⊛
                         ⟪ ♯ (⟦ just <$> p + ⟧ ∣ return nothing) ⟫
⟦ p between (t ∷ []) ⟧ = const [] <$> tok t
⟦ p between
       (t ∷ t′ ∷ ts) ⟧ = ⟪ ♯ (♯? (const _∷_ <$> tok t) ⊛
                         ⟪ ♯ ⟦ ♭ p ⟧ ⟫) ⟫ ⊛
                         ⟪ ♯ ⟦ p between (t′ ∷ ts) ⟧ ⟫
⟦ p₁ ∥ p₂            ⟧ = ,_ <$> ⟦ p₁ ⟧
                       ∣        ⟦ p₂ ⟧

------------------------------------------------------------------------
-- Semantics of the programs

module Semantics where

  -- This definition may seem unnecessary: why not simply define
  --
  --   x ∈⟦ p ⟧· s  =  x ∈ ⟦ p ⟧ · s?
  --
  -- One reason is that it is hard for Agda to infer the value of p
  -- from ⟦ p ⟧ (note that ⟦_⟧ is a function which evaluates). By
  -- using the definition below this problem is avoided. A more
  -- important reason may be that the definition below ensures that
  -- the details of ⟦_⟧ do not need to be understood.

  infix  60 <$>_
  infixl 50 _⊛_
  infix  4  _∈⟦_⟧·_

  data _∈⟦_⟧·_ : ∀ {R} → R → ParserProg R → List NamePart → Set₁ where
    ∣ˡ         : ∀ {R x s}
                   {p₁ : ParserProg R} {p₂ : ParserProg R}
                 (x∈p₁ : x ∈⟦ p₁ ⟧· s) → x ∈⟦ p₁ ∣ p₂ ⟧· s
    ∣ʳ         : ∀ {R x s}
                   {p₁ : ParserProg R} {p₂ : ParserProg R}
                 (x∈p₂ : x ∈⟦ p₂ ⟧· s) → x ∈⟦ p₁ ∣ p₂ ⟧· s
    _⊛_        : ∀ {s₁ s₂ R₁ R₂ f x}
                   {p₁ : ParserProg (R₁ → R₂)}
                   {p₂ : ParserProg R₁}
                 (f∈p₁ : f ∈⟦ p₁ ⟧· s₁)
                 (x∈p₂ : x ∈⟦ p₂ ⟧· s₂) →
                 f x ∈⟦ p₁ ⊛ p₂ ⟧· s₁ ++ s₂
    _⊛∞_       : ∀ {s₁ s₂ R₁ R₂ f x}
                   {p₁ : ∞ (ParserProg (R₁ → R₂))}
                   {p₂ : ∞ (ParserProg R₁)}
                 (f∈p₁ : f ∈⟦ ♭ p₁ ⟧· s₁)
                 (x∈p₂ : x ∈⟦ ♭ p₂ ⟧· s₂) →
                 f x ∈⟦ p₁ ⊛∞ p₂ ⟧· s₁ ++ s₂
    <$>_       : ∀ {s R₁ R₂ x} {f : R₁ → R₂} {p : ParserProg R₁}
                 (x∈p : x ∈⟦ p ⟧· s) → f x ∈⟦ f <$> p ⟧· s
    +-[]       : ∀ {R x s} {p : ParserProg R}
                 (x∈p : x ∈⟦ p ⟧· s) → [ x ] ∈⟦ p + ⟧· s
    +-∷        : ∀ {R x s₁ s₂ xs} {p : ParserProg R}
                 (x∈p : x ∈⟦ p ⟧· s₁) (xs∈p : xs ∈⟦ p + ⟧· s₂) →
                 x ∷ xs ∈⟦ p + ⟧· s₁ ++ s₂
    between-[] : ∀ {R t} {p : ∞ (ParserProg R)} →
                 [] ∈⟦ p between (t ∷ []) ⟧· t ∷ []
    between-∷  : ∀ {R n t x xs s₁ s₂}
                   {p : ∞ (ParserProg R)} {ts : Vec NamePart (suc n)}
                 (x∈p : x ∈⟦ ♭ p ⟧· s₁)
                 (xs∈⋯ : xs ∈⟦ p between ts ⟧· s₂) →
                 x ∷ xs ∈⟦ p between (t ∷ ts) ⟧· t ∷ s₁ ++ s₂
    ∥ˡ         : ∀ {I i} {R : I → Set} {x s}
                   {p₁ : ParserProg (R i)}
                   {p₂ : ParserProg (∃ R)}
                 (x∈p₁ : x ∈⟦ p₁ ⟧· s) → (, x) ∈⟦ p₁ ∥ p₂ ⟧· s
    ∥ʳ         : ∀ {I i} {R : I → Set} {x s}
                   {p₁ : ParserProg (R i)}
                   {p₂ : ParserProg (∃ R)}
                 (x∈p₂ : x ∈⟦ p₂ ⟧· s) → x ∈⟦ p₁ ∥ p₂ ⟧· s

  -- The semantics is correct. (Note that this proof only establishes
  -- language equivalence, not parser equivalence; see
  -- TotalParserCombinators.Semantics.)

  sound : ∀ {R x s} {p : ParserProg R} →
          x ∈⟦ p ⟧· s → x ∈ ⟦ p ⟧ · s
  sound (∣ˡ x∈p₁)      = ∣ˡ    (sound x∈p₁)
  sound (∣ʳ x∈p₂)      = ∣ʳ [] (sound x∈p₂)
  sound (f∈p₁ ⊛  x∈p₂) = sound f∈p₁ ⊛ sound x∈p₂
  sound (f∈p₁ ⊛∞ x∈p₂) = sound f∈p₁ ⊛ sound x∈p₂
  sound (<$> x∈p)      = <$> sound x∈p
  sound (+-[] x∈p)     = cast∈ refl refl (proj₂ LM.identity _)
                           (<$> sound x∈p ⊛ ∣ʳ [] return)
  sound (+-∷ x∈p xs∈p) = _⊛_ {xs = _ ∷ []} (<$> sound x∈p)
                                           (∣ˡ (<$> sound xs∈p))
  sound (∥ˡ x∈p₁)      = ∣ˡ {x = (, _)} (<$> sound x∈p₁)
  sound (∥ʳ x∈p₂)      = ∣ʳ [] (sound x∈p₂)
  sound between-[]     = <$> Tok.complete
  sound (between-∷ {ts = _ ∷ _} x∈p xs∈⋯) =
    <$> Tok.complete ⊛ sound x∈p ⊛ sound xs∈⋯

  complete : ∀ {R x s} (p : ParserProg R) →
             x ∈ ⟦ p ⟧ · s → x ∈⟦ p ⟧· s
  complete fail      ()

  complete (p₁ ∣ p₂) (∣ˡ     x∈p₁) = ∣ˡ (complete p₁ x∈p₁)
  complete (p₁ ∣ p₂) (∣ʳ .[] x∈p₂) = ∣ʳ (complete p₂ x∈p₂)

  complete (p₁ ⊛  p₂) (f∈p₁ ⊛ y∈p₂) = complete    p₁  f∈p₁ ⊛  complete    p₂  y∈p₂
  complete (p₁ ⊛∞ p₂) (f∈p₁ ⊛ y∈p₂) = complete (♭ p₁) f∈p₁ ⊛∞ complete (♭ p₂) y∈p₂

  complete (f <$> p) (<$> x∈p) = <$> complete p x∈p

  complete (p +) (<$> x∈p ⊛ ∣ˡ (<$> xs∈p+)) =
    +-∷ (complete p x∈p) (complete (p +) xs∈p+)
  complete (p +) (_⊛_ {s₁ = s} (<$> x∈p) (∣ʳ .[] return))
    with s ++ [] | proj₂ LM.identity s
  ... | .s | refl = +-[] (complete p x∈p)

  complete (p between (t ∷ [])) (<$> t∈) with Tok.sound t∈
  ... | (refl , refl) = between-[]
  complete (p between (t ∷ t′ ∷ ts)) (<$> t∈ ⊛ x∈p ⊛ xs∈)
    with Tok.sound t∈
  ... | (refl , refl) =
    between-∷ (complete (♭ p) x∈p) (complete (p between (t′ ∷ ts)) xs∈)

  complete (p₁ ∥ p₂) (∣ˡ (<$> x∈p₁)) = ∥ˡ (complete p₁ x∈p₁)
  complete (p₁ ∥ p₂) (∣ʳ .[] x∈p₂)   = ∥ʳ (complete p₂ x∈p₂)

------------------------------------------------------------------------
-- A variant of the semantics

-- The alternative semantics defined below may be slightly harder to
-- understand, but it is (language) equivalent to the one above, and
-- it simplifies the proof in Mixfix.Cyclic.Show.

module Semantics-⊕ where

  infix  60 <$>_
  infixl 50 _⊛_
  infix  4  _⊕_∈⟦_⟧·_

  data _⊕_∈⟦_⟧·_ : ∀ {R} →
                   R → List NamePart →
                   ParserProg R → List NamePart → Set₁ where
    ∣ˡ         : ∀ {R x s s₁}
                   {p₁ : ParserProg R} {p₂ : ParserProg R}
                 (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
    ∣ʳ         : ∀ {R x s s₁}
                   {p₁ : ParserProg R} {p₂ : ParserProg R}
                 (x∈p₂ : x ⊕ s₁ ∈⟦ p₂ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
    _⊛_        : ∀ {s s₁ s₂ R₁ R₂ f x}
                   {p₁ : ParserProg (R₁ → R₂)}
                   {p₂ : ParserProg R₁}
                 (f∈p₁ : f ⊕ s₁ ∈⟦ p₁ ⟧· s)
                 (x∈p₂ : x ⊕ s₂ ∈⟦ p₂ ⟧· s₁) →
                 f x ⊕ s₂ ∈⟦ p₁ ⊛ p₂ ⟧· s
    _⊛∞_       : ∀ {s s₁ s₂ R₁ R₂ f x}
                   {p₁ : ∞ (ParserProg (R₁ → R₂))}
                   {p₂ : ∞ (ParserProg R₁)}
                 (f∈p₁ : f ⊕ s₁ ∈⟦ ♭ p₁ ⟧· s)
                 (x∈p₂ : x ⊕ s₂ ∈⟦ ♭ p₂ ⟧· s₁) →
                 f x ⊕ s₂ ∈⟦ p₁ ⊛∞ p₂ ⟧· s
    <$>_       : ∀ {s s′ R₁ R₂ x} {f : R₁ → R₂} {p : ParserProg R₁}
                 (x∈p : x ⊕ s′ ∈⟦ p ⟧· s) → f x ⊕ s′ ∈⟦ f <$> p ⟧· s
    +-[]       : ∀ {R x s s₁} {p : ParserProg R}
                 (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) → [ x ] ⊕ s₁ ∈⟦ p + ⟧· s
    +-∷        : ∀ {R x s s₁ s₂ xs} {p : ParserProg R}
                 (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) (xs∈p : xs ⊕ s₂ ∈⟦ p + ⟧· s₁) →
                 x ∷ xs ⊕ s₂ ∈⟦ p + ⟧· s
    between-[] : ∀ {R t s} {p : ∞ (ParserProg R)} →
                 [] ⊕ s ∈⟦ p between (t ∷ []) ⟧· t ∷ s
    between-∷  : ∀ {R n t x xs s s₁ s₂}
                   {p : ∞ (ParserProg R)} {ts : Vec NamePart (suc n)}
                 (x∈p : x ⊕ s₁ ∈⟦ ♭ p ⟧· s)
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

  tok-sound : ∀ {t t′ s₁ s} →
              t′ ⊕ s₁ ∈ tok t · s →
              t ≡ t′ × s ≡ t′ ∷ s₁
  tok-sound     ∈ with ContSem.sound′ ∈
  tok-sound     ∈ | (s         , refl , ∈′) with Tok.sound ∈′
  tok-sound {t} ∈ | (.(t ∷ []) , refl , ∈′) | (refl , refl) = (refl , refl)

  tok-complete : ∀ {t s} → t ⊕ s ∈ tok t · t ∷ s
  tok-complete = ContSem.complete′ (_ , refl , Tok.complete)

  sound : ∀ {R x s s′} {p : ParserProg R} →
          x ⊕ s′ ∈⟦ p ⟧· s → x ⊕ s′ ∈ ⟦ p ⟧ · s
  sound (∣ˡ x∈p₁)      = ∣ˡ    (sound x∈p₁)
  sound (∣ʳ x∈p₂)      = ∣ʳ [] (sound x∈p₂)
  sound (f∈p₁ ⊛  x∈p₂) = sound f∈p₁ ⊛ sound x∈p₂
  sound (f∈p₁ ⊛∞ x∈p₂) = sound f∈p₁ ⊛ sound x∈p₂
  sound (<$> x∈p)      = <$> sound x∈p
  sound (+-[] x∈p)     = <$> sound x∈p ⊛ ∣ʳ [] return
  sound (+-∷ x∈p xs∈p) = _⊛_ {xs = _ ∷ []} (<$> sound x∈p)
                                           (∣ˡ (<$> sound xs∈p))
  sound (∥ˡ x∈p₁)      = ∣ˡ {x = (, _)} (<$> sound x∈p₁)
  sound (∥ʳ x∈p₂)      = ∣ʳ [] (sound x∈p₂)
  sound between-[]     = <$> tok-complete
  sound (between-∷ {ts = _ ∷ _} x∈p xs∈⋯) =
    <$> tok-complete ⊛ sound x∈p ⊛ sound xs∈⋯

  complete : ∀ {R x s s′} (p : ParserProg R) →
             x ⊕ s′ ∈ ⟦ p ⟧ · s → x ⊕ s′ ∈⟦ p ⟧· s
  complete fail      ()

  complete (p₁ ∣ p₂) (∣ˡ     x∈p₁) = ∣ˡ (complete p₁ x∈p₁)
  complete (p₁ ∣ p₂) (∣ʳ .[] x∈p₂) = ∣ʳ (complete p₂ x∈p₂)

  complete (p₁ ⊛  p₂) (f∈p₁ ⊛ y∈p₂) = complete    p₁  f∈p₁ ⊛  complete    p₂  y∈p₂
  complete (p₁ ⊛∞ p₂) (f∈p₁ ⊛ y∈p₂) = complete (♭ p₁) f∈p₁ ⊛∞ complete (♭ p₂) y∈p₂

  complete (f <$> p) (<$> x∈p) = <$> complete p x∈p

  complete (p +) (<$> x∈p ⊛ ∣ˡ (<$> xs∈p+)) = +-∷  (complete p x∈p) (complete (p +) xs∈p+)
  complete (p +) (<$> x∈p ⊛ ∣ʳ .[] return)  = +-[] (complete p x∈p)

  complete (p between (t ∷ [])) (<$> t∈) with tok-sound t∈
  ... | (refl , refl) = between-[]
  complete (p between (t ∷ t′ ∷ ts)) (<$> t∈ ⊛ x∈p ⊛ xs∈)
    with tok-sound t∈
  ... | (refl , refl) =
    between-∷ (complete (♭ p) x∈p) (complete (p between (t′ ∷ ts)) xs∈)

  complete (p₁ ∥ p₂) (∣ˡ (<$> x∈p₁)) = ∥ˡ (complete p₁ x∈p₁)
  complete (p₁ ∥ p₂) (∣ʳ .[] x∈p₂)   = ∥ʳ (complete p₂ x∈p₂)
