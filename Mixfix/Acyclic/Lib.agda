------------------------------------------------------------------------
-- Small parser combinator library used by Mixfix.Acyclic.Grammar
------------------------------------------------------------------------

-- Note that while Mixfix.Acyclic.Lib and Mixfix.Cyclic.Lib may appear
-- to be very similar, there are some important differences:
--
-- • Mixfix.Cyclic.Lib._⊛∞_ accepts delayed parsers,
--   Mixfix.Acyclic.Lib._⊛_ does not.
--
-- • There is a translation from the parsers in Mixfix.Acyclic.Lib to
--   the /simplified/ parsers in
--   StructurallyRecursiveDescentParsing.Simplified; no such
--   translation is defined for the parsers in Mixfix.Cyclic.Lib. Note
--   that the depth-first backend in
--   StructurallyRecursiveDescentParsing.DepthFirst only handles
--   simplified parsers.

module Mixfix.Acyclic.Lib where

open import Algebra
open import Coinduction
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List as List using (List; []; _∷_; _++_)
private module LM {A} = Monoid (List.monoid A)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷ʳ_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product
import Data.String as String
open import Relation.Binary
open DecSetoid String.decSetoid using (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

open import TotalParserCombinators.Coinduction
import StructurallyRecursiveDescentParsing.Simplified as Simplified
open Simplified hiding (⟦_⟧)
open import StructurallyRecursiveDescentParsing.Simplified.Semantics
  as Sem hiding (cast∈; sound; complete)
open import Mixfix.Operator using (NamePart)

------------------------------------------------------------------------
-- Programs

-- Agda's termination checker only accepts corecursive definitions if
-- they are /syntactically/ guarded by constructors. The following
-- small language of "parser programs" reifies a selection of parser
-- combinators as /constructors/. These constructors are then used in
-- Mixfix.Acyclic.Grammar in order to ensure that Agda accepts the
-- grammars defined there.

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
              (p : ∞ (ParserProg R)) (toks : Vec NamePart (1 + n)) →
              ParserProg (Vec R n)
  _∥_       : ∀ {I i} {R : I → Set}
              (p₁ : ParserProg (R i))
              (p₂ : ParserProg (∃ R)) →
                    ParserProg (∃ R)

-- Parses a given token.

tok : NamePart → Parser NamePart false NamePart
tok tok = token !>>= λ tok′ → ♯ ok tok′
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

  ♯′_ : ∀ {A} → A → ∞ A
  ♯′ x = ♯ x

⟦_⟧ : ∀ {R} → ParserProg R → Parser NamePart false R
⟦ fail                    ⟧ = fail
⟦ p₁ ∣ p₂                 ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ p₁ ⊛ p₂                 ⟧ = ⟦ p₁ ⟧ !>>= λ f → ♯ ⟦ f <$> p₂ ⟧
⟦ f <$> p                 ⟧ = ⟦ p  ⟧ !>>= λ x → ♯′ return (f x)
⟦ p +                     ⟧ = ⟦ p  ⟧ !>>= λ x → ♯
                              (⟦ _∷_ x <$> p + ⟧ ∣ return [ x ])
⟦ p between (t ∷ [])      ⟧ = tok t !>>= λ _ → ♯′ return []
⟦ p between (t ∷ t′ ∷ ts) ⟧ = tok t !>>= λ _ → ♯
                              ⟦ _∷_ <$> ♭ p ⊛ (p between (t′ ∷ ts)) ⟧
⟦ p₁ ∥ p₂                 ⟧ = (⟦ p₁ ⟧ !>>= λ x → ♯′ return (, x)) ∣ ⟦ p₂ ⟧

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

  private

    drop-[] : ∀ {R s x} {p : Parser NamePart false R} →
              x ∈ p · s ++ [] → x ∈ p · s
    drop-[] = Sem.cast∈ refl refl (proj₂ LM.identity _)

    add-[] : ∀ {R s x} {p : ParserProg R} →
             x ∈⟦ p ⟧· s → x ∈⟦ p ⟧· s ++ []
    add-[] {s = s} x∈p with s ++ [] | proj₂ LM.identity s
    ... | .s | refl = x∈p

  ⊛-complete : ∀ {s₁ s₂ R₁ R₂ f x}
                 {p₁ : ParserProg (R₁ → R₂)} {p₂ : ParserProg R₁} →
               f ∈ ⟦ p₁ ⟧ · s₁ → x ∈ ⟦ p₂ ⟧ · s₂ →
               f x ∈ ⟦ p₁ ⊛ p₂ ⟧ · s₁ ++ s₂
  ⊛-complete f∈p₁ x∈p₂ = f∈p₁ !>>= drop-[] (x∈p₂ !>>= return)

  tok-sound : ∀ {t t′ s} →
              t′ ∈ tok t · s →
              t ≡ t′ × s ≡ t′ ∷ []
  tok-sound {t} (_!>>=_ {x = t″} token t′∈) with t ≟ t″
  tok-sound (token !>>= return) | yes t≈t″ = (t≈t″ , refl)
  tok-sound (token !>>= ())     | no  t≉t″

  tok-complete : ∀ {t} → t ∈ tok t · t ∷ []
  tok-complete {t} = token !>>= ok-lemma
    where
    ok-lemma : t ∈ TheToken.ok t t · []
    ok-lemma with t ≟ t
    ... | yes refl = return
    ... | no  t≢t  with t≢t refl
    ...   | ()

  sound : ∀ {R x s} {p : ParserProg R} →
          x ∈⟦ p ⟧· s → x ∈ ⟦ p ⟧ · s
  sound (∣ˡ x∈p₁)      = ∣ˡ       (sound x∈p₁)
  sound (∣ʳ x∈p₂)      = ∣ʳ false (sound x∈p₂)
  sound (f∈p₁ ⊛ x∈p₂)  = ⊛-complete (sound f∈p₁) (sound x∈p₂)
  sound (<$> x∈p)      = drop-[] (sound x∈p !>>= return)
  sound (+-[] x∈p)     = drop-[] (sound x∈p !>>= ∣ʳ false return)
  sound (+-∷ x∈p xs∈p) = sound x∈p !>>= ∣ˡ (drop-[] (sound xs∈p !>>= return))
  sound (∥ˡ x∈p₁)      = drop-[] (∣ˡ (sound x∈p₁ !>>= return))
  sound (∥ʳ x∈p₂)      = ∣ʳ false (sound x∈p₂)
  sound between-[]     = tok-complete !>>= return
  sound (between-∷ {s₁ = s₁} {ts = _ ∷ _} x∈p xs∈⋯) =
    tok-complete !>>=
    ⊛-complete (drop-[] {s = s₁} (sound x∈p !>>= return)) (sound xs∈⋯)

  complete : ∀ {R x s} (p : ParserProg R) →
             x ∈ ⟦ p ⟧ · s → x ∈⟦ p ⟧· s
  complete fail      ()

  complete (p₁ ∣ p₂) (∣ˡ        x∈p₁) = ∣ˡ (complete p₁ x∈p₁)
  complete (p₁ ∣ p₂) (∣ʳ .false x∈p₂) = ∣ʳ (complete p₂ x∈p₂)

  complete (p₁ ⊛ p₂) (f∈p₁ !>>= (y∈p₂ !>>= return)) =
    complete p₁ f∈p₁ ⊛ add-[] (complete p₂ y∈p₂)

  complete (f <$> p) (x∈p !>>= return) = add-[] (<$> complete p x∈p)

  complete (p +) (x∈p !>>= ∣ˡ (xs∈p+ !>>= return)) = +-∷ (complete p x∈p) (add-[] (complete (p +) xs∈p+))
  complete (p +) (x∈p !>>= ∣ʳ .false return)       = add-[] (+-[] (complete p x∈p))

  complete (p between (t ∷ [])) (t∈ !>>= return) with tok-sound t∈
  ... | (refl , refl) = between-[]
  complete (p between (t ∷ t′ ∷ ts))
           (t∈ !>>= (x∈p !>>= return !>>= (xs∈ !>>= return))) with tok-sound t∈
  ... | (refl , refl) =
    between-∷ (add-[] (complete (♭ p) x∈p))
              (add-[] (complete (p between (t′ ∷ ts)) xs∈))

  complete (p₁ ∥ p₂) (∣ˡ (x∈p₁ !>>= return)) = add-[] (∥ˡ (complete p₁ x∈p₁))
  complete (p₁ ∥ p₂) (∣ʳ .false x∈p₂)        = ∥ʳ (complete p₂ x∈p₂)

------------------------------------------------------------------------
-- A variant of the semantics

-- The alternative semantics defined below may be slightly harder to
-- understand, but it is (language) equivalent to the one above, and
-- it simplifies the proof in Mixfix.Acyclic.Show.

module Semantics-⊕ where

  infix  60 <$>_
  infixl 50 _⊛_
  infix  4  _⊕_∈⟦_⟧·_

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

  -- The semantics is correct.

  ⊛-complete : ∀ {s s₁ s₂ R₁ R₂ f x}
                 {p₁ : ParserProg (R₁ → R₂)} {p₂ : ParserProg R₁} →
               f ⊕ s₁ ∈ ⟦ p₁ ⟧ · s → x ⊕ s₂ ∈ ⟦ p₂ ⟧ · s₁ →
               f x ⊕ s₂ ∈ ⟦ p₁ ⊛ p₂ ⟧ · s
  ⊛-complete f∈p₁ x∈p₂ = f∈p₁ !>>= (x∈p₂ !>>= return)

  tok-sound : ∀ {t t′ s₁ s} →
              t′ ⊕ s₁ ∈ tok t · s →
              t ≡ t′ × s ≡ t′ ∷ s₁
  tok-sound     ∈ with Sem.⊕-sound′ ∈
  tok-sound     ∈ | (s         , refl , ∈′) with Semantics.tok-sound ∈′
  tok-sound {t} ∈ | (.(t ∷ []) , refl , ∈′) | (refl , refl) = (refl , refl)

  tok-complete : ∀ {t s} → t ⊕ s ∈ tok t · t ∷ s
  tok-complete = Sem.⊕-complete′ (_ , refl , Semantics.tok-complete)

  sound : ∀ {R x s s′} {p : ParserProg R} →
          x ⊕ s′ ∈⟦ p ⟧· s → x ⊕ s′ ∈ ⟦ p ⟧ · s
  sound (∣ˡ x∈p₁)      = ∣ˡ       (sound x∈p₁)
  sound (∣ʳ x∈p₂)      = ∣ʳ false (sound x∈p₂)
  sound (f∈p₁ ⊛ x∈p₂)  = ⊛-complete (sound f∈p₁) (sound x∈p₂)
  sound (<$> x∈p)      = sound x∈p !>>= return
  sound (+-[] x∈p)     = sound x∈p !>>= ∣ʳ false return
  sound (+-∷ x∈p xs∈p) = sound x∈p !>>= ∣ˡ (sound xs∈p !>>= return)
  sound (∥ˡ x∈p₁)      = ∣ˡ (sound x∈p₁ !>>= return)
  sound (∥ʳ x∈p₂)      = ∣ʳ false (sound x∈p₂)
  sound between-[]     = tok-complete !>>= return
  sound (between-∷ {ts = _ ∷ _} x∈p xs∈⋯) =
    tok-complete !>>=
    ⊛-complete (sound x∈p !>>= return) (sound xs∈⋯)

  complete : ∀ {R x s s′} (p : ParserProg R) →
             x ⊕ s′ ∈ ⟦ p ⟧ · s → x ⊕ s′ ∈⟦ p ⟧· s
  complete fail      ()

  complete (p₁ ∣ p₂) (∣ˡ        x∈p₁) = ∣ˡ (complete p₁ x∈p₁)
  complete (p₁ ∣ p₂) (∣ʳ .false x∈p₂) = ∣ʳ (complete p₂ x∈p₂)

  complete (p₁ ⊛ p₂) (f∈p₁ !>>= (y∈p₂ !>>= return)) =
    complete p₁ f∈p₁ ⊛ complete p₂ y∈p₂

  complete (f <$> p) (x∈p !>>= return) = <$> complete p x∈p

  complete (p +) (x∈p !>>= ∣ˡ (xs∈p+ !>>= return)) = +-∷  (complete p x∈p) (complete (p +) xs∈p+)
  complete (p +) (x∈p !>>= ∣ʳ .false return)       = +-[] (complete p x∈p)

  complete (p between (t ∷ [])) (t∈ !>>= return) with tok-sound t∈
  ... | (refl , refl) = between-[]
  complete (p between (t ∷ t′ ∷ ts))
           (t∈ !>>= (x∈p !>>= return !>>= (xs∈ !>>= return))) with tok-sound t∈
  ... | (refl , refl) =
    between-∷ (complete (♭ p) x∈p) (complete (p between (t′ ∷ ts)) xs∈)

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
