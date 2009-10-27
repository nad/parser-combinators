------------------------------------------------------------------------
-- Total parser combinators (recognisers)
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- The recognisers are parametrised on the alphabet.

module TotalRecognisers
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         -- The tokens must come with decidable equality.
         where

open import Algebra
open import Coinduction
open import Data.Bool using (Bool; true; false; _∨_)
import Data.Bool.Properties as Bool
private
  module BoolCS = CommutativeSemiring Bool.commutativeSemiring-∧-∨
open import Data.Function using (_∘_; _$_)
open import Data.List as List using (List; []; _∷_; _++_; [_])
private
  module ListMonoid {A} = Monoid (List.monoid A)
open import Data.Product
open import Relation.Nullary

------------------------------------------------------------------------
-- A "right-strict" variant of _∧_

-- If the left-strict variant of _∧_ were used to type _·_ below, then
-- the inferred definition of ∂n would not be total; it would contain
-- expressions of the form "∂n (♭ p₁) t ∧ false". With the
-- right-strict definition of _∧_ such expressions reduce to "false".

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
b ∧ true  = b
b ∧ false = false

-- A lemma.

left-zero : ∀ b → false ∧ b ≡ false
left-zero true  = refl
left-zero false = refl

------------------------------------------------------------------------
-- Conditional coinduction

-- Coinductive if the index is /false/.

data ∞? (A : Set) : Bool → Set where
  ⟨_⟩ : (x :   A) → ∞? A true
  ⟪_⟫ : (x : ∞ A) → ∞? A false

♯? : ∀ {b A} → A → ∞? A b
♯? {true}  x = ⟨   x ⟩
♯? {false} x = ⟪ ♯ x ⟫

♭? : ∀ {A b} → ∞? A b → A
♭? ⟨ x ⟩ =   x
♭? ⟪ x ⟫ = ♭ x

-- A lemma.

♭?♯? : ∀ {A} b {x : A} → ♭? (♯? {b} x) ≡ x
♭?♯? true  = refl
♭?♯? false = refl

------------------------------------------------------------------------
-- Parser combinators

infixl 10 _·_
infixl  5 _∣_

-- The index is true if the corresponding language contains the empty
-- string (is nullable).

data P : Bool → Set where
  ∅        : P false
  ε        : P true
  tok      : Tok → P false
  _∣_      : ∀ {n₁ n₂} →     P n₁     →     P n₂     → P (n₁ ∨ n₂)
  _·_      : ∀ {n₁ n₂} → ∞? (P n₁) n₂ → ∞? (P n₂) n₁ → P (n₁ ∧ n₂)
  nonempty : ∀ {n} → P n → P false
  cast     : ∀ {n₁ n₂} → n₁ ≡ n₂ → P n₁ → P n₂

-- Note that ∅, nonempty and cast could be defined as derived
-- combinators. (For cast this is obvious, for ∅ and nonempty see
-- below, and note that the proof in
-- TotalRecognisers.ExpressiveStrength does not rely on these
-- constructors.) However, Agda uses /guarded/ corecursion, so the
-- fact that nonempty and cast are constructors can be very convenient
-- when constructing other parsers.

-- For an example of the use of nonempty, see the Kleene star example
-- below. For an example of the use of cast, see
-- TotalRecognisers.NotOnlyContextFree.)

------------------------------------------------------------------------
-- Semantics

-- The semantics is defined inductively: s ∈ p iff the string s is
-- contained in the language defined by p.

infix 4 _∈_

data _∈_ : ∀ {n} → List Tok → P n → Set where
  ε        : [] ∈ ε
  tok      : ∀ {t} → [ t ] ∈ tok t
  ∣ˡ       : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
             s ∈ p₁ → s ∈ p₁ ∣ p₂
  ∣ʳ       : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
             s ∈ p₂ → s ∈ p₁ ∣ p₂
  _·_      : ∀ {s₁ s₂ n₁ n₂} {p₁ : ∞? (P n₁) n₂} {p₂ : ∞? (P n₂) n₁} →
             s₁ ∈ ♭? p₁ → s₂ ∈ ♭? p₂ → s₁ ++ s₂ ∈ p₁ · p₂
  nonempty : ∀ {n t s} {p : P n} →
             t ∷ s ∈ p → t ∷ s ∈ nonempty p
  cast     : ∀ {n₁ n₂ s} {p : P n₁} {eq : n₁ ≡ n₂} →
             s ∈ p → s ∈ cast eq p

-- A lemma.

cast∈ : ∀ {n} {p p′ : P n} {s s′} → s ≡ s′ → p ≡ p′ → s ∈ p → s′ ∈ p′
cast∈ refl refl s∈ = s∈

------------------------------------------------------------------------
-- Example: A definition which is left and right recursive

leftRight : P false
leftRight = ⟪ ♯ leftRight ⟫ · ⟪ ♯ leftRight ⟫

-- Note that leftRight is equivalent to ∅, so ∅ does not need to be a
-- primitive combinator.

leftRight≈∅ : ∀ {s} → ¬ s ∈ leftRight
leftRight≈∅ (∈₁ · ∈₂) = leftRight≈∅ ∈₁

------------------------------------------------------------------------
-- Example: Kleene star

-- The intended semantics of the Kleene star.

infixr 5 _∷_
infix  4 _∈[_]⋆

data _∈[_]⋆ {n} : List Tok → P n → Set where
  []  : ∀ {p}       → [] ∈[ p ]⋆
  _∷_ : ∀ {s₁ s₂ p} → s₁ ∈ p → s₂ ∈[ p ]⋆ → s₁ ++ s₂ ∈[ p ]⋆

module Variant₁ where

  -- This definition requires that the argument parsers are not
  -- nullable.

  _⋆ : P false → P true
  p ⋆ = ε ∣ ⟨ p ⟩ · ⟪ ♯ (p ⋆) ⟫

  -- The definition of _⋆ above is correct.

  ⋆-sound : ∀ {s p} → s ∈ p ⋆ → s ∈[ p ]⋆
  ⋆-sound (∣ˡ ε)           = []
  ⋆-sound (∣ʳ (pr₁ · pr₂)) = pr₁ ∷ ⋆-sound pr₂

  ⋆-complete : ∀ {s p} → s ∈[ p ]⋆ → s ∈ p ⋆
  ⋆-complete []                    = ∣ˡ ε
  ⋆-complete (_∷_ {[]}    pr₁ pr₂) = ⋆-complete pr₂
  ⋆-complete (_∷_ {_ ∷ _} pr₁ pr₂) =
    ∣ʳ {n₁ = true} (pr₁ · ⋆-complete pr₂)

module Variant₂ where

  -- This definition works for any argument parser.

  _⋆ : ∀ {n} → P n → P true
  p ⋆ = ε ∣ ⟨ nonempty p ⟩ · ⟪ ♯ (p ⋆) ⟫

  -- The definition of _⋆ above is correct.

  ⋆-sound : ∀ {s n} {p : P n} → s ∈ p ⋆ → s ∈[ p ]⋆
  ⋆-sound (∣ˡ ε)                    = []
  ⋆-sound (∣ʳ (nonempty pr₁ · pr₂)) = pr₁ ∷ ⋆-sound pr₂

  ⋆-complete : ∀ {s n} {p : P n} → s ∈[ p ]⋆ → s ∈ p ⋆
  ⋆-complete []                    = ∣ˡ ε
  ⋆-complete (_∷_ {[]}    pr₁ pr₂) = ⋆-complete pr₂
  ⋆-complete (_∷_ {_ ∷ _} pr₁ pr₂) =
    ∣ʳ {n₁ = true} (nonempty pr₁ · ⋆-complete pr₂)

  -- Note, however, that for actual parsing the corresponding
  -- definition would not be correct. The reason is that p would give
  -- a result also when the empty string was accepted, and these
  -- results are ignored by the definition above. In the case of
  -- actual parsing the result of p ⋆, when p is nullable, should be a
  -- stream and not a finite list.

------------------------------------------------------------------------
-- Nullability

-- The nullability index is correct.

⇒ : ∀ {n} {p : P n} → [] ∈ p → n ≡ true
⇒ pr = ⇒′ pr refl
  where
  ⇒′ : ∀ {n s} {p : P n} → s ∈ p → s ≡ [] → n ≡ true
  ⇒′ ε                     refl = refl
  ⇒′ tok                   ()
  ⇒′ (∣ˡ pr₁)              refl with ⇒ pr₁
  ⇒′ (∣ˡ pr₁)              refl | refl = refl
  ⇒′ (∣ʳ pr₂)              refl with ⇒ pr₂
  ⇒′ (∣ʳ {n₁ = n₁} pr₂)    refl | refl = proj₂ BoolCS.zero n₁
  ⇒′ (_·_ {[]}    pr₁ pr₂) refl = cong₂ _∧_ (⇒ pr₁) (⇒ pr₂)
  ⇒′ (_·_ {_ ∷ _} pr₁ pr₂) ()
  ⇒′ (nonempty p)          ()
  ⇒′ (cast {eq = refl} p)  refl = ⇒′ p refl

⇐ : ∀ {n} (p : P n) → n ≡ true → [] ∈ p
⇐ ∅                            ()
⇐ ε                            refl = ε
⇐ (tok t)                      ()
⇐ (_∣_ {true}           p₁ p₂) refl = ∣ˡ (⇐ p₁ refl)
⇐ (_∣_ {false} {true}   p₁ p₂) refl = ∣ʳ {p₁ = p₁} (⇐ p₂ refl)
⇐ (_∣_ {false} {false}  p₁ p₂) ()
⇐ (⟨ p₁ ⟩ · ⟨ p₂ ⟩)            refl = ⇐ p₁ refl · ⇐ p₂ refl
⇐ (⟪ p₁ ⟫ · ⟨ p₂ ⟩)            ()
⇐ (⟨ p₁ ⟩ · ⟪ p₂ ⟫)            ()
⇐ (⟪ p₁ ⟫ · ⟪ p₂ ⟫)            ()
⇐ (nonempty p)                 ()
⇐ (cast refl p)                refl = cast (⇐ p refl)

-- We can decide if the empty string belongs to a given language.

nullable? : ∀ {n} (p : P n) → Dec ([] ∈ p)
nullable? {true}  p = yes (⇐ p refl)
nullable? {false} p = no helper
  where
  helper : ¬ [] ∈ p
  helper []∈p with ⇒ []∈p
  ... | ()

------------------------------------------------------------------------
-- Derivative

-- The index of the derivative. The right-hand sides (excluding
-- t′ ≟ t) are inferable, but included here so that they can easily be
-- inspected.

∂n : ∀ {n} → P n → Tok → Bool
∂n ∅                 t = false
∂n ε                 t = false
∂n (tok t′)          t with t′ ≟ t
∂n (tok t′)          t | yes t′≡t = true
∂n (tok t′)          t | no  t′≢t = false
∂n (p₁ ∣ p₂)         t = ∂n p₁ t ∨ ∂n p₂ t
∂n (⟨ p₁ ⟩ · ⟨ p₂ ⟩) t = ∂n p₁ t ∨ ∂n p₂ t
∂n (⟪ p₁ ⟫ · ⟨ p₂ ⟩) t = ∂n p₂ t
∂n (⟨ p₁ ⟩ · ⟪ p₂ ⟫) t = ∂n p₁ t
∂n (⟪ p₁ ⟫ · ⟪ p₂ ⟫) t = false
∂n (nonempty p)      t = ∂n p t
∂n (cast _ p)        t = ∂n p t

-- ∂ p t is the "derivative" of p with respect to t. It is specified
-- by the equivalence s ∈ ∂ p t ⇔ t ∷ s ∈ p (proved below).

∂ : ∀ {n} (p : P n) (t : Tok) → P (∂n p t)
∂ ∅                 t = ∅
∂ ε                 t = ∅
∂ (tok t′)          t with t′ ≟ t
∂ (tok t′)          t | yes t′≡t = ε
∂ (tok t′)          t | no  t′≢t = ∅
∂ (p₁ ∣ p₂)         t = ∂ p₁ t ∣ ∂ p₂ t
∂ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) t = ⟨   ∂    p₁  t ⟩ · ♯?    p₂ ∣ ∂ p₂  t
∂ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) t = ⟪ ♯ ∂ (♭ p₁) t ⟫ · ♯?    p₂ ∣ ∂ p₂  t
∂ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) t = ⟨   ∂    p₁  t ⟩ · ♯? (♭ p₂)
∂ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) t = ⟪ ♯ ∂ (♭ p₁) t ⟫ · ♯? (♭ p₂)
∂ (nonempty p)      t = ∂ p t
∂ (cast _ p)        t = ∂ p t

-- ∂ is correct.

∂-sound : ∀ {s n} {p : P n} {t} → s ∈ ∂ p t → t ∷ s ∈ p
∂-sound s∈ = ∂-sound′ _ _ s∈
  where
  ∂-sound′ : ∀ {s n} (p : P n) t → s ∈ ∂ p t → t ∷ s ∈ p
  ∂-sound′ ∅                 t ()
  ∂-sound′ ε                 t ()
  ∂-sound′ (tok t′)          t _              with t′ ≟ t
  ∂-sound′ (tok .t)          t ε              | yes refl = tok
  ∂-sound′ (tok t′)          t ()             | no  t′≢t
  ∂-sound′ (p₁ ∣ p₂)         t (∣ˡ ∈₁)        = ∣ˡ (∂-sound′ p₁ t ∈₁)
  ∂-sound′ (p₁ ∣ p₂)         t (∣ʳ ∈₂)        = ∣ʳ {p₁ = p₁} (∂-sound′ p₂ t ∈₂)
  ∂-sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) t (∣ˡ (∈₁ · ∈₂)) = ∂-sound ∈₁ · cast∈ refl (♭?♯? (∂n p₁ t)) ∈₂
  ∂-sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) t (∣ʳ ∈₂)        = ⇐ p₁ refl · ∂-sound′ p₂ t ∈₂
  ∂-sound′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) t (∈₁ · ∈₂)      = ∂-sound ∈₁ · cast∈ refl (♭?♯? (∂n p₁ t)) ∈₂
  ∂-sound′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) t (∣ˡ (∈₁ · ∈₂)) = ∂-sound ∈₁ · cast∈ refl (♭?♯? (∂n (♭ p₁) t)) ∈₂
  ∂-sound′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) t (∣ʳ ∈₂)        = ⇐ (♭ p₁) refl · ∂-sound′ p₂ t ∈₂
  ∂-sound′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) t (∈₁ · ∈₂)      = ∂-sound ∈₁ · cast∈ refl (♭?♯? (∂n (♭ p₁) t)) ∈₂
  ∂-sound′ (nonempty p)      t ∈              = nonempty (∂-sound ∈)
  ∂-sound′ (cast _ p)        t ∈              = cast (∂-sound ∈)

∂-complete : ∀ {s n} {p : P n} {t} → t ∷ s ∈ p → s ∈ ∂ p t
∂-complete {t = t} t∷s∈ = ∂-complete′ _ t∷s∈ refl
  where
  ∂-complete′ : ∀ {s s′ n} (p : P n) → s′ ∈ p → s′ ≡ t ∷ s → s ∈ ∂ p t
  ∂-complete′         ∅        ()  refl
  ∂-complete′         ε        ()  refl
  ∂-complete′         (tok t′) _   refl with t′ ≟ t
  ∂-complete′         (tok .t) tok refl | yes refl = ε
  ∂-complete′ {[]}    (tok .t) tok refl | no  t′≢t with t′≢t refl
  ∂-complete′ {[]}    (tok .t) tok refl | no  t′≢t | ()
  ∂-complete′ {_ ∷ _} (tok t′) ()  refl | no  t′≢t
  ∂-complete′ (p₁ ∣ p₂)         (∣ˡ ∈₁)              refl = ∣ˡ (∂-complete ∈₁)
  ∂-complete′ (p₁ ∣ p₂)         (∣ʳ ∈₂)              refl = ∣ʳ {p₁ = ∂ p₁ t} (∂-complete ∈₂)
  ∂-complete′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (_·_ {[]}     ∈₁ ∈₂) refl = ∣ʳ {p₁ = ⟨ ∂ p₁ t ⟩ · _} (∂-complete ∈₂)
  ∂-complete′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∣ˡ (∂-complete ∈₁ · cast∈ refl (sym (♭?♯? (∂n p₁ t))) ∈₂)
  ∂-complete′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl with ⇒ ∈₁
  ∂-complete′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl | ()
  ∂-complete′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∂-complete ∈₁ · cast∈ refl (sym (♭?♯? (∂n p₁ t))) ∈₂
  ∂-complete′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) (_·_ {[]}     ∈₁ ∈₂) refl = ∣ʳ {p₁ = ⟪ _ ⟫ · _} (∂-complete ∈₂)
  ∂-complete′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∣ˡ (∂-complete ∈₁ · cast∈ refl (sym (♭?♯? (∂n (♭ p₁) t))) ∈₂)
  ∂-complete′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl with ⇒ ∈₁
  ∂-complete′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl | ()
  ∂-complete′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∂-complete ∈₁ · cast∈ refl (sym (♭?♯? (∂n (♭ p₁) t))) ∈₂
  ∂-complete′ (nonempty p)      (nonempty ∈)         refl = ∂-complete ∈
  ∂-complete′ (cast _ p)        (cast ∈)             refl = ∂-complete ∈

------------------------------------------------------------------------
-- _∈_ is decidable

-- _∈?_ runs a parser (recogniser). Note that the result is yes or no
-- plus a /proof/ verifying that the answer is correct.

infix 4 _∈?_

_∈?_ : ∀ {n} (s : List Tok) (p : P n) → Dec (s ∈ p)
[]    ∈? p = nullable? p
t ∷ s ∈? p with s ∈? ∂ p t
t ∷ s ∈? p | yes s∈∂pt = yes (∂-sound s∈∂pt)
t ∷ s ∈? p | no  s∉∂pt = no  (s∉∂pt ∘ ∂-complete)

------------------------------------------------------------------------
-- The combinator nonempty does not need to be primitive

-- The variant of nonempty which is defined below (nonempty′) makes
-- many parsers larger, though.

module AlternativeNonempty where

  nonempty′ : ∀ {n} → P n → P false
  nonempty′ ∅                 = ∅
  nonempty′ ε                 = ∅
  nonempty′ (tok t)           = tok t
  nonempty′ (p₁ ∣ p₂)         = nonempty′ p₁ ∣ nonempty′ p₂
  nonempty′ (⟪ p₁ ⟫ ·   p₂  ) = ⟪ p₁ ⟫ ·   p₂
  nonempty′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) = ⟨ p₁ ⟩ · ⟪ p₂ ⟫
  nonempty′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) = nonempty′ p₁ ∣ nonempty′ p₂
                              ∣ ♯? (nonempty′ p₁) · ♯? (nonempty′ p₂)
  nonempty′ (nonempty p)      = nonempty′ p
  nonempty′ (cast eq p)       = nonempty′ p

  sound : ∀ {n s} {p : P n} → s ∈ nonempty′ p → s ∈ nonempty p
  sound {s = []}    pr with ⇒ pr
  ... | ()
  sound {s = _ ∷ _} pr = nonempty (sound′ _ pr refl)
    where
    sound′ : ∀ {n t s s′} (p : P n) →
             s′ ∈ nonempty′ p → s′ ≡ t ∷ s → t ∷ s ∈ p
    sound′ ∅                 ()                         refl
    sound′ ε                 ()                         refl
    sound′ (tok t)           tok                        refl = tok
    sound′ (p₁ ∣ p₂)         (∣ˡ pr)                    refl = ∣ˡ           (sound′ p₁ pr refl)
    sound′ (p₁ ∣ p₂)         (∣ʳ pr)                    refl = ∣ʳ {p₁ = p₁} (sound′ p₂ pr refl)
    sound′ (⟪ p₁ ⟫ ·   p₂  ) pr                         refl = pr
    sound′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) pr                         refl = pr
    sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (∣ˡ (∣ˡ pr))               refl = cast∈ (proj₂ ListMonoid.identity _) refl $
                                                                 sound′ p₁ pr refl · ⇐ p₂ refl
    sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (∣ˡ (∣ʳ pr))               refl = ⇐ p₁ refl · sound′ p₂ pr refl
    sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (∣ʳ (_·_ {[]}    pr₁ pr₂)) refl with ⇒ pr₁
    ... | ()
    sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (∣ʳ (_·_ {_ ∷ _} pr₁ pr₂)) refl with sound {p = p₂} pr₂
    ... | nonempty pr₂′ = sound′ p₁ pr₁ refl · pr₂′
    sound′ (nonempty p)      pr                         refl = nonempty (sound′ p pr refl)
    sound′ (cast _ p)        pr                         refl = cast (sound′ p pr refl)

  complete : ∀ {n s} {p : P n} → s ∈ nonempty p → s ∈ nonempty′ p
  complete (nonempty pr) = complete′ _ pr refl
    where
    complete′ : ∀ {n t s s′} (p : P n) →
                s ∈ p → s ≡ t ∷ s′ → t ∷ s′ ∈ nonempty′ p
    complete′ ∅                 ()                            refl
    complete′ ε                 ()                            refl
    complete′ (tok t)           tok                           refl = tok
    complete′ (p₁ ∣ p₂)         (∣ˡ pr)                       refl = ∣ˡ              (complete′ p₁ pr refl)
    complete′ (p₁ ∣ p₂)         (∣ʳ pr)                       refl = ∣ʳ {n₁ = false} (complete′ p₂ pr refl)
    complete′ (⟪ p₁ ⟫ ·   p₂  ) pr                            refl = pr
    complete′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) pr                            refl = pr
    complete′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (_·_ {[]}            pr₁ pr₂) refl = ∣ˡ (∣ʳ {n₁ = false} (complete′ p₂ pr₂ refl))
    complete′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (_·_ {_ ∷ _} {[]}    pr₁ pr₂) refl = cast∈ (sym $ proj₂ ListMonoid.identity _) refl $
                                                                       ∣ˡ (∣ˡ {n₂ = false} (complete′ p₁ pr₁ refl))
    complete′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (_·_ {_ ∷ _} {_ ∷ _} pr₁ pr₂) refl = ∣ʳ {n₁ = false} (complete′ p₁ pr₁ refl ·
                                                                                      complete′ p₂ pr₂ refl)
    complete′ (nonempty p)      (nonempty pr)                 refl = complete′ p pr refl
    complete′ (cast _ p)        (cast pr)                     refl = complete′ p pr refl
