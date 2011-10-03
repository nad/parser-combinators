------------------------------------------------------------------------
-- Total recognisers which can handle left recursion
------------------------------------------------------------------------

-- The recognisers are parametrised on the alphabet.

module TotalRecognisers.LeftRecursion (Tok : Set) where

open import Algebra
open import Coinduction
open import Data.Bool as Bool hiding (_∧_)
import Data.Bool.Properties as Bool
private
  module BoolCS = CommutativeSemiring Bool.commutativeSemiring-∧-∨
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence as Eq
  using (_⇔_; equivalence; module Equivalence)
  renaming (_∘_ to _⟨∘⟩_)
open import Data.List as List using (List; []; _∷_; _++_; [_])
private
  module ListMonoid {A : Set} = Monoid (List.monoid A)
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- A "right-strict" variant of _∧_

-- If the left-strict variant of _∧_ were used to type _·_ below, then
-- the inferred definition of D-nullable would not be total; it would
-- contain expressions of the form "D-nullable t (♭ p₁) ∧ false". With
-- the right-strict definition of _∧_ such expressions reduce to
-- "false".

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
b ∧ true  = b
b ∧ false = false

-- A lemma.

left-zero : ∀ b → false ∧ b ≡ false
left-zero true  = refl
left-zero false = refl

------------------------------------------------------------------------
-- Recogniser combinators

infixl 10 _·_
infixl  5 _∣_

mutual

  -- The index is true if the corresponding language contains the empty
  -- string (is nullable).

  data P : Bool → Set where
    fail     : P false
    empty    : P true
    sat      : (Tok → Bool) → P false
    _∣_      : ∀ {n₁ n₂} →        P n₁ →        P n₂ → P (n₁ ∨ n₂)
    _·_      : ∀ {n₁ n₂} → ∞⟨ n₂ ⟩P n₁ → ∞⟨ n₁ ⟩P n₂ → P (n₁ ∧ n₂)
    nonempty : ∀ {n} → P n → P false
    cast     : ∀ {n₁ n₂} → n₁ ≡ n₂ → P n₁ → P n₂

  -- Delayed if the index is /false/.

  ∞⟨_⟩P : Bool → Bool → Set
  ∞⟨ false ⟩P n = ∞ (P n)
  ∞⟨ true  ⟩P n =    P n

-- Note that fail, nonempty and cast could be defined as derived
-- combinators. (For cast this is obvious, fail could be defined
-- either using sat or the combinator leftRight below, and nonempty is
-- defined in the module AlternativeNonempty. Note also that the proof
-- in TotalRecognisers.LeftRecursion.ExpressiveStrength does not rely
-- on these constructors.) However, Agda uses /guarded/ corecursion,
-- so the fact that nonempty and cast are constructors can be very
-- convenient when constructing other recognisers.

-- For an example of the use of nonempty, see the Kleene star example
-- in TotalRecognisers.LeftRecursion.Lib. For examples of the use of
-- cast, see TotalRecognisers.LeftRecursion.ExpressiveStrength and
-- TotalRecognisers.LeftRecursion.NotOnlyContextFree.

------------------------------------------------------------------------
-- Helpers

♭? : ∀ {b n} → ∞⟨ b ⟩P n → P n
♭? {b = false} x = ♭ x
♭? {b = true}  x =   x

♯? : ∀ {b n} → P n → ∞⟨ b ⟩P n
♯? {b = false} x = ♯ x
♯? {b = true}  x =   x

forced? : ∀ {b n} → ∞⟨ b ⟩P n → Bool
forced? {b = b} _ = b

-- A lemma.

♭?♯? : ∀ b {n} {p : P n} → ♭? {b} (♯? p) ≡ p
♭?♯? false = refl
♭?♯? true  = refl

------------------------------------------------------------------------
-- Semantics

-- The semantics is defined inductively: s ∈ p iff the string s is
-- contained in the language defined by p.

infix 4 _∈_

data _∈_ : ∀ {n} → List Tok → P n → Set where
  empty    : [] ∈ empty
  sat      : ∀ {f t} → T (f t) → [ t ] ∈ sat f
  ∣-left   : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
             s ∈ p₁ → s ∈ p₁ ∣ p₂
  ∣-right  : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
             s ∈ p₂ → s ∈ p₁ ∣ p₂
  _·_      : ∀ {s₁ s₂ n₁ n₂}
               {p₁ : ∞⟨ n₂ ⟩P n₁} {p₂ : ∞⟨ n₁ ⟩P n₂} →
             s₁ ∈ ♭? p₁ → s₂ ∈ ♭? p₂ → s₁ ++ s₂ ∈ p₁ · p₂
  nonempty : ∀ {n t s} {p : P n} →
             t ∷ s ∈ p → t ∷ s ∈ nonempty p
  cast     : ∀ {n₁ n₂ s} {p : P n₁} {eq : n₁ ≡ n₂} →
             s ∈ p → s ∈ cast eq p

infix 4 _≤_ _≈_

-- p₁ ≤ p₂ iff the language (defined by) p₂ contains all the strings
-- in the language p₁.

_≤_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≤ p₂ = ∀ {s} → s ∈ p₁ → s ∈ p₂

-- p₁ ≈ p₂ iff the languages p₁ and p₂ contain the same strings.

_≈_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≈ p₂ = ∀ {s} → s ∈ p₁ ⇔ s ∈ p₂

-- p₁ ≈ p₂ iff both p₁ ≤ p₂ and p₂ ≤ p₁.

≈⇔≤≥ : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
       p₁ ≈ p₂ ⇔ (p₁ ≤ p₂ × p₂ ≤ p₁)
≈⇔≤≥ = equivalence
         (λ p₁≈p₂  → ((λ {s} → _⟨$⟩_ (Equivalence.to   (p₁≈p₂ {s = s})))
                     , λ {s} → _⟨$⟩_ (Equivalence.from (p₁≈p₂ {s = s}))))
         (λ p₁≤≥p₂ {s} → equivalence (proj₁ p₁≤≥p₂ {s = s})
                                     (proj₂ p₁≤≥p₂ {s = s}))

-- Some lemmas.

cast∈ : ∀ {n} {p p′ : P n} {s s′} → s ≡ s′ → p ≡ p′ → s ∈ p → s′ ∈ p′
cast∈ refl refl s∈ = s∈

drop-♭♯ : ∀ n {n′} {p : P n′} → ♭? (♯? {n} p) ≤ p
drop-♭♯ n = cast∈ refl (♭?♯? n)

add-♭♯ : ∀ n {n′} {p : P n′} → p ≤ ♭? (♯? {n} p)
add-♭♯ n = cast∈ refl (sym $ ♭?♯? n)

------------------------------------------------------------------------
-- Example: A definition which is left and right recursive

leftRight : P false
leftRight = ♯ leftRight · ♯ leftRight

-- Note that leftRight is equivalent to fail, so fail does not need to
-- be a primitive combinator.

leftRight≈fail : leftRight ≈ fail
leftRight≈fail = equivalence ≤fail (λ ())
  where
  ≤fail : ∀ {s A} → s ∈ leftRight → A
  ≤fail (∈₁ · ∈₂) = ≤fail ∈₁

-- For more examples, see TotalRecognisers.LeftRecursion.Lib.

------------------------------------------------------------------------
-- Nullability

-- The nullability index is correct.

⇒ : ∀ {n} {p : P n} → [] ∈ p → n ≡ true
⇒ pr = ⇒′ pr refl
  where
  ⇒′ : ∀ {n s} {p : P n} → s ∈ p → s ≡ [] → n ≡ true
  ⇒′ empty                   refl = refl
  ⇒′ (sat _)                 ()
  ⇒′ (∣-left            pr₁) refl with ⇒ pr₁
  ⇒′ (∣-left            pr₁) refl | refl = refl
  ⇒′ (∣-right           pr₂) refl with ⇒ pr₂
  ⇒′ (∣-right {n₁ = n₁} pr₂) refl | refl = proj₂ BoolCS.zero n₁
  ⇒′ (nonempty p)            ()
  ⇒′ (cast {eq = refl} p)    refl = ⇒′ p refl
  ⇒′ (_·_ {[]}    pr₁ pr₂)   refl = cong₂ _∧_ (⇒ pr₁) (⇒ pr₂)
  ⇒′ (_·_ {_ ∷ _} pr₁ pr₂)   ()

⇐ : ∀ {n} (p : P n) → n ≡ true → [] ∈ p
⇐ fail                        ()
⇐ empty                       refl = empty
⇐ (sat f)                     ()
⇐ (_∣_ {true}          p₁ p₂) refl = ∣-left            (⇐ p₁ refl)
⇐ (_∣_ {false} {true}  p₁ p₂) refl = ∣-right {p₁ = p₁} (⇐ p₂ refl)
⇐ (_∣_ {false} {false} p₁ p₂) ()
⇐ (nonempty p)                ()
⇐ (cast refl p)               refl = cast (⇐ p refl)
⇐ (_·_ {.true} {true}  p₁ p₂) refl = ⇐ p₁ refl · ⇐ p₂ refl
⇐ (_·_ {_}     {false} p₁ p₂) ()

index-correct : ∀ {n} {p : P n} → [] ∈ p ⇔ n ≡ true
index-correct = equivalence ⇒ (⇐ _)

-- We can decide if the empty string belongs to a given language.

nullable? : ∀ {n} (p : P n) → Dec ([] ∈ p)
nullable? {n} p = Dec.map (Eq.sym index-correct) (Bool._≟_ n true)

------------------------------------------------------------------------
-- Derivative

-- The index of the derivative.

D-nullable : ∀ {n} → Tok → P n → Bool
D-nullable t fail         = false
D-nullable t empty        = false
D-nullable t (sat f)      = f t
D-nullable t (p₁ ∣ p₂)    = D-nullable t p₁ ∨ D-nullable t p₂
D-nullable t (nonempty p) = D-nullable t p
D-nullable t (cast _ p)   = D-nullable t p
D-nullable t (p₁ · p₂)    with forced? p₁ | forced? p₂
... | true  | false = D-nullable t p₁
... | false | false = false
... | true  | true  = D-nullable t p₁ ∨ D-nullable t p₂
... | false | true  = D-nullable t p₂

-- D t p is the "derivative" of p with respect to t. It is specified
-- by the equivalence s ∈ D t p ⇔ t ∷ s ∈ p (proved below).

D : ∀ {n} (t : Tok) (p : P n) → P (D-nullable t p)
D t fail         = fail
D t empty        = fail
D t (sat f)      with f t
...              | true  = empty
...              | false = fail
D t (p₁ ∣ p₂)    = D t p₁ ∣ D t p₂
D t (nonempty p) = D t p
D t (cast _ p)   = D t p
D t (p₁ · p₂)    with forced? p₁ | forced? p₂
... | true  | false =   D t    p₁  · ♯? (♭ p₂)
... | false | false = ♯ D t (♭ p₁) · ♯? (♭ p₂)
... | true  | true  =   D t    p₁  · ♯?    p₂ ∣ D t p₂
... | false | true  = ♯ D t (♭ p₁) · ♯?    p₂ ∣ D t p₂

-- D is correct.

D-sound : ∀ {n s t} {p : P n} → s ∈ D t p → t ∷ s ∈ p
D-sound s∈ = D-sound′ _ _ s∈
  where
  sat-lemma : ∀ {s} f t → s ∈ D t (sat f) → T (f t) × s ≡ []
  sat-lemma f t ∈ with f t
  sat-lemma f t empty | true  = (_ , refl)
  sat-lemma f t ()    | false

  D-sound′ : ∀ {s n} (p : P n) t → s ∈ D t p → t ∷ s ∈ p
  D-sound′ fail         t ()
  D-sound′ empty        t ()
  D-sound′ (sat f)      t s∈                  with sat-lemma f t s∈
  ...                                         | (ok , refl) = sat ok
  D-sound′ (p₁ ∣ p₂)    t (∣-left  ∈₁)        = ∣-left (D-sound′ p₁ t ∈₁)
  D-sound′ (p₁ ∣ p₂)    t (∣-right ∈₂)        = ∣-right {p₁ = p₁} (D-sound′ p₂ t ∈₂)
  D-sound′ (nonempty p) t ∈                   = nonempty (D-sound ∈)
  D-sound′ (cast _ p)   t ∈                   = cast (D-sound ∈)
  D-sound′ (p₁ · p₂)    t s∈                  with forced? p₁ | forced? p₂
  D-sound′ (p₁ · p₂)    t (∣-left  (∈₁ · ∈₂)) | true  | true  = D-sound ∈₁ · drop-♭♯ (D-nullable t p₁) ∈₂
  D-sound′ (p₁ · p₂)    t (∣-right ∈₂)        | true  | true  = ⇐ p₁ refl · D-sound′ p₂ t ∈₂
  D-sound′ (p₁ · p₂)    t (∣-left  (∈₁ · ∈₂)) | false | true  = D-sound ∈₁ · drop-♭♯ (D-nullable t (♭ p₁)) ∈₂
  D-sound′ (p₁ · p₂)    t (∣-right ∈₂)        | false | true  = ⇐ (♭ p₁) refl · D-sound′ p₂ t ∈₂
  D-sound′ (p₁ · p₂)    t (∈₁ · ∈₂)           | true  | false = D-sound ∈₁ · drop-♭♯ (D-nullable t    p₁ ) ∈₂
  D-sound′ (p₁ · p₂)    t (∈₁ · ∈₂)           | false | false = D-sound ∈₁ · drop-♭♯ (D-nullable t (♭ p₁)) ∈₂

D-complete : ∀ {n s t} {p : P n} → t ∷ s ∈ p → s ∈ D t p
D-complete {t = t} t∷s∈ = D-complete′ _ t∷s∈ refl
  where
  D-complete′ : ∀ {s s′ n} (p : P n) → s′ ∈ p → s′ ≡ t ∷ s → s ∈ D t p
  D-complete′ fail         ()                   refl
  D-complete′ empty        ()                   refl
  D-complete′ (sat f)      (sat ok)             refl with f t
  D-complete′ (sat f)      (sat ok)             refl | true  = empty
  D-complete′ (sat f)      (sat ())             refl | false
  D-complete′ (p₁ ∣ p₂)    (∣-left  ∈₁)         refl = ∣-left                (D-complete ∈₁)
  D-complete′ (p₁ ∣ p₂)    (∣-right ∈₂)         refl = ∣-right {p₁ = D t p₁} (D-complete ∈₂)
  D-complete′ (nonempty p) (nonempty ∈)         refl = D-complete ∈
  D-complete′ (cast _ p)   (cast ∈)             refl = D-complete ∈
  D-complete′ (p₁ · p₂)    _                    _    with forced? p₁ | forced? p₂
  D-complete′ (p₁ · p₂)    (_·_ {[]}     ∈₁ ∈₂) refl | true  | true  = ∣-right {p₁ = D t p₁ · _} (D-complete ∈₂)
  D-complete′ (p₁ · p₂)    (_·_ {._ ∷ _} ∈₁ ∈₂) refl | true  | true  = ∣-left (D-complete ∈₁ · add-♭♯ (D-nullable t p₁) ∈₂)
  D-complete′ (p₁ · p₂)    (_·_ {[]}     ∈₁ ∈₂) refl | true  | false with ⇒ ∈₁
  D-complete′ (p₁ · p₂)    (_·_ {[]}     ∈₁ ∈₂) refl | true  | false | ()
  D-complete′ (p₁ · p₂)    (_·_ {._ ∷ _} ∈₁ ∈₂) refl | true  | false = D-complete ∈₁ · add-♭♯ (D-nullable t p₁) ∈₂
  D-complete′ (p₁ · p₂)    (_·_ {[]}     ∈₁ ∈₂) refl | false | true  = ∣-right {p₁ = _·_ {n₂ = false} _ _} (D-complete ∈₂)
  D-complete′ (p₁ · p₂)    (_·_ {._ ∷ _} ∈₁ ∈₂) refl | false | true  = ∣-left (D-complete ∈₁ · add-♭♯ (D-nullable t (♭ p₁)) ∈₂)
  D-complete′ (p₁ · p₂)    (_·_ {[]}     ∈₁ ∈₂) refl | false | false with ⇒ ∈₁
  D-complete′ (p₁ · p₂)    (_·_ {[]}     ∈₁ ∈₂) refl | false | false | ()
  D-complete′ (p₁ · p₂)    (_·_ {._ ∷ _} ∈₁ ∈₂) refl | false | false = D-complete ∈₁ · add-♭♯ (D-nullable t (♭ p₁)) ∈₂

D-correct : ∀ {n s t} {p : P n} → s ∈ D t p ⇔ t ∷ s ∈ p
D-correct = equivalence D-sound D-complete

------------------------------------------------------------------------
-- _∈_ is decidable

-- _∈?_ runs a recogniser. Note that the result is yes or no plus a
-- /proof/ verifying that the answer is correct.

infix 4 _∈?_

_∈?_ : ∀ {n} (s : List Tok) (p : P n) → Dec (s ∈ p)
[]    ∈? p = nullable? p
t ∷ s ∈? p with s ∈? D t p
t ∷ s ∈? p | yes s∈Dtp = yes (D-sound s∈Dtp)
t ∷ s ∈? p | no  s∉Dtp = no  (s∉Dtp ∘ D-complete)

-- The last three lines could be replaced by the following one:
--
-- t ∷ s ∈? p = Dec.map D-correct (s ∈? D t p)

------------------------------------------------------------------------
-- Alternative characterisation of equality

infix 5 _∷_
infix 4 _≈′_

-- Two recognisers/languages are equal if their nullability indices
-- are equal and all their derivatives are equal (coinductively). Note
-- that the elements of this type are bisimulations.

data _≈′_ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) : Set where
  _∷_ : n₁ ≡ n₂ → (∀ t → ∞ (D t p₁ ≈′ D t p₂)) → p₁ ≈′ p₂

-- This definition is equivalent to the one above.

≈′-sound : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≈′ p₂ → p₁ ≈ p₂
≈′-sound (refl ∷ rest) {[]}    = Eq.sym index-correct ⟨∘⟩ index-correct
≈′-sound (refl ∷ rest) {t ∷ s} =
  D-correct ⟨∘⟩ ≈′-sound (♭ (rest t)) ⟨∘⟩ Eq.sym D-correct

same-nullability : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
                   p₁ ≈ p₂ → n₁ ≡ n₂
same-nullability p₁≈p₂ =
  Bool.⇔→≡ (index-correct ⟨∘⟩ p₁≈p₂ ⟨∘⟩ Eq.sym index-correct)

D-cong : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} {t} →
         p₁ ≈ p₂ → D t p₁ ≈ D t p₂
D-cong p₁≈p₂ = Eq.sym D-correct ⟨∘⟩ p₁≈p₂ ⟨∘⟩ D-correct

≈′-complete : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≈ p₂ → p₁ ≈′ p₂
≈′-complete p₁≈p₂ =
  same-nullability p₁≈p₂ ∷ λ _ → ♯ ≈′-complete (D-cong p₁≈p₂)

≈′-correct : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≈′ p₂ ⇔ p₁ ≈ p₂
≈′-correct = equivalence ≈′-sound ≈′-complete

------------------------------------------------------------------------
-- The combinator nonempty does not need to be primitive

-- The variant of nonempty which is defined below (nonempty′) makes
-- many recognisers larger, though.

module AlternativeNonempty where

  nonempty′ : ∀ {n} → P n → P false
  nonempty′ fail         = fail
  nonempty′ empty        = fail
  nonempty′ (sat f)      = sat f
  nonempty′ (p₁ ∣ p₂)    = nonempty′ p₁ ∣ nonempty′ p₂
  nonempty′ (nonempty p) = nonempty′ p
  nonempty′ (cast eq p)  = nonempty′ p
  nonempty′ (p₁ · p₂)    with forced? p₁ | forced? p₂
  ... | false | _     = p₁ · p₂
  ... | true  | false = p₁ · p₂
  ... | true  | true  = nonempty′ p₁ ∣ nonempty′ p₂
                      ∣ ♯ nonempty′ p₁ · ♯ nonempty′ p₂

  sound : ∀ {n} {p : P n} → nonempty′ p ≤ nonempty p
  sound {s = []}    pr with ⇒ pr
  ... | ()
  sound {s = _ ∷ _} pr = nonempty (sound′ _ pr refl)
    where
    sound′ : ∀ {n t s s′} (p : P n) →
             s′ ∈ nonempty′ p → s′ ≡ t ∷ s → t ∷ s ∈ p
    sound′ fail         ()                              refl
    sound′ empty        ()                              refl
    sound′ (sat f)      (sat ok)                        refl = sat ok
    sound′ (p₁ ∣ p₂)    (∣-left  pr)                    refl = ∣-left            (sound′ p₁ pr refl)
    sound′ (p₁ ∣ p₂)    (∣-right pr)                    refl = ∣-right {p₁ = p₁} (sound′ p₂ pr refl)
    sound′ (nonempty p) pr                              refl = nonempty (sound′ p pr refl)
    sound′ (cast _ p)   pr                              refl = cast (sound′ p pr refl)
    sound′ (p₁ · p₂)    pr                              _    with forced? p₁ | forced? p₂
    sound′ (p₁ · p₂)    pr                              refl | false | _     = pr
    sound′ (p₁ · p₂)    pr                              refl | true  | false = pr
    sound′ (p₁ · p₂)    (∣-left (∣-left  pr))           refl | true  | true  = cast∈ (proj₂ ListMonoid.identity _) refl $
                                                                                 sound′ p₁ pr refl · ⇐ p₂ refl
    sound′ (p₁ · p₂)    (∣-left (∣-right pr))           refl | true  | true  = ⇐ p₁ refl · sound′ p₂ pr refl
    sound′ (p₁ · p₂)    (∣-right (_·_ {[]}    pr₁ pr₂)) refl | true  | true  with ⇒ pr₁
    ... | ()
    sound′ (p₁ · p₂)    (∣-right (_·_ {_ ∷ _} pr₁ pr₂)) refl | true  | true  with sound {p = p₂} pr₂
    ... | nonempty pr₂′ = sound′ p₁ pr₁ refl · pr₂′

  complete : ∀ {n} {p : P n} → nonempty p ≤ nonempty′ p
  complete (nonempty pr) = complete′ _ pr refl
    where
    complete′ : ∀ {n t s s′} (p : P n) →
                s ∈ p → s ≡ t ∷ s′ → t ∷ s′ ∈ nonempty′ p
    complete′ fail         ()                            refl
    complete′ empty        ()                            refl
    complete′ (sat f)      (sat ok)                      refl = sat ok
    complete′ (p₁ ∣ p₂)    (∣-left pr)                   refl = ∣-left               (complete′ p₁ pr refl)
    complete′ (p₁ ∣ p₂)    (∣-right pr)                  refl = ∣-right {n₁ = false} (complete′ p₂ pr refl)
    complete′ (nonempty p) (nonempty pr)                 refl = complete′ p pr refl
    complete′ (cast _ p)   (cast pr)                     refl = complete′ p pr refl
    complete′ (p₁ · p₂)    pr                            _    with forced? p₁ | forced? p₂
    complete′ (p₁ · p₂)    pr                            refl | false | _     = pr
    complete′ (p₁ · p₂)    pr                            refl | true  | false = pr
    complete′ (p₁ · p₂)    (_·_ {[]}            pr₁ pr₂) refl | true  | true  = ∣-left (∣-right {n₁ = false} (complete′ p₂ pr₂ refl))
    complete′ (p₁ · p₂)    (_·_ {_ ∷ _} {[]}    pr₁ pr₂) refl | true  | true  = cast∈ (sym $ proj₂ ListMonoid.identity _) refl $
                                                                                  ∣-left (∣-left {n₂ = false} (complete′ p₁ pr₁ refl))
    complete′ (p₁ · p₂)    (_·_ {_ ∷ _} {_ ∷ _} pr₁ pr₂) refl | true  | true  = ∣-right {n₁ = false} (complete′ p₁ pr₁ refl ·
                                                                                   complete′ p₂ pr₂ refl)

  correct : ∀ {n} {p : P n} → nonempty′ p ≈ nonempty p
  correct = equivalence sound complete
