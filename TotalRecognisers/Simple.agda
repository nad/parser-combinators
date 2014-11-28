------------------------------------------------------------------------
-- Simple recognisers
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])

-- The recognisers are parametrised on the alphabet.

module TotalRecognisers.Simple
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         -- The tokens must come with decidable equality.
         where

open import Algebra
open import Coinduction
open import Data.Bool hiding (_≟_)
import Data.Bool.Properties as Bool
private
  module BoolCS = CommutativeSemiring Bool.commutativeSemiring-∧-∨
open import Function
open import Data.List
open import Data.Product
open import Relation.Nullary

------------------------------------------------------------------------
-- Recogniser combinators

infixl 10 _·_
infixl  5 _∣_

mutual

  -- The index is true if the corresponding language contains the
  -- empty string (is nullable).

  data P : Bool → Set where
    fail  : P false
    empty : P true
    tok   : Tok → P false
    _∣_   : ∀ {n₁ n₂} → P n₁ →            P n₂ → P (n₁ ∨ n₂)
    _·_   : ∀ {n₁ n₂} → P n₁ → ∞⟨ not n₁ ⟩P n₂ → P (n₁ ∧ n₂)

  -- Coinductive if the index is true.

  ∞⟨_⟩P : Bool → Bool → Set
  ∞⟨ true  ⟩P n = ∞ (P n)
  ∞⟨ false ⟩P n =    P n

------------------------------------------------------------------------
-- Conditional coinduction helpers

delayed? : ∀ {b n} → ∞⟨ b ⟩P n → Bool
delayed? {b = b} _ = b

♭? : ∀ {b n} → ∞⟨ b ⟩P n → P n
♭? {true}  x = ♭ x
♭? {false} x =   x

♯? : ∀ {b n} → P n → ∞⟨ b ⟩P n
♯? {true}  x = ♯ x
♯? {false} x =   x

-- A lemma.

♭?♯? : ∀ b {n} {p : P n} → ♭? {b} (♯? p) ≡ p
♭?♯? true  = refl
♭?♯? false = refl

------------------------------------------------------------------------
-- Semantics

-- The semantics is defined inductively: s ∈ p iff the string s is
-- contained in the language defined by p.

infix 4 _∈_

data _∈_ : ∀ {n} → List Tok → P n → Set where
  empty   : [] ∈ empty
  tok     : ∀ {t} → [ t ] ∈ tok t
  ∣-left  : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
            s ∈ p₁ → s ∈ p₁ ∣ p₂
  ∣-right : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
            s ∈ p₂ → s ∈ p₁ ∣ p₂
  _·_     : ∀ {s₁ s₂ n₁ n₂} {p₁ : P n₁} {p₂ : ∞⟨ not n₁ ⟩P n₂} →
            s₁ ∈ p₁ → s₂ ∈ ♭? p₂ → s₁ ++ s₂ ∈ p₁ · p₂

-- A lemma.

cast : ∀ {n} {p p′ : P n} {s} → p ≡ p′ → s ∈ p → s ∈ p′
cast refl s∈ = s∈

------------------------------------------------------------------------
-- Nullability

-- The nullability index is correct.

⇒ : ∀ {n} {p : P n} → [] ∈ p → n ≡ true
⇒ pr = ⇒′ pr refl
  where
  ⇒′ : ∀ {n s} {p : P n} → s ∈ p → s ≡ [] → n ≡ true
  ⇒′ empty                   refl = refl
  ⇒′ tok                     ()
  ⇒′ (∣-left            pr₁) refl with ⇒ pr₁
  ⇒′ (∣-left            pr₁) refl | refl = refl
  ⇒′ (∣-right           pr₂) refl with ⇒ pr₂
  ⇒′ (∣-right {n₁ = n₁} pr₂) refl | refl = proj₂ BoolCS.zero n₁
  ⇒′ (_·_ {[]}    pr₁ pr₂)   refl = cong₂ _∧_ (⇒ pr₁) (⇒ pr₂)
  ⇒′ (_·_ {_ ∷ _} pr₁ pr₂)   ()

⇐ : ∀ {n} (p : P n) → n ≡ true → [] ∈ p
⇐ fail                         ()
⇐ empty                        refl = empty
⇐ (tok t)                      ()
⇐ (_∣_ {true}           p₁ p₂) refl = ∣-left            (⇐ p₁ refl)
⇐ (_∣_ {false} {true}   p₁ p₂) refl = ∣-right {p₁ = p₁} (⇐ p₂ refl)
⇐ (_∣_ {false} {false}  p₁ p₂) ()
⇐ (_·_ {true}  p₁ p₂)          refl = ⇐ p₁ refl · ⇐ p₂ refl
⇐ (_·_ {false} p₁ p₂)          ()

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

-- D-nullable and D are placed in a mutual block to ensure that the
-- underscores in the definition of D-nullable can be solved by
-- constraints introduced in the body of D. The functions are not
-- actually mutually recursive.

mutual

  -- The index of the derivative. The right-hand sides (excluding
  -- t′ ≟ t and delayed? p₂) are inferable, but included here so that
  -- they can easily be inspected.

  D-nullable : ∀ {n} → Tok → P n → Bool
  D-nullable t fail      = false
  D-nullable t empty     = false
  D-nullable t (tok t′)  with t′ ≟ t
  D-nullable t (tok t′)  | yes t′≡t = true
  D-nullable t (tok t′)  | no  t′≢t = false
  D-nullable t (p₁ ∣ p₂) = D-nullable t p₁ ∨ D-nullable t p₂
  D-nullable t (p₁ · p₂) with delayed? p₂
  D-nullable t (p₁ · p₂) | true  = D-nullable t p₁ ∧ _
  D-nullable t (p₁ · p₂) | false = D-nullable t p₁ ∧ _ ∨ D-nullable t p₂

  -- D t p is the "derivative" of p with respect to t. It is specified
  -- by the equivalence s ∈ D t p ⇔ t ∷ s ∈ p (proved below).

  D : ∀ {n} (t : Tok) (p : P n) → P (D-nullable t p)
  D t fail      = fail
  D t empty     = fail
  D t (tok t′)  with t′ ≟ t
  D t (tok t′)  | yes t′≡t = empty
  D t (tok t′)  | no  t′≢t = fail
  D t (p₁ ∣ p₂) = D t p₁ ∣ D t p₂
  D t (p₁ · p₂) with delayed? p₂
  D t (p₁ · p₂) | true  = D t p₁ · ♯? (♭ p₂)
  D t (p₁ · p₂) | false = D t p₁ · ♯?    p₂ ∣ D t p₂

-- D is correct.

D-sound : ∀ {s n} {t} {p : P n} → s ∈ D t p → t ∷ s ∈ p
D-sound s∈ = D-sound′ _ _ s∈
  where
  D-sound′ : ∀ {s n} t (p : P n) → s ∈ D t p → t ∷ s ∈ p
  D-sound′ t fail                ()
  D-sound′ t empty               ()
  D-sound′ t (tok t′)            _                   with t′ ≟ t
  D-sound′ t (tok .t)            empty               | yes refl = tok
  D-sound′ t (tok t′)            ()                  | no  t′≢t
  D-sound′ t (p₁ ∣ p₂)           (∣-left  ∈₁)        = ∣-left            (D-sound′ t p₁ ∈₁)
  D-sound′ t (p₁ ∣ p₂)           (∣-right ∈₂)        = ∣-right {p₁ = p₁} (D-sound′ t p₂ ∈₂)
  D-sound′ t (_·_ {true}  p₁ p₂) (∣-left  (∈₁ · ∈₂)) = D-sound′ t p₁ ∈₁ · cast (♭?♯? (not (D-nullable t p₁))) ∈₂
  D-sound′ t (_·_ {true}  p₁ p₂) (∣-right ∈₂)        = ⇐ p₁ refl · D-sound′ t p₂ ∈₂
  D-sound′ t (_·_ {false} p₁ p₂) (∈₁ · ∈₂)           = D-sound′ t p₁ ∈₁ · cast (♭?♯? (not (D-nullable t p₁))) ∈₂

D-complete : ∀ {s n} {t} {p : P n} → t ∷ s ∈ p → s ∈ D t p
D-complete {t = t} t∷s∈ = D-complete′ _ t∷s∈ refl
  where
  D-complete′ : ∀ {s s′ n} (p : P n) → s′ ∈ p → s′ ≡ t ∷ s → s ∈ D t p
  D-complete′         fail     ()  refl
  D-complete′         empty    ()  refl
  D-complete′         (tok t′) _   refl with t′ ≟ t
  D-complete′         (tok .t) tok refl | yes refl = empty
  D-complete′ {[]}    (tok .t) tok refl | no  t′≢t with t′≢t refl
  D-complete′ {[]}    (tok .t) tok refl | no  t′≢t | ()
  D-complete′ {_ ∷ _} (tok t′) ()  refl | no  t′≢t
  D-complete′ (p₁ ∣ p₂)           (∣-left  ∈₁)         refl = ∣-left                    (D-complete ∈₁)
  D-complete′ (p₁ ∣ p₂)           (∣-right ∈₂)         refl = ∣-right {p₁ = D t p₁}     (D-complete ∈₂)
  D-complete′ (_·_ {true}  p₁ p₂) (_·_ {[]}     ∈₁ ∈₂) refl = ∣-right {p₁ = D t p₁ · _} (D-complete ∈₂)
  D-complete′ (_·_ {true}  p₁ p₂) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∣-left (D-complete ∈₁ · cast (sym (♭?♯? (not (D-nullable t p₁)))) ∈₂)
  D-complete′ (_·_ {false} p₁ p₂) (_·_ {[]}     ∈₁ ∈₂) refl with ⇒ ∈₁
  D-complete′ (_·_ {false} p₁ p₂) (_·_ {[]}     ∈₁ ∈₂) refl | ()
  D-complete′ (_·_ {false} p₁ p₂) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = D-complete ∈₁ · cast (sym (♭?♯? (not (D-nullable t p₁)))) ∈₂

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
