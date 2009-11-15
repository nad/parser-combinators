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
open import Data.Function
open import Data.List as List using (List; []; _∷_; _++_; [_])
private
  module ListMonoid {A} = Monoid (List.monoid A)
open import Data.Product
open import Relation.Binary.PropositionalEquality
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
-- Recogniser combinators

infixl 10 _·_
infixl  5 _∣_

-- The index is true if the corresponding language contains the empty
-- string (is nullable).

data P : Bool → Set where
  ∅        : P false
  ε        : P true
  sat      : (Tok → Bool) → P false
  _∣_      : ∀ {n₁ n₂} →     P n₁     →     P n₂     → P (n₁ ∨ n₂)
  _·_      : ∀ {n₁ n₂} → ∞? (P n₁) n₂ → ∞? (P n₂) n₁ → P (n₁ ∧ n₂)
  nonempty : ∀ {n} → P n → P false
  cast     : ∀ {n₁ n₂} → n₁ ≡ n₂ → P n₁ → P n₂

-- Note that ∅, nonempty and cast could be defined as derived
-- combinators. (For cast this is obvious, for ∅ and nonempty see
-- below, and note that the proof in
-- TotalRecognisers.LeftRecursion.ExpressiveStrength does not rely on
-- these constructors.) However, Agda uses /guarded/ corecursion, so
-- the fact that nonempty and cast are constructors can be very
-- convenient when constructing other recognisers.

-- For an example of the use of nonempty, see the Kleene star example
-- in TotalRecognisers.LeftRecursion.Lib. For examples of the use of
-- cast, see TotalRecognisers.LeftRecursion.ExpressiveStrength and
-- TotalRecognisers.LeftRecursion.NotOnlyContextFree.

------------------------------------------------------------------------
-- Semantics

-- The semantics is defined inductively: s ∈ p iff the string s is
-- contained in the language defined by p.

infix 4 _∈_

data _∈_ : ∀ {n} → List Tok → P n → Set where
  ε        : [] ∈ ε
  sat      : ∀ {f t} → T (f t) → [ t ] ∈ sat f
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

infix 4 _≤_ _≈_

-- p₁ ≤ p₂ iff the language (defined by) p₂ contains all the strings
-- in the language p₁.

_≤_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≤ p₂ = ∀ {s} → s ∈ p₁ → s ∈ p₂

-- p₁ ≈ p₂ iff the languages p₁ and p₂ contain the same strings.

_≈_ : ∀ {n₁ n₂} → P n₁ → P n₂ → Set
p₁ ≈ p₂ = p₁ ≤ p₂ × p₂ ≤ p₁

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
leftRight = ⟪ ♯ leftRight ⟫ · ⟪ ♯ leftRight ⟫

-- Note that leftRight is equivalent to ∅, so ∅ does not need to be a
-- primitive combinator.

leftRight≈∅ : leftRight ≈ ∅
leftRight≈∅ = ((λ {_} → ≤∅) , λ ())
  where
  ≤∅ : ∀ {s A} → s ∈ leftRight → A
  ≤∅ (∈₁ · ∈₂) = ≤∅ ∈₁

-- For more examples, see TotalRecognisers.LeftRecursion.Lib.

------------------------------------------------------------------------
-- Nullability

-- The nullability index is correct.

⇒ : ∀ {n} {p : P n} → [] ∈ p → n ≡ true
⇒ pr = ⇒′ pr refl
  where
  ⇒′ : ∀ {n s} {p : P n} → s ∈ p → s ≡ [] → n ≡ true
  ⇒′ ε                     refl = refl
  ⇒′ (sat _)               ()
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
⇐ (sat f)                      ()
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

-- The index of the derivative. Most of the right-hand sides are
-- inferable, but they are included here so that they can easily be
-- inspected.

∂n : ∀ {n} → P n → Tok → Bool
∂n ∅                 t = false
∂n ε                 t = false
∂n (sat f)           t = f t
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
∂ (sat f)           t with f t
...                   | true  = ε
...                   | false = ∅
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
  sat-lemma : ∀ {s} f t → s ∈ ∂ (sat f) t → T (f t) × s ≡ []
  sat-lemma f t ∈ with f t
  sat-lemma f t ε  | true  = (_ , refl)
  sat-lemma f t () | false

  ∂-sound′ : ∀ {s n} (p : P n) t → s ∈ ∂ p t → t ∷ s ∈ p
  ∂-sound′ ∅                 t ()
  ∂-sound′ ε                 t ()
  ∂-sound′ (sat f)           t s∈             with sat-lemma f t s∈
  ...                                         | (ok , refl) = sat ok
  ∂-sound′ (p₁ ∣ p₂)         t (∣ˡ ∈₁)        = ∣ˡ (∂-sound′ p₁ t ∈₁)
  ∂-sound′ (p₁ ∣ p₂)         t (∣ʳ ∈₂)        = ∣ʳ {p₁ = p₁} (∂-sound′ p₂ t ∈₂)
  ∂-sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) t (∣ˡ (∈₁ · ∈₂)) = ∂-sound ∈₁ · drop-♭♯ (∂n p₁ t) ∈₂
  ∂-sound′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) t (∣ʳ ∈₂)        = ⇐ p₁ refl · ∂-sound′ p₂ t ∈₂
  ∂-sound′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) t (∈₁ · ∈₂)      = ∂-sound ∈₁ · drop-♭♯ (∂n p₁ t) ∈₂
  ∂-sound′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) t (∣ˡ (∈₁ · ∈₂)) = ∂-sound ∈₁ · drop-♭♯ (∂n (♭ p₁) t) ∈₂
  ∂-sound′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) t (∣ʳ ∈₂)        = ⇐ (♭ p₁) refl · ∂-sound′ p₂ t ∈₂
  ∂-sound′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) t (∈₁ · ∈₂)      = ∂-sound ∈₁ · drop-♭♯ (∂n (♭ p₁) t) ∈₂
  ∂-sound′ (nonempty p)      t ∈              = nonempty (∂-sound ∈)
  ∂-sound′ (cast _ p)        t ∈              = cast (∂-sound ∈)

∂-complete : ∀ {s n} {p : P n} {t} → t ∷ s ∈ p → s ∈ ∂ p t
∂-complete {t = t} t∷s∈ = ∂-complete′ _ t∷s∈ refl
  where
  ∂-complete′ : ∀ {s s′ n} (p : P n) → s′ ∈ p → s′ ≡ t ∷ s → s ∈ ∂ p t
  ∂-complete′ ∅                 ()                   refl
  ∂-complete′ ε                 ()                   refl
  ∂-complete′ (sat f)           (sat ok)             refl with f t
  ∂-complete′ (sat f)           (sat ok)             refl | true  = ε
  ∂-complete′ (sat f)           (sat ())             refl | false
  ∂-complete′ (p₁ ∣ p₂)         (∣ˡ ∈₁)              refl = ∣ˡ (∂-complete ∈₁)
  ∂-complete′ (p₁ ∣ p₂)         (∣ʳ ∈₂)              refl = ∣ʳ {p₁ = ∂ p₁ t} (∂-complete ∈₂)
  ∂-complete′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (_·_ {[]}     ∈₁ ∈₂) refl = ∣ʳ {p₁ = ⟨ ∂ p₁ t ⟩ · _} (∂-complete ∈₂)
  ∂-complete′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∣ˡ (∂-complete ∈₁ · add-♭♯ (∂n p₁ t) ∈₂)
  ∂-complete′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl with ⇒ ∈₁
  ∂-complete′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl | ()
  ∂-complete′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∂-complete ∈₁ · add-♭♯ (∂n p₁ t) ∈₂
  ∂-complete′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) (_·_ {[]}     ∈₁ ∈₂) refl = ∣ʳ {p₁ = ⟪ _ ⟫ · _} (∂-complete ∈₂)
  ∂-complete′ (⟪ p₁ ⟫ · ⟨ p₂ ⟩) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∣ˡ (∂-complete ∈₁ · add-♭♯ (∂n (♭ p₁) t) ∈₂)
  ∂-complete′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl with ⇒ ∈₁
  ∂-complete′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) (_·_ {[]}     ∈₁ ∈₂) refl | ()
  ∂-complete′ (⟪ p₁ ⟫ · ⟪ p₂ ⟫) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∂-complete ∈₁ · add-♭♯ (∂n (♭ p₁) t) ∈₂
  ∂-complete′ (nonempty p)      (nonempty ∈)         refl = ∂-complete ∈
  ∂-complete′ (cast _ p)        (cast ∈)             refl = ∂-complete ∈

------------------------------------------------------------------------
-- _∈_ is decidable

-- _∈?_ runs a recogniser. Note that the result is yes or no plus a
-- /proof/ verifying that the answer is correct.

infix 4 _∈?_

_∈?_ : ∀ {n} (s : List Tok) (p : P n) → Dec (s ∈ p)
[]    ∈? p = nullable? p
t ∷ s ∈? p with s ∈? ∂ p t
t ∷ s ∈? p | yes s∈∂pt = yes (∂-sound s∈∂pt)
t ∷ s ∈? p | no  s∉∂pt = no  (s∉∂pt ∘ ∂-complete)

------------------------------------------------------------------------
-- Alternative characterisation of equality

infix 5 _∷_
infix 4 _≋_

-- Two recognisers/languages are equal if their nullability indices
-- are equal and all their derivatives are equal (coinductively). Note
-- that the members of this type are bisimulations.

data _≋_ {n₁ n₂} (p₁ : P n₁) (p₂ : P n₂) : Set where
  _∷_ : n₁ ≡ n₂ → (∀ t → ∞ (∂ p₁ t ≋ ∂ p₂ t)) → p₁ ≋ p₂

-- This definition is equivalent to the one above.

same-nullability : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
                   p₁ ≈ p₂ → n₁ ≡ n₂
same-nullability {n₁ = true}  p₁≈p₂ = sym $ ⇒ $ proj₁ p₁≈p₂ $ ⇐ _ refl
same-nullability {n₁ = false} p₁≈p₂ = sym $ Bool.¬-not $ helper p₁≈p₂
  where
  helper : ∀ {n₂} {p₁ : P false} {p₂ : P n₂} →
           p₁ ≈ p₂ → n₂ ≢ true
  helper p₁≈p₂ refl with ⇒ $ proj₂ p₁≈p₂ $ ⇐ _ refl
  ... | ()

∂-cong : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} {t} →
         p₁ ≤ p₂ → ∂ p₁ t ≤ ∂ p₂ t
∂-cong p₁≤p₂ s∈∂p₁t = ∂-complete (p₁≤p₂ (∂-sound s∈∂p₁t))

≋-sym : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≋ p₂ → p₂ ≋ p₁
≋-sym (refl ∷ rest) = refl ∷ λ t → ♯ ≋-sym (♭ (rest t))

≋-sound : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≋ p₂ → p₁ ≈ p₂
≋-sound p₁≋p₂ = ((λ {_} → lemma p₁≋p₂) , λ {_} → lemma (≋-sym p₁≋p₂))
  where
  lemma : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≋ p₂ → p₁ ≤ p₂
  lemma (refl ∷ rest) {[]}    []∈p₁  = ⇐ _ (⇒ []∈p₁)
  lemma (refl ∷ rest) {t ∷ s} t∷s∈p₁ =
    ∂-sound (lemma (♭ (rest t)) (∂-complete t∷s∈p₁))

≋-complete : ∀ {n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} → p₁ ≈ p₂ → p₁ ≋ p₂
≋-complete {n₁} {n₂} p₁≈p₂ with Bool._≟_ n₁ n₂
≋-complete p₁≈p₂ | yes refl =
  refl ∷ λ t → ♯ ≋-complete ((λ {_} → ∂-cong (proj₁ p₁≈p₂))
                            , λ {_} → ∂-cong (proj₂ p₁≈p₂)
                            )
≋-complete p₁≈p₂ | no n₁≢n₂ with n₁≢n₂ $ same-nullability p₁≈p₂
... | ()

------------------------------------------------------------------------
-- The combinator nonempty does not need to be primitive

-- The variant of nonempty which is defined below (nonempty′) makes
-- many recognisers larger, though.

module AlternativeNonempty where

  nonempty′ : ∀ {n} → P n → P false
  nonempty′ ∅                 = ∅
  nonempty′ ε                 = ∅
  nonempty′ (sat f)           = sat f
  nonempty′ (p₁ ∣ p₂)         = nonempty′ p₁ ∣ nonempty′ p₂
  nonempty′ (⟪ p₁ ⟫ ·   p₂  ) = ⟪ p₁ ⟫ ·   p₂
  nonempty′ (⟨ p₁ ⟩ · ⟪ p₂ ⟫) = ⟨ p₁ ⟩ · ⟪ p₂ ⟫
  nonempty′ (⟨ p₁ ⟩ · ⟨ p₂ ⟩) = nonempty′ p₁ ∣ nonempty′ p₂
                              ∣ ♯? (nonempty′ p₁) · ♯? (nonempty′ p₂)
  nonempty′ (nonempty p)      = nonempty′ p
  nonempty′ (cast eq p)       = nonempty′ p

  sound : ∀ {n} {p : P n} → nonempty′ p ≤ nonempty p
  sound {s = []}    pr with ⇒ pr
  ... | ()
  sound {s = _ ∷ _} pr = nonempty (sound′ _ pr refl)
    where
    sound′ : ∀ {n t s s′} (p : P n) →
             s′ ∈ nonempty′ p → s′ ≡ t ∷ s → t ∷ s ∈ p
    sound′ ∅                 ()                         refl
    sound′ ε                 ()                         refl
    sound′ (sat f)           (sat ok)                   refl = sat ok
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

  complete : ∀ {n} {p : P n} → nonempty p ≤ nonempty′ p
  complete (nonempty pr) = complete′ _ pr refl
    where
    complete′ : ∀ {n t s s′} (p : P n) →
                s ∈ p → s ≡ t ∷ s′ → t ∷ s′ ∈ nonempty′ p
    complete′ ∅                 ()                            refl
    complete′ ε                 ()                            refl
    complete′ (sat f)           (sat ok)                      refl = sat ok
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
