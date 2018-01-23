------------------------------------------------------------------------
-- This module establishes that the recognisers are as expressive as
-- possible when the alphabet is Bool (this could be generalised to
-- arbitrary finite alphabets), whereas this is not the case when the
-- alphabet is ℕ
------------------------------------------------------------------------

module TotalRecognisers.LeftRecursion.ExpressiveStrength where

open import Algebra
open import Coinduction
open import Data.Bool as Bool hiding (_∧_)
open import Data.Empty
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Data.List
import Data.List.Properties as ListProp
open import Data.List.Reverse
open import Data.Nat as Nat
open import Data.Nat.InfinitelyOften as Inf
import Data.Nat.Properties as NatProp
open import Data.Product
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Negation
private
  module ListMonoid {A : Set} = Monoid (ListProp.++-monoid A)
  module NatOrder             = DecTotalOrder NatProp.≤-decTotalOrder

import TotalRecognisers.LeftRecursion
open TotalRecognisers.LeftRecursion Bool using (_∧_; left-zero)
private
  open module LR {Tok : Set} = TotalRecognisers.LeftRecursion Tok
    hiding (P; ∞⟨_⟩P; _∧_; left-zero; _∷_)

  P : Set → Bool → Set
  P Tok = LR.P {Tok}

  ∞⟨_⟩P : Bool → Set → Bool → Set
  ∞⟨ b ⟩P Tok n = LR.∞⟨_⟩P {Tok} b n

open import TotalRecognisers.LeftRecursion.Lib Bool hiding (_∷_)

------------------------------------------------------------------------
-- A boring lemma

private

  lemma : (f : List Bool → Bool) →
          (false ∧ f [ true ] ∨ false ∧ f [ false ]) ∨ f [] ≡ f []
  lemma f = cong₂ (λ b₁ b₂ → (b₁ ∨ b₂) ∨ f [])
                  (left-zero (f [ true  ]))
                  (left-zero (f [ false ]))

------------------------------------------------------------------------
-- Expressive strength

-- For every grammar there is an equivalent decidable predicate.

grammar⇒pred : ∀ {Tok n} (p : P Tok n) →
               ∃ λ (f : List Tok → Bool) → ∀ {s} → s ∈ p ⇔ T (f s)
grammar⇒pred p =
  ((λ s → ⌊ s ∈? p ⌋) , λ {_} → equivalence fromWitness toWitness)

-- When the alphabet is Bool the other direction holds: for every
-- decidable predicate there is a corresponding grammar.
--
-- Note that the grammars constructed by the proof are all "infinite
-- LL(1)".

pred⇒grammar : (f : List Bool → Bool) →
               ∃ λ (p : P Bool (f [])) → ∀ {s} → s ∈ p ⇔ T (f s)
pred⇒grammar f =
  (p f , λ {s} → equivalence (p-sound f) (p-complete f s))
  where
  p : (f : List Bool → Bool) → P Bool (f [])
  p f = cast (lemma f)
      ( ♯? (sat id ) · ♯ p (f ∘ _∷_ true )
      ∣ ♯? (sat not) · ♯ p (f ∘ _∷_ false)
      ∣ accept-if-true (f [])
      )

  p-sound : ∀ f {s} → s ∈ p f → T (f s)
  p-sound f (cast (∣-right s∈)) with AcceptIfTrue.sound (f []) s∈
  ... | (refl , ok) = ok
  p-sound f (cast (∣-left (∣-left (t∈ · s∈)))) with drop-♭♯ (f [ true  ]) t∈
  ... | sat {t = true}  _  = p-sound (f ∘ _∷_ true ) s∈
  ... | sat {t = false} ()
  p-sound f (cast (∣-left (∣-right (t∈ · s∈)))) with drop-♭♯ (f [ false ]) t∈
  ... | sat {t = false} _  = p-sound (f ∘ _∷_ false) s∈
  ... | sat {t = true}  ()

  p-complete : ∀ f s → T (f s) → s ∈ p f
  p-complete f [] ok =
    cast (∣-right {n₁ = false ∧ f [ true ] ∨ false ∧ f [ false ]} $
      AcceptIfTrue.complete ok)
  p-complete f (true  ∷ bs) ok =
    cast (∣-left $ ∣-left $
      add-♭♯ (f [ true  ]) (sat _) ·
      p-complete (f ∘ _∷_ true ) bs ok)
  p-complete f (false ∷ bs) ok =
    cast (∣-left $ ∣-right {n₁ = false ∧ f [ true ]} $
      add-♭♯ (f [ false ]) (sat _) ·
      p-complete (f ∘ _∷_ false) bs ok)

-- An alternative proof which uses a left recursive definition of the
-- grammar to avoid the use of a cast.

pred⇒grammar′ : (f : List Bool → Bool) →
                ∃ λ (p : P Bool (f [])) → ∀ {s} → s ∈ p ⇔ T (f s)
pred⇒grammar′ f =
  (p f , λ {s} → equivalence (p-sound f) (p-complete f s))
  where
  extend : {A B : Set} → (List A → B) → A → (List A → B)
  extend f x = λ xs → f (xs ∷ʳ x)

  p : (f : List Bool → Bool) → P Bool (f [])
  p f = ♯ p (extend f true ) · ♯? (sat id )
      ∣ ♯ p (extend f false) · ♯? (sat not)
      ∣ accept-if-true (f [])

  p-sound : ∀ f {s} → s ∈ p f → T (f s)
  p-sound f (∣-right s∈) with AcceptIfTrue.sound (f []) s∈
  ... | (refl , ok) = ok
  p-sound f (∣-left (∣-left (s∈ · t∈))) with drop-♭♯ (f [ true  ]) t∈
  ... | sat {t = true}  _  = p-sound (extend f true ) s∈
  ... | sat {t = false} ()
  p-sound f (∣-left (∣-right (s∈ · t∈))) with drop-♭♯ (f [ false ]) t∈
  ... | sat {t = false} _  = p-sound (extend f false) s∈
  ... | sat {t = true}  ()

  p-complete′ : ∀ f {s} → Reverse s → T (f s) → s ∈ p f
  p-complete′ f [] ok =
    ∣-right {n₁ = false} $ AcceptIfTrue.complete ok
  p-complete′ f (bs ∶ rs ∶ʳ true ) ok =
    ∣-left {n₁ = false} $ ∣-left {n₁ = false} $
      p-complete′ (extend f true ) rs ok ·
      add-♭♯ (f [ true  ]) (sat _)
  p-complete′ f (bs ∶ rs ∶ʳ false) ok =
    ∣-left {n₁ = false} $ ∣-right {n₁ = false} $
      p-complete′ (extend f false) rs ok ·
      add-♭♯ (f [ false ]) (sat _)

  p-complete : ∀ f s → T (f s) → s ∈ p f
  p-complete f s = p-complete′ f (reverseView s)

-- If infinite alphabets are allowed the result is different: there
-- are decidable predicates which cannot be realised as grammars. The
-- proof below shows that a recogniser for natural number strings
-- cannot accept exactly the strings of the form "nn".

module NotExpressible where

  -- A "pair" is a string containing two equal elements.

  pair : ℕ → List ℕ
  pair n = n ∷ n ∷ []

  -- OnlyPairs p is inhabited iff p only accepts pairs and empty
  -- strings. (Empty strings are allowed due to the presence of the
  -- nonempty combinator.)

  OnlyPairs : ∀ {n} → P ℕ n → Set
  OnlyPairs p = ∀ {n s} → n ∷ s ∈ p → s ≡ [ n ]

  -- ManyPairs p is inhabited iff p accepts infinitely many pairs.

  ManyPairs : ∀ {n} → P ℕ n → Set
  ManyPairs p = Inf (λ n → pair n ∈ p)

  -- AcceptsNonEmptyString p is inhabited iff p accepts a non-empty
  -- string.

  AcceptsNonEmptyString : ∀ {Tok n} → P Tok n → Set
  AcceptsNonEmptyString p = ∃₂ λ t s → t ∷ s ∈ p

  -- If a recogniser does not accept any non-empty string, then it
  -- either accepts the empty string or no string at all.

  nullable-or-fail : ∀ {Tok n} {p : P Tok n} →
                     ¬ AcceptsNonEmptyString p →
                     [] ∈ p ⊎ (∀ s → ¬ s ∈ p)
  nullable-or-fail {p = p} ¬a with [] ∈? p
  ... | yes []∈p = inj₁ []∈p
  ... | no  []∉p = inj₂ helper
    where
    helper : ∀ s → ¬ s ∈ p
    helper []      = []∉p
    helper (t ∷ s) = ¬a ∘ _,_ t ∘ _,_ s

  -- If p₁ · p₂ accepts infinitely many pairs, and nothing but pairs
  -- (or the empty string), then at most one of p₁ and p₂ accepts a
  -- non-empty string. This follows because p₁ and p₂ are independent
  -- of each other. For instance, if p₁ accepted n and p₂ accepted i
  -- and j, then p₁ · p₂ would accept both ni and nj, and if p₁
  -- accepted mm and p₂ accepted n then p₁ · p₂ would accept mmn.

  at-most-one : ∀ {n₁ n₂} {p₁ : ∞⟨ n₂ ⟩P ℕ n₁} {p₂ : ∞⟨ n₁ ⟩P ℕ n₂} →
                OnlyPairs (p₁ · p₂) →
                ManyPairs (p₁ · p₂) →
                AcceptsNonEmptyString (♭? p₁) →
                AcceptsNonEmptyString (♭? p₂) → ⊥
  at-most-one op mp (n₁ , s₁ , n₁s₁∈p₁) (n₂ , s₂ , n₂s₂∈p₂)
    with op (n₁s₁∈p₁ · n₂s₂∈p₂)
  at-most-one _ _ (_ , _ ∷ []    , _) (_ , _ , _) | ()
  at-most-one _ _ (_ , _ ∷ _ ∷ _ , _) (_ , _ , _) | ()
  at-most-one {p₁ = p₁} {p₂} op mp
              (n , [] , n∈p₁) (.n , .[] , n∈p₂) | refl =
    twoDifferentWitnesses mp helper
    where
    ¬pair : ∀ {i s} → s ∈ p₁ · p₂ → n ≢ i → s ≢ pair i
    ¬pair (_·_ {s₁ = []}          _ ii∈p₂) n≢i refl with op (n∈p₁ · ii∈p₂)
    ... | ()
    ¬pair (_·_ {s₁ = i  ∷ []}     i∈p₁  _) n≢i refl with op (i∈p₁ · n∈p₂)
    ¬pair (_·_ {s₁ = .n ∷ []}     n∈p₁  _) n≢n refl | refl = n≢n refl
    ¬pair (_·_ {s₁ = i ∷ .i ∷ []} ii∈p₁ _) n≢i refl with op (ii∈p₁ · n∈p₂)
    ... | ()
    ¬pair (_·_ {s₁ = _ ∷ _ ∷ _ ∷ _} _ _) _ ()

    helper : ¬ ∃₂ λ i j → i ≢ j × pair i ∈ p₁ · p₂ × pair j ∈ p₁ · p₂
    helper (i  , j , i≢j , ii∈ , jj∈) with Nat._≟_ n i
    helper (.n , j , n≢j , nn∈ , jj∈) | yes refl = ¬pair jj∈ n≢j refl
    helper (i  , j , i≢j , ii∈ , jj∈) | no  n≢i  = ¬pair ii∈ n≢i refl

  -- OnlyPairs and ManyPairs are mutually exclusive.

  ¬pairs : ∀ {n} (p : P ℕ n) → OnlyPairs p → ManyPairs p → ⊥
  ¬pairs fail op mp = witness mp (helper ∘ proj₂)
    where
    helper : ∀ {t} → ¬ pair t ∈ fail
    helper ()
  ¬pairs empty op mp = witness mp (helper ∘ proj₂)
    where
    helper : ∀ {t} → ¬ pair t ∈ empty
    helper ()
  ¬pairs (sat f) op mp = witness mp (helper ∘ proj₂)
    where
    helper : ∀ {t} → ¬ pair t ∈ sat f
    helper ()
  ¬pairs (nonempty p) op mp =
    ¬pairs p (op ∘ nonempty) (Inf.map helper mp)
    where
    helper : ∀ {n} → pair n ∈ nonempty p → pair n ∈ p
    helper (nonempty pr) = pr
  ¬pairs (cast eq p) op mp = ¬pairs p (op ∘ cast) (Inf.map helper mp)
    where
    helper : ∀ {n} → pair n ∈ cast eq p → pair n ∈ p
    helper (cast pr) = pr

  -- The most interesting cases are _∣_ and _·_. For the choice
  -- combinator we make use of the fact that if p₁ ∣ p₂ accepts
  -- infinitely many pairs, then at least one of p₁ and p₂ do. (We are
  -- deriving a contradiction, so the use of classical reasoning is
  -- unproblematic.)

  ¬pairs (p₁ ∣ p₂) op mp = commutes-with-∪ (Inf.map split mp) helper
    where
    helper : ¬ (ManyPairs p₁ ⊎ ManyPairs p₂)
    helper (inj₁ mp₁) = ¬pairs p₁ (op ∘ ∣-left)            mp₁
    helper (inj₂ mp₂) = ¬pairs p₂ (op ∘ ∣-right {p₁ = p₁}) mp₂

    split : ∀ {s} → s ∈ p₁ ∣ p₂ → s ∈ p₁ ⊎ s ∈ p₂
    split (∣-left  s∈p₁) = inj₁ s∈p₁
    split (∣-right s∈p₂) = inj₂ s∈p₂

  -- For the sequencing combinator we make use of the fact that the
  -- argument recognisers cannot both accept non-empty strings.

  ¬pairs (p₁ · p₂) op mp =
    excluded-middle λ a₁? →
    excluded-middle λ a₂? →
    helper a₁? a₂?
    where
    continue : {n n′ : Bool} (p : ∞⟨ n′ ⟩P ℕ n) → n′ ≡ true →
               OnlyPairs (♭? p) → ManyPairs (♭? p) → ⊥
    continue p eq with forced? p
    continue p refl | true = ¬pairs p
    continue p ()   | false

    helper : Dec (AcceptsNonEmptyString (♭? p₁)) →
             Dec (AcceptsNonEmptyString (♭? p₂)) → ⊥
    helper (yes a₁) (yes a₂) = at-most-one op mp a₁ a₂

    helper (no ¬a₁) _ with nullable-or-fail ¬a₁
    ... | inj₁ []∈p₁ =
      continue p₂ (⇒ []∈p₁) (op ∘ _·_ []∈p₁) (Inf.map right mp)
      where
      right : ∀ {s} → s ∈ p₁ · p₂ → s ∈ ♭? p₂
      right (_·_ {s₁ = []}    _ ∈p₂) = ∈p₂
      right (_·_ {s₁ = _ ∷ _} ∈p₁ _) = ⊥-elim (¬a₁ (, , ∈p₁))
    ... | inj₂ is-fail = witness mp (∉ ∘ proj₂)
      where
      ∉ : ∀ {s} → ¬ s ∈ p₁ · p₂
      ∉ (∈p₁ · _) = is-fail _ ∈p₁

    helper _ (no ¬a₂) with nullable-or-fail ¬a₂
    ... | inj₁ []∈p₂ =
      continue p₁ (⇒ []∈p₂)
               (op ∘ (λ ∈p₁ → cast∈ (proj₂ ListMonoid.identity _) refl
                              (∈p₁ · []∈p₂)))
               (Inf.map left mp)
      where
      left : ∀ {s} → s ∈ p₁ · p₂ → s ∈ ♭? p₁
      left (_·_ {s₂ = _ ∷ _}        _ ∈p₂) = ⊥-elim (¬a₂ (, , ∈p₂))
      left (_·_ {s₁ = s₁} {s₂ = []} ∈p₁ _) =
        cast∈ (sym $ proj₂ ListMonoid.identity s₁) refl ∈p₁
    ... | inj₂ is-fail = witness mp (∉ ∘ proj₂)
      where
      ∉ : ∀ {s} → ¬ s ∈ p₁ · p₂
      ∉ (_ · ∈p₂) = is-fail _ ∈p₂

  -- Note that it is easy to decide whether a string is a pair or not.

  pair? : List ℕ → Bool
  pair? (m ∷ n ∷ []) = ⌊ Nat._≟_ m n ⌋
  pair? _            = false

  -- This means that there are decidable predicates over token strings
  -- which cannot be realised using the recogniser combinators.

  not-realisable :
    ¬ ∃₂ (λ n (p : P ℕ n) → ∀ {s} → s ∈ p ⇔ T (pair? s))
  not-realisable (_ , p , hyp) = ¬pairs p op mp
    where
    op : OnlyPairs p
    op {n} {[]}         s∈p = ⊥-elim (Equivalence.to hyp ⟨$⟩ s∈p)
    op {n} { m ∷ []}    s∈p with toWitness (Equivalence.to hyp ⟨$⟩ s∈p)
    op {n} {.n ∷ []}    s∈p | refl = refl
    op {n} {_  ∷ _ ∷ _} s∈p = ⊥-elim (Equivalence.to hyp ⟨$⟩ s∈p)

    mp : ManyPairs p
    mp (i , ¬pair) =
      ¬pair i NatOrder.refl $ Equivalence.from hyp ⟨$⟩ fromWitness refl

not-expressible :
  ∃₂ λ (Tok : Set) (f : List Tok → Bool) →
    ¬ ∃₂ (λ n (p : P Tok n) → ∀ {s} → s ∈ p ⇔ T (f s))
not-expressible = (ℕ , pair? , not-realisable)
  where open NotExpressible
