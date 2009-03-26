------------------------------------------------------------------------
-- A memoising backend
------------------------------------------------------------------------

-- This code has bitrotted.

-- Following Frost/Szydlowski and Frost/Hafiz/Callaghan (but without
-- the left recursion fix). An improvement has been made: The user
-- does not have to insert memoisation annotations manually. Instead
-- all grammar nonterminals are memoised. This is perhaps a bit less
-- flexible, but less error-prone, since there is no need to guarantee
-- that all "keys" (arguments to the memoise combinator) are unique
-- (assuming that the nonterminal equality is strong enough).

open import Relation.Binary
import Relation.Binary.PropositionalEquality  as PropEq
import Relation.Binary.PropositionalEquality1 as PropEq1
open PropEq  using (_≡_)
open PropEq1 using (_≡₁_)
open import StructurallyRecursiveDescentParsing.Index
open import Data.Product as Prod

module StructurallyRecursiveDescentParsing.Memoised

  -- In order to be able to store results in a memo table (and avoid
  -- having to lift the table code to Set1) the result types have to
  -- come from the following universe:

  {Result : Set} (⟦_⟧ : Result → Set)

  -- Nonterminals also have to be small enough:

  {NT : Index → Result → Set} {LargeNT : NonTerminalType}
  (resultType : ∀ {i r} → LargeNT i r → Result)
  (resultTypeCorrect : ∀ {i r} (x : LargeNT i r) →
                       ⟦ resultType x ⟧ ≡₁ r)
  (notTooLarge : ∀ {i r} (x : LargeNT i r) → NT i (resultType x))

  -- Furthermore nonterminals need to be ordered, so that they can be
  -- used as memo table keys:

  {_≈_ _<_ : Rel (∃₂ NT)}
  (ntOrdered : IsStrictTotalOrder _≈_ _<_)

  -- And the underlying equality needs to be strong enough:

  (indicesEqual : _≈_ =[ (λ irx → (proj₁ irx , proj₁ (proj₂ irx))) ]⇒
                  _≡_ {Index × Result})

  -- Token type:

  {Tok : Set}

  where

open import Data.Bool renaming (true to ⊤; false to ⊥)
import Data.Nat as Nat
open Nat using (ℕ; zero; suc; pred; z≤n; s≤s)
import Data.Nat.Properties as NatProp
open import Data.Function using (_∘_; _on₁_)
import Data.Vec  as Vec;  open Vec  using (Vec;  []; _∷_)
import Data.List as List; open List using (List; []; _∷_)
open import Data.Sum
open import Data.Maybe
open import Relation.Binary.OrderMorphism hiding (_∘_)
open _⇒-Poset_
import Relation.Binary.On as On
import Relation.Binary.Props.StrictTotalOrder as STOProps
open STOProps NatProp.strictTotalOrder

import StructurallyRecursiveDescentParsing.Memoised.Monad as Monad
open import StructurallyRecursiveDescentParsing.Type
open import StructurallyRecursiveDescentParsing.Utilities
  renaming (_∘_ to _∘′_)

------------------------------------------------------------------------
-- Some monotone functions

MonoFun : Set
MonoFun = poset ⇒-Poset poset

suc-mono : _≤_ =[ suc ]⇒ _≤_
suc-mono (inj₁ i<j)    = inj₁ (s≤s i<j)
suc-mono (inj₂ ≡-refl) = inj₂ ≡-refl

pred-mono : _≤_ =[ pred ]⇒ _≤_
pred-mono (inj₁ (s≤s (z≤n {zero})))  = inj₂ PropEq.refl
pred-mono (inj₁ (s≤s (z≤n {suc j}))) = inj₁ (s≤s z≤n)
pred-mono (inj₁ (s≤s (s≤s i<j)))     = inj₁ (s≤s i<j)
pred-mono (inj₂ PropEq.refl)         = inj₂ PropEq.refl

sucM : MonoFun
sucM = record
  { fun      = suc
  ; monotone = suc-mono
  }

predM : MonoFun
predM = record
  { fun      = pred
  ; monotone = pred-mono
  }

maybePredM : Empty → MonoFun
maybePredM e = if e then id else predM

lemma : ∀ e pos → fun (maybePredM e) pos ≤ pos
lemma ⊤ pos       = refl
lemma ⊥ zero      = refl
lemma ⊥ (suc pos) = inj₁ (Poset.refl Nat.poset)

------------------------------------------------------------------------
-- Parser monad

data Key : MonoFun → Result → Set where
  key : ∀ {e c r} (nt : NT (e ◇ c) r) → Key (maybePredM e) r

shuffle : ∃₂ Key → ∃₂ NT
shuffle (._ , _ , key x) = (, , x)

_≈K_ : Rel (∃₂ Key)
_≈K_ = _≈_ on₁ shuffle

_<K_ : Rel (∃₂ Key)
_<K_ = _<_ on₁ shuffle

ordered : IsStrictTotalOrder _≈K_ _<K_
ordered = On.isStrictTotalOrder shuffle ntOrdered

funsEqual : _≈K_ =[ proj₁ ]⇒ _≡_
funsEqual {(._ , _ , key _)} {(._ , _ , key _)} eq =
  PropEq.cong (maybePredM ∘ empty ∘ proj₁) (indicesEqual eq)

resultsEqual : _≈K_ =[ (λ rfk → proj₁ (proj₂ rfk)) ]⇒ _≡_
resultsEqual {(._ , _ , key _)} {(._ , _ , key _)} eq =
  PropEq.cong proj₂ (indicesEqual eq)

open Monad
       (StrictTotalOrder.isStrictTotalOrder NatProp.strictTotalOrder)
       (Vec Tok)
       ⟦_⟧
       ordered
       (λ {k₁} {k₂} → funsEqual    {k₁} {k₂})
       (λ {k₁} {k₂} → resultsEqual {k₁} {k₂})
open PM
  renaming ( return to return′
           ; _>>=_  to _>>=′_
           ; _=<<_  to _=<<′_
           ; ∅      to fail′
           ; _∣_    to _∣′_
           )

cast : ∀ {bnd f A₁ A₂} → A₁ ≡₁ A₂ → P bnd f A₁ → P bnd f A₂
cast refl p = p

------------------------------------------------------------------------
-- Run function for the parsers

-- Some helper functions.

private

  -- Extracts the first element from the input, if any.

  eat : ∀ {bnd} (inp : Input≤ bnd) →
        Maybe Tok × Input≤ (pred (position inp))
  eat {bnd} xs = helper (bounded xs) (string xs)
    where
    helper : ∀ {pos} → pos ≤ bnd → Vec Tok pos →
             Maybe Tok × Input≤ (pred pos)
    helper _  []       = (nothing , [] isBounded∶ refl)
    helper le (c ∷ cs) = (just c  , cs isBounded∶ refl)

  -- Fails if it encounters nothing.

  fromJust : ∀ {bnd} → Maybe Tok → P bnd idM Tok
  fromJust nothing  = fail′
  fromJust (just c) = return′ c

-- For every successful parse the run function returns the remaining
-- string. (Since there can be several successful parses a list of
-- strings is returned.)

-- This function is structurally recursive with respect to the
-- following lexicographic measure:
--
-- 1) The upper bound of the length of the input string.
-- 2) The parser's proper left corner tree.

private

 module Dummy (g : Grammar LargeNT Tok) where

  mutual
    parse : ∀ n {e c R} →
            Parser LargeNT Tok (e ◇ c) R →
            P n (if e then idM else predM) R
    parse n       (return x)          = return′ x
    parse n       (_∣_ {⊤}     p₁ p₂) = parse  n      p₁   ∣′ parse↑ n    p₂
    parse n       (_∣_ {⊥} {⊤} p₁ p₂) = parse↑ n      p₁   ∣′ parse  n    p₂
    parse n       (_∣_ {⊥} {⊥} p₁ p₂) = parse  n      p₁   ∣′ parse  n    p₂
    parse n       (p₁ ?>>= p₂)        = parse  n      p₁ >>=′ parse  n ∘′ p₂
    parse (suc n) (p₁ !>>= p₂)        = parse (suc n) p₁ >>=′ parse↑ n ∘′ p₂
    parse zero    (p₁ !>>= p₂)        = fail′
    parse n       fail                = fail′
    parse n       token               = fromJust =<<′ gmodify predM eat
    parse n       (! x)               = memoParse n x

    parse↑ : ∀ n {e c R} → Parser LargeNT Tok (e ◇ c) R → P n idM R
    parse↑ n {e} p = adjustBound (lemma e) (parse n p)

    memoParse : ∀ n {R e c} → LargeNT (e ◇ c) R →
                P n (if e then idM else predM) R
    memoParse n x = cast₁ (memoise k (cast₂ (parse n (g x))))
      where
      k     = key (notTooLarge x)
      cast₁ = cast (resultTypeCorrect x)
      cast₂ = cast (sym (resultTypeCorrect x))

-- Exported run function.

parse : ∀ {i R} →
        Grammar LargeNT Tok → Parser LargeNT Tok i R →
        List Tok → List (R × List Tok)
parse g p toks =
  List.map (Prod.map id (λ xs → Vec.toList (string xs))) $
  run (Vec.fromList toks) (Dummy.parse g _ p)

-- A variant which only returns parses which leave no remaining input.

parse-complete : ∀ {i R} →
                 Grammar Tok LargeNT → Parser Tok LargeNT i R →
                 List Tok → List R
parse-complete g p s =
  List.map proj₁ (List.filter (List.null ∘ proj₂) (parse g p s))
