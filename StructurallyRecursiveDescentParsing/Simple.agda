------------------------------------------------------------------------
-- A simple backend
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Simple where

open import Data.Bool
open import Data.Product
open import Data.Maybe
open import Data.BoundedVec.Inefficient
import Data.List as L
open import Data.Nat
open import Data.Function using (id; _∘_)
open import Category.Applicative.Indexed
open import Category.Monad.Indexed
open import Category.Monad.State

open import StructurallyRecursiveDescentParsing.Index
open import StructurallyRecursiveDescentParsing.Type
open import StructurallyRecursiveDescentParsing.Utilities
  renaming (_∘_ to _∘′_)

------------------------------------------------------------------------
-- Parser monad

private

  P : Set → IFun ℕ
  P Tok = IStateT (BoundedVec Tok) L.List

  open module M₁ {Tok} =
    RawIMonadPlus (StateTIMonadPlus (BoundedVec Tok) L.ListMonadPlus)
    using ()
    renaming ( return to return′
             ; _>>=_  to _>>=′_
             ; _>>_   to _>>′_
             ; ∅      to fail′
             ; _∣_    to _∣′_
             )

  open module M₂ {Tok} =
    RawIMonadState (StateTIMonadState (BoundedVec Tok) L.ListMonad)
    using ()
    renaming ( get    to get′
             ; put    to put′
             ; modify to modify′
             )

------------------------------------------------------------------------
-- Run function for the parsers

-- For every successful parse the run function returns the remaining
-- string. (Since there can be several successful parses a list of
-- strings is returned.)

-- This function is structurally recursive with respect to the
-- following lexicographic measure:
--
-- 1) The upper bound of the length of the input string.
-- 2) The parser's proper left corner tree.

private

 module Dummy {NT Tok} (g : Grammar NT Tok) where

  mutual
    parse↓ : ∀ {e c R} n → Parser NT Tok (e ◇ c) R →
             P Tok n (if e then n else pred n) R
    parse↓ n       (return x)                  = return′ x
    parse↓ n       fail                        = fail′
    parse↓ n       (_∣_ {true}          p₁ p₂) = parse↓ n       p₁   ∣′ parse↑ n    p₂
    parse↓ n       (_∣_ {false} {true}  p₁ p₂) = parse↑ n       p₁   ∣′ parse↓ n    p₂
    parse↓ n       (_∣_ {false} {false} p₁ p₂) = parse↓ n       p₁   ∣′ parse↓ n    p₂
    parse↓ n       (p₁ ?>>= p₂)                = parse↓ n       p₁ >>=′ parse↓ n ∘′ p₂
    parse↓ zero    (p₁ !>>= p₂)                = fail′
    parse↓ (suc n) (p₁ !>>= p₂)                = parse↓ (suc n) p₁ >>=′ parse↑ n ∘′ p₂
    parse↓ n       (! x)                       = parse↓ n (g x)
    parse↓ n       token                       = get′ >>=′ eat
      where
      eat : ∀ {n} → BoundedVec Tok n → P Tok n (pred n) Tok
      eat []      = fail′
      eat (c ∷ s) = put′ s >>′ return′ c

    parse↑ : ∀ {e c R} n → Parser NT Tok (e ◇ c) R → P Tok n n R
    parse↑ {true}  n       p = parse↓ n p
    parse↑ {false} zero    p = fail′
    parse↑ {false} (suc n) p = parse↓ (suc n) p >>=′ λ r →
                               modify′ ↑        >>′
                               return′ r

open Dummy public

-- Exported run function.

parse : ∀ {NT Tok i R} →
        Grammar NT Tok → Parser NT Tok i R →
        L.List Tok → L.List (R × L.List Tok)
parse g p s = L.map (map-× id toList) (parse↓ g _ p (fromList s))

-- A variant which only returns parses which leave no remaining input.

parseComplete : ∀ {NT Tok i R} →
                Grammar NT Tok → Parser NT Tok i R →
                L.List Tok → L.List R
parseComplete g p s =
  L.map proj₁ (L.filter (L.null ∘ proj₂) (parse g p s))
