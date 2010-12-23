------------------------------------------------------------------------
-- An alternative backend
------------------------------------------------------------------------

-- Acknowledgements:
--
-- • The use of parsing "processes" is based on implementation C from
--   Koen Claessen's paper Parallel parsing processes.
--
-- • The idea to use toProc is due to Jean-Philippe Bernardy.

-- It is not obvious how to adapt this backend so that it can handle
-- parsers which are simultaneously left and right recursive, like
-- TotalRecognisers.LeftRecursion.leftRight.

open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module TotalRecognisers.Simple.AlternativeBackend
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         -- The tokens must come with decidable equality.
         where

open import Coinduction
open import Data.Bool
open import Data.List
open import Relation.Nullary.Decidable

import TotalRecognisers.Simple as S
open S Tok _≟_ hiding (_∈?_)

------------------------------------------------------------------------
-- Parsing "processes"

data Proc : Set where
  tokenBind : (p : Tok → ∞ Proc) → Proc
  emptyOr   : (p : Proc) → Proc
  fail      : Proc

-- The semantics of Proc is given by run: run p s is true iff s is a
-- member of the language defined by p.

run : Proc → List Tok → Bool
run (tokenBind p) (c ∷ s) = run (♭ (p c)) s
run (emptyOr p)   s       = null s ∨ run p s
run _             _       = false

------------------------------------------------------------------------
-- Parsers can be turned into processes

-- Here I use my technique for "beating the productivity checker".

-- Process "programs".

data ProcP : Set where
  -- Process primitives.
  tokenBind : (p : Tok → ∞ ProcP) → ProcP
  emptyOr   : (p : ProcP) → ProcP
  fail      : ProcP

  -- Symmetric choice.
  _∣_     : (p₁ p₂ : ProcP) → ProcP

  -- Embedding of parsers.
  toProc  : ∀ {n} (p : P n) (κ : ProcP) → ProcP

-- WHNFs.

data ProcW : Set where
  tokenBind : (p : Tok → ∞ ProcP) → ProcW
  emptyOr   : (p : ProcW) → ProcW
  fail      : ProcW

-- WHNFs can be turned into programs.

program : ProcW → ProcP
program (tokenBind p) = tokenBind p
program (emptyOr p)   = emptyOr (program p)
program fail          = fail

-- Symmetric choice for WHNFs.

_∣W_ : ProcW → ProcW → ProcW
tokenBind p₁ ∣W tokenBind p₂ = tokenBind (λ c → ♯ (♭ (p₁ c) ∣ ♭ (p₂ c)))
emptyOr p₁   ∣W emptyOr p₂   = emptyOr (p₁ ∣W p₂)
emptyOr p₁   ∣W p₂           = emptyOr (p₁ ∣W p₂)
p₁           ∣W emptyOr p₂   = emptyOr (p₁ ∣W p₂)
fail         ∣W p₂           = p₂
p₁           ∣W fail         = p₁

-- Interpretation of toProc.

mutual

  toProcW′ : ∀ {n} → P n → if n then ProcW else ProcP → ProcW
  toProcW′ fail                                  κ = fail
  toProcW′ empty                                 κ = κ
  toProcW′ (tok t)                               κ = tokenBind (λ t′ →
                                                       if ⌊ t ≟ t′ ⌋ then ♯ κ else ♯ fail)
  toProcW′ (_∣_ {n₁ = true } {n₂ = true } p₁ p₂) κ = toProcW′ p₁ κ ∣W toProcW′ p₂ κ
  toProcW′ (_∣_ {n₁ = true } {n₂ = false} p₁ p₂) κ = toProcW′ p₁ κ ∣W toProcW  p₂ κ
  toProcW′ (_∣_ {n₁ = false} {n₂ = true } p₁ p₂) κ = toProcW  p₁ κ ∣W toProcW′ p₂ κ
  toProcW′ (_∣_ {n₁ = false} {n₂ = false} p₁ p₂) κ = toProcW′ p₁ κ ∣W toProcW′ p₂ κ
  toProcW′ (_·_ {n₁ = true }              p₁ p₂) κ = toProcW′ p₁ (toProcW′  p₂  κ)
  toProcW′ (_·_ {n₁ = false}              p₁ p₂) κ = toProcW′ p₁ (toProc (♭ p₂) κ)

  toProcW : ∀ {n} → P n → ProcW → ProcW
  toProcW {true } p κ = toProcW′ p          κ
  toProcW {false} p κ = toProcW′ p (program κ)

-- Programs can be turned into WHNFs.

whnf : ProcP → ProcW
whnf (tokenBind p) = tokenBind p
whnf (emptyOr p)   = emptyOr (whnf p)
whnf fail          = fail
whnf (p₁ ∣ p₂)     = whnf p₁ ∣W whnf p₂
whnf (toProc p κ)  = toProcW p (whnf κ)

-- Programs can be turned into processes.

mutual

  ⟦_⟧W : ProcW → Proc
  ⟦ tokenBind p ⟧W = tokenBind (λ c → ♯ ⟦ ♭ (p c) ⟧P)
  ⟦ emptyOr p   ⟧W = emptyOr ⟦ p ⟧W
  ⟦ fail        ⟧W = fail

  ⟦_⟧P : ProcP → Proc
  ⟦ p ⟧P = ⟦ whnf p ⟧W

------------------------------------------------------------------------
-- Alternative backend

-- I have not proved that this implementation is correct.

infix 4 _∈?_

_∈?_ : ∀ {n} → List Tok → P n → Bool
s ∈? p = run ⟦ toProc p (emptyOr fail) ⟧P s
