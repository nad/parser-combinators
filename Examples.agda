------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------

module Examples where

open import Data.List
open import Logic
import Data.Char as C
import Data.String as S
open C using (Char)
open import Parser
private
  open module T = Token C.decSetoid

module Ex₁ where

  -- e ∷= 0 + e | 0

  Γ : Ctxt
  Γ = _

  zeros : Label Γ _
  zeros = lz

  env : Env Char Γ
  env = ∅ ▷ token '0' · token '+' · ! zeros ∣ token '0'

  ex₁ : ⟦ ! zeros ⟧ env (S.toList "0+0") ≡ [] ∷ S.toList "+0" ∷ []
  ex₁ = ≡-refl

module Ex₂ where

  -- e ∷= f + e | f
  -- f ∷= 0 | 0 * f | ( e )

  Γ : Ctxt
  Γ = _

  expr : Label Γ _
  expr = ls lz

  factor : Label Γ _
  factor = lz

  expr'   = ! factor · token '+' · ! expr
          ∣ ! factor
  factor' = token '0'
          ∣ token '0' · token '*' · ! factor
          ∣ token '(' · ! expr · token ')'

  env : Env Char Γ
  env = ∅ ▷ expr' ▷ factor'

  ex₁ : ⟦ ! expr ⟧ env (S.toList "(0*)") ≡ []
  ex₁ = ≡-refl

  ex₂ : ⟦ ! expr ⟧ env (S.toList "0*(0+0)") ≡
        S.toList "*(0+0)" ∷ [] ∷ []
  ex₂ = ≡-refl

{-

module Ex₃ where

  -- This is not allowed:

  -- e ∷= f + e | f
  -- f ∷= 0 | f * 0 | ( e )

  Γ : Ctxt
  Γ = _

  expr : Label Γ _
  expr = ls lz

  factor : Label Γ _
  factor = lz

  expr'   = ! factor · token '+' · ! expr
          ∣ ! factor
  factor' = token '0'
          ∣ ! factor · token '*' · token '0'
          ∣ token '(' · ! expr · token ')'

  env : Env Char Γ
  env = ∅ ▷ expr' ▷ factor'

-}
