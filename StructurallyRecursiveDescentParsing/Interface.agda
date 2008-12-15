------------------------------------------------------------------------
-- Terminating parser "combinator" interface
------------------------------------------------------------------------

-- Use StructurallyRecursiveDescentParsing.Simple to actually run the
-- parsers.

module StructurallyRecursiveDescentParsing.Interface where

open import StructurallyRecursiveDescentParsing.Index
import StructurallyRecursiveDescentParsing.Type as P
open P public using (Parser; Grammar)

open import Data.Bool
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Exported combinators

infix  60 !_
infixl 40 _∣_
infixl 10 _>>=_ _!>>=_

!_ : forall {tok nt e c r} ->
     nt (e ◇ c) r -> Parser tok nt (e ◇ step c) r
!_ = P.!_

symbol : forall {tok nt} -> Parser tok nt 0I tok
symbol = P.symbol

return : forall {tok nt r} -> r -> Parser tok nt 1I r
return = P.return

fail : forall {tok nt r} -> Parser tok nt 0I r
fail = P.fail

_>>=_ : forall {tok nt e₁ c₁ i₂ r₁ r₂} -> let i₁ = (e₁ ◇ c₁) in
        Parser tok nt i₁ r₁ ->
        (r₁ -> Parser tok nt i₂ r₂) ->
        Parser tok nt (i₁ ·I i₂) r₂
_>>=_ {e₁ = true } = P._?>>=_
_>>=_ {e₁ = false} = P._!>>=_

-- If the first parser is guaranteed to consume something, then the
-- second parser's index can depend on the result of the first parser.

_!>>=_ : forall {tok nt c₁ r₁ r₂} {i₂ : r₁ -> Index} ->
         let i₁ = (false ◇ c₁) in
         Parser tok nt i₁ r₁ ->
         ((x : r₁) -> Parser tok nt (i₂ x) r₂) ->
         Parser tok nt (i₁ ·I 1I) r₂
_!>>=_ = P._!>>=_

_∣_ : forall {tok nt e₁ c₁ i₂ r} -> let i₁ = (e₁ ◇ c₁) in
      Parser tok nt i₁ r ->
      Parser tok nt i₂ r ->
      Parser tok nt (i₁ ∣I i₂) r
_∣_ = P.alt _ _

cast : forall {tok nt e₁ e₂ c₁ c₂ r} ->
       e₁ ≡ e₂ -> c₁ ≡ c₂ ->
       Parser tok nt (e₁ ◇ c₁) r -> Parser tok nt (e₂ ◇ c₂) r
cast ≡-refl ≡-refl p = p
